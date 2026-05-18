import argparse
import sys
import os
import json
import ast
import atexit
import select
from pathlib import Path
import subprocess
import logging
import threading
from collections import deque
sys.path.append(os.path.dirname(__file__))
from node_visitor import *

HOMEDIR = Path.absolute(Path(__name__).parent.parent)
SRC_DIR = HOMEDIR / "src"
PY_EXEC = HOMEDIR / ".venv" / "bin" / "python"
logger = logging.getLogger(__name__)

class ASTToJsonLeanVisitor(ASTToJsonLeanVisitorBase):
    """Concrete visitor that implements the translation logic for a specific subset of Python syntax."""
    pass  # For now, we only have BinOp, Constant, and Expr. We can add more visit methods as needed.
        
translator = ASTToJsonLeanVisitor()


def configure_logging(verbose: bool) -> None:
    """Configure CLI logging, keeping normal runs quiet unless verbose is enabled."""
    level = logging.DEBUG if verbose else logging.WARNING
    logging.basicConfig(level=level, format="%(levelname)s: %(message)s")


def _node_type(node):
    return node.get("node_type") if isinstance(node, dict) else None


def _walk_json_nodes(node, *, skip_nested_function_bodies=False):
    if isinstance(node, dict):
        yield node
        node_type = node.get("node_type")
        for key, value in node.items():
            if skip_nested_function_bodies and node_type == "FunctionDef" and key == "body":
                continue
            yield from _walk_json_nodes(value, skip_nested_function_bodies=skip_nested_function_bodies)
    elif isinstance(node, list):
        for item in node:
            yield from _walk_json_nodes(item, skip_nested_function_bodies=skip_nested_function_bodies)


def _body_has_direct_exception_syntax(body):
    for stmt in body:
        for node in _walk_json_nodes(stmt, skip_nested_function_bodies=True):
            if _node_type(node) in {"Try", "Raise"}:
                return True
    return False


def _body_has_direct_io_syntax(body):
    for stmt in body:
        for node in _walk_json_nodes(stmt, skip_nested_function_bodies=True):
            if _node_type(node) != "Call":
                continue
            func = node.get("func")
            if (
                isinstance(func, dict)
                and func.get("node_type") == "Name"
                and func.get("id") in {"print", "input"}
            ):
                return True
    return False


def _body_calls_known_functions(body, known_names):
    called = set()
    for stmt in body:
        for node in _walk_json_nodes(stmt, skip_nested_function_bodies=True):
            if _node_type(node) != "Call":
                continue
            func = node.get("func")
            if isinstance(func, dict) and func.get("node_type") == "Name":
                func_name = func.get("id")
                if func_name in known_names:
                    called.add(func_name)
    return called


def _annotate_calls(node, effectful_names):
    if isinstance(node, dict):
        if node.get("node_type") == "Call":
            func = node.get("func")
            if isinstance(func, dict) and func.get("node_type") == "Name" and func.get("id") in effectful_names:
                node["effect_mode"] = "except"
        node_type = node.get("node_type")
        for key, value in node.items():
            if node_type == "FunctionDef" and key == "body":
                continue
            _annotate_calls(value, effectful_names)
    elif isinstance(node, list):
        for item in node:
            _annotate_calls(item, effectful_names)


def _annotate_calls_with_mode(node, effectful_names, effect_mode):
    if isinstance(node, dict):
        if node.get("node_type") == "Call":
            func = node.get("func")
            if isinstance(func, dict) and func.get("node_type") == "Name" and func.get("id") in effectful_names:
                node.setdefault("effect_mode", effect_mode)
        node_type = node.get("node_type")
        for key, value in node.items():
            if node_type == "FunctionDef" and key == "body":
                continue
            _annotate_calls_with_mode(value, effectful_names, effect_mode)
    elif isinstance(node, list):
        for item in node:
            _annotate_calls_with_mode(item, effectful_names, effect_mode)


def _annotate_direct_io_calls(node):
    if isinstance(node, dict):
        if node.get("node_type") == "Call":
            func = node.get("func")
            if (
                isinstance(func, dict)
                and func.get("node_type") == "Name"
                and func.get("id") in {"print", "input"}
            ):
                node.setdefault("effect_mode", "io")
        node_type = node.get("node_type")
        for key, value in node.items():
            if node_type == "FunctionDef" and key == "body":
                continue
            _annotate_direct_io_calls(value)
    elif isinstance(node, list):
        for item in node:
            _annotate_direct_io_calls(item)


def annotate_exception_effects(module_json):
    """Mark function defs and direct calls that require translated `Except` handling."""
    def annotate_scope(body):
        local_functions = {
            stmt["name"]: stmt
            for stmt in body
            if isinstance(stmt, dict) and stmt.get("node_type") == "FunctionDef"
        }
        for fn in local_functions.values():
            annotate_scope(fn.get("body", []))

        effectful = {
            name: _body_has_direct_exception_syntax(fn.get("body", []))
            for name, fn in local_functions.items()
        }
        changed = True
        while changed:
            changed = False
            for name, fn in local_functions.items():
                if effectful[name]:
                    continue
                called = _body_calls_known_functions(fn.get("body", []), local_functions.keys())
                if any(effectful.get(callee, False) for callee in called):
                    effectful[name] = True
                    changed = True

        effectful_names = {name for name, is_effectful in effectful.items() if is_effectful}
        for name, fn in local_functions.items():
            if effectful[name]:
                fn["effect_mode"] = "except"
            _annotate_calls(fn.get("body", []), effectful_names)

        _annotate_calls(body, effectful_names)

    if isinstance(module_json, dict) and module_json.get("node_type") == "Module":
        annotate_scope(module_json.get("body", []))


def annotate_io_effects(module_json):
    """Mark input/print-bearing function defs and direct calls that require translated `IO` handling."""
    def annotate_scope(body):
        local_functions = {
            stmt["name"]: stmt
            for stmt in body
            if isinstance(stmt, dict) and stmt.get("node_type") == "FunctionDef"
        }
        for fn in local_functions.values():
            annotate_scope(fn.get("body", []))

        io_effectful = {
            name: _body_has_direct_io_syntax(fn.get("body", []))
            for name, fn in local_functions.items()
            if fn.get("effect_mode") != "except"
        }
        changed = True
        while changed:
            changed = False
            for name, fn in local_functions.items():
                if fn.get("effect_mode") == "except":
                    continue
                if io_effectful.get(name, False):
                    continue
                called = _body_calls_known_functions(fn.get("body", []), local_functions.keys())
                if any(io_effectful.get(callee, False) for callee in called):
                    io_effectful[name] = True
                    changed = True

        io_effectful_names = {name for name, is_effectful in io_effectful.items() if is_effectful}
        for name, fn in local_functions.items():
            if fn.get("effect_mode") == "except":
                continue
            if io_effectful.get(name, False):
                fn["effect_mode"] = "io"
            _annotate_direct_io_calls(fn.get("body", []))
            _annotate_calls_with_mode(fn.get("body", []), io_effectful_names, "io")

        _annotate_direct_io_calls(body)
        _annotate_calls_with_mode(body, io_effectful_names, "io")

    if isinstance(module_json, dict) and module_json.get("node_type") == "Module":
        annotate_scope(module_json.get("body", []))

def translate_to_json(source_code, filepath=None):
    """
    Parses Python source code and translates it to a JSON IR.
    If `filepath` is provided, it first runs the annotator code to add type annotations,
    else the source_code argument will be used as-is for translation.
    """
    if filepath is not None:
        logger.debug("Annotating Python source from %s before AST translation.", filepath)
        logger.debug("Original source:\n%s", source_code)
        annotated_code = subprocess.run(
            [str(PY_EXEC), str(SRC_DIR / "annotate_python.py"), "--no-write", "--file", str(filepath)],
            text=True,
            capture_output=True,
        )
        if annotated_code.returncode != 0:
            logger.warning("Annotation failed: %s", annotated_code.stderr.strip())
            logger.warning("Falling back to unannotated source code for translation.")
        source_code = annotated_code.stdout if annotated_code.returncode == 0 else source_code

    logger.debug("Source passed to Python AST parser:\n%s", source_code)
    ast_tree = ast.parse(source_code)
    logger.debug("Parsed Python AST:\n%s", ast.dump(ast_tree, indent=4))
    data = translator.visit(ast_tree)
    annotate_exception_effects(data)
    annotate_io_effects(data)
    logger.debug("Generated JSON IR: %s", json.dumps(data))
    return json.dumps(data)

parent_dir = Path(__file__).parent.parent

class LeanBackendClient:
    """Persistent line-oriented client for the Lean backend server mode."""

    def __init__(self, cwd: Path):
        self.cwd = cwd
        self.proc = None
        self._stderr_lines = deque(maxlen=200)
        self._stderr_thread = None

    @property
    def binary_path(self):
        return self.cwd / ".lake" / "build" / "bin" / "py2lean"

    def _tracked_backend_sources(self):
        """Yield Lean source files whose freshness determines whether `py2lean` must be rebuilt."""
        explicit_files = [
            self.cwd / "py2lean.lean",
            self.cwd / "lakefile.lean",
            self.cwd / "lean-toolchain",
        ]
        for path in explicit_files:
            if path.exists():
                yield path

        pyastlean_dir = self.cwd / "PyAstLean"
        if pyastlean_dir.exists():
            yield from pyastlean_dir.rglob("*.lean")

    def _binary_needs_rebuild(self):
        """Return true when the backend binary is missing or older than tracked Lean sources."""
        binary = self.binary_path
        if not binary.exists():
            logger.debug("py2lean backend binary is missing; rebuild required.")
            return True

        binary_mtime = binary.stat().st_mtime
        latest_source_mtime = max(
            (path.stat().st_mtime for path in self._tracked_backend_sources()),
            default=0.0,
        )
        if latest_source_mtime > binary_mtime:
            logger.debug(
                "A tracked Lean source is newer than the py2lean backend binary; rebuild required."
            )
            return True
        return False

    def _ensure_binary(self):
        if not self._binary_needs_rebuild():
            logger.debug("Reusing existing py2lean backend binary; no rebuild needed.")
            return

        logger.debug("Building py2lean backend binary before starting server.")
        build = subprocess.run(
            ["lake", "build", "py2lean"],
            cwd=self.cwd,
            text=True,
            capture_output=True,
        )
        if build.returncode != 0:
            raise RuntimeError(build.stderr.strip() or build.stdout.strip() or "lake build py2lean failed")

    def _command(self):
        return ["lake", "env", str(self.binary_path), "--server"]

    def _drain_stderr(self):
        assert self.proc is not None and self.proc.stderr is not None
        for line in self.proc.stderr:
            line = line.rstrip()
            if not line:
                continue
            self._stderr_lines.append(line)
            logger.debug("Lean backend stderr: %s", line)

    def _recent_stderr(self):
        return "\n".join(self._stderr_lines)

    def _one_shot_request(self, ast_json, target, check=True):
        """Fallback backend path that avoids the persistent server when it misbehaves."""
        json_task = json.dumps(
            {"task": "translate", "ast": ast_json, "target": target, "check": check},
            separators=(",", ":"),
        )
        cmd = ["lake", "exe", "py2lean", json_task, target]
        logger.debug("Falling back to one-shot Lean backend: %s", cmd)
        proc = subprocess.run(
            cmd,
            cwd=self.cwd,
            text=True,
            capture_output=True,
        )
        if proc.returncode != 0:
            return {
                "result": False,
                "error": proc.stderr.strip() or proc.stdout.strip() or "Lean backend failed",
            }
        output = proc.stdout.strip()
        try:
            return json.loads(output)
        except json.JSONDecodeError as err:
            return {
                "result": False,
                "error": f"Invalid JSON response from one-shot Lean backend: {err}\n{output}",
            }

    def start(self):
        if self.proc is not None and self.proc.poll() is None:
            return
        self._ensure_binary()
        cmd = self._command()
        logger.debug("Starting persistent Lean backend: %s", cmd)
        self.proc = subprocess.Popen(
            cmd,
            cwd=self.cwd,
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            bufsize=1,
        )
        self._stderr_lines.clear()
        self._stderr_thread = threading.Thread(target=self._drain_stderr, daemon=True)
        self._stderr_thread.start()

    def close(self):
        if self.proc is None:
            return
        try:
            if self.proc.stdin is not None:
                self.proc.stdin.close()
        except BrokenPipeError:
            pass
        try:
            self.proc.wait(timeout=2)
        except subprocess.TimeoutExpired:
            self.proc.kill()
            self.proc.wait(timeout=2)
        finally:
            if self.proc.stdout is not None:
                self.proc.stdout.close()
            if self.proc.stderr is not None:
                self.proc.stderr.close()
        self.proc = None
        self._stderr_thread = None

    def request(self, ast_json, target, check=True):
        """Send one translation request to the persistent Lean backend."""
        self.start()
        assert self.proc is not None
        assert self.proc.stdin is not None
        assert self.proc.stdout is not None
        json_task = json.dumps(
            {"task": "translate", "ast": ast_json, "target": target, "check": check},
            separators=(",", ":"),
        )
        logger.debug("Sending request to Lean backend: target=%s check=%s", target, check)
        try:
            self.proc.stdin.write(json_task + "\n")
            self.proc.stdin.flush()
        except BrokenPipeError:
            self.close()
            return self._one_shot_request(ast_json, target, check)

        assert self.proc.stdout is not None
        ready, _, _ = select.select([self.proc.stdout], [], [], 5.0)
        if not ready:
            logger.debug("Persistent Lean backend timed out waiting for a response; retrying once-shot.")
            self.close()
            return self._one_shot_request(ast_json, target, check)

        response_line = self.proc.stdout.readline()
        if not response_line:
            self.close()
            return self._one_shot_request(ast_json, target, check)
        response_line = response_line.strip()
        logger.debug("Lean backend response: %s", response_line)
        try:
            return json.loads(response_line)
        except json.JSONDecodeError as err:
            logger.debug("Persistent Lean backend returned invalid JSON; retrying one-shot.")
            self.close()
            return self._one_shot_request(ast_json, target, check)

    def __enter__(self):
        self.start()
        return self

    def __exit__(self, exc_type, exc, tb):
        self.close()


_LEAN_BACKEND = LeanBackendClient(parent_dir)
atexit.register(_LEAN_BACKEND.close)


def invoke_lean_backend(ast_json, target, check=True, client=None):
    """Send one JSON AST node to the Lean backend and return the parsed JSON response."""
    backend = client or _LEAN_BACKEND
    try:
        return backend.request(ast_json, target, check)
    except Exception as err:
        return {"result": False, "error": str(err)}

def translate_to_lean(source_code, target="term", filepath = None):
    """Translate Python source to Lean via JSON IR and the Lean backend executable."""
    json_ir = translate_to_json(source_code, filepath)
    ast_json = json.loads(json_ir)
    client = _LEAN_BACKEND

    if ast_json.get("node_type") == "Module":
        body = ast_json.get("body", [])
        if target == "command":
            code_parts = []
            for stmt in body:
                # A top-level Python `pass` is a true no-op, so there is no Lean command to emit.
                if stmt.get("node_type") == "Pass":
                    continue
                result = invoke_lean_backend(stmt, target, check=False, client=client)
                if result.get("result") is False:
                    return result
                code_key = f"lean_{target}"
                if code_key not in result:
                    return {"result": False, "error": f"Missing '{code_key}' in backend response."}
                code_parts.append(result[code_key])
            return {"result": True, f"lean_{target}": "\n\n".join(code_parts)}

        if len(body) == 1:
            return invoke_lean_backend(body[0], target, client=client)
        return {
            "result": False,
            "error": f"Target '{target}' only supports a single top-level statement; use --target command for full modules.",
        }

    return invoke_lean_backend(ast_json, target, client=client)

def egProgram():
    return """def f(n):
    x = n + 1
    y = x * 2
    x = y - 1
    return x + y
"""


def main(argv=None):
    """CLI entry point that reads a file and forwards its contents to the translator."""
    parser = argparse.ArgumentParser(description="Translate a Python file to Lean.")
    parser.add_argument("file", nargs="?", help="Python source file to translate")
    parser.add_argument("--file", dest="file_option", help=argparse.SUPPRESS)
    parser.add_argument(
        "--target",
        nargs="?",
        default="term",
        help="Lean target string to pass to the translator (default: term)",
    )
    parser.add_argument("--verbose", "-v", action="store_true", help="Enable verbose output for debugging")
    args = parser.parse_args(argv)
    configure_logging(args.verbose)

    file_path = args.file_option or args.file
    if not file_path:
        parser.error("the following arguments are required: file")

    source_code = Path(file_path).read_text(encoding="utf-8")
    result = translate_to_lean(source_code, args.target, file_path)

    if isinstance(result, dict):
        if result.get("result") is False:
            print(result.get("error", "Translation failed."), file=sys.stderr)
            return 1

        code_key = f"lean_{args.target}"
        if code_key in result:
            logger.info("Successfully translated to Lean target '%s'.", args.target)
            print(result[code_key])
            return 0
    print("Unexpected translation result format.", file=sys.stderr)
    print(result)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
