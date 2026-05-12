import argparse
import sys
import os
import json
import ast
from pathlib import Path
import subprocess
sys.path.append(os.path.dirname(__file__))
from node_visitor import *

HOMEDIR = Path.cwd().parent
SRC_DIR = HOMEDIR / "src"
PY_EXEC = HOMEDIR / ".venv" / "bin" / "python"

class ASTToJsonLeanVisitor(ASTToJsonLeanVisitorBase):
    """Concrete visitor that implements the translation logic for a specific subset of Python syntax."""
    pass  # For now, we only have BinOp, Constant, and Expr. We can add more visit methods as needed.
        
translator = ASTToJsonLeanVisitor()

def translate_to_json(source_code, filepath=None):
    """
    Parses Python source code and translates it to a JSON IR.
    If `filepath` is provided, it first runs the annotator code to add type annotations,
    else the source_code argument will be used as-is for translation.
    """
    if filepath is not None:
        print(f"Adding Annotations to source code:\n{source_code}", file=sys.stderr)  # Debugging output
        annotated_code = subprocess.run(
            [str(PY_EXEC), str(SRC_DIR / "annotate_python.py"), "--no-write", "--file", str(filepath)],
            text=True,
            capture_output=True,
        )
        if annotated_code.returncode != 0:
            print(f"Error during annotation: {annotated_code.stderr}", file=sys.stderr)
            print("Falling back to unannotated source code for translation.", file=sys.stderr)
        source_code = annotated_code.stdout if annotated_code.returncode == 0 else source_code 

    print(f"Translating source code:\n{source_code}", file=sys.stderr)  # Debugging output
    ast_tree = ast.parse(source_code)
    print(f"Parsed AST:\n{ast.dump(ast_tree, indent=4)}", file=sys.stderr)  # Debugging output
    # Current limitation: the translator lowers only the first top-level statement.
    data= translator.visit(ast_tree.body[0])  # Assuming we want to translate the first statement only
    print(f"Generated JSON: {json.dumps(data)}", file=sys.stderr)  # Debugging output   
    return json.dumps(data)

parent_dir = Path(__file__).parent.parent

def translate_to_lean(source_code, target="term", filepath = None):
    """Translate Python source to Lean via JSON IR and the Lean backend executable.

    Note: this function currently consumes `source_code` as-is. If we want the
    `annotate_python.py` preprocessing stage to be mandatory, that hook still
    needs to be added before `translate_to_json`.
    """
    json_ir = translate_to_json(source_code, filepath)
    json_task = json.dumps({"task": "translate", "ast": json.loads(json_ir)})
    # Prefer the built executable when present; otherwise fall back to `lake exe`.
    py2lean_bin = parent_dir / ".lake" / "build" / "bin" / "py2lean"
    cmd = [str(py2lean_bin), json_task, target] if py2lean_bin.exists() else ["lake", "exe", "py2lean", json_task, target]
    proc = subprocess.Popen(
        cmd,
        cwd=parent_dir,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
    )
    stdout, stderr = proc.communicate()
    if proc.returncode != 0:
        return {"result": False, "error": stderr.strip() or "py2lean backend failed"}
    return json.loads(stdout)

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
    parser.add_argument("filename", help="Python source file to translate")
    parser.add_argument(
        "target",
        nargs="?",
        default="term",
        help="Lean target string to pass to the translator (default: term)",
    )
    args = parser.parse_args(argv)

    source_code = Path(args.filename).read_text(encoding="utf-8")
    result = translate_to_lean(source_code, args.target, args.filename)

    if isinstance(result, dict):
        if result.get("result") is False:
            print(result.get("error", "Translation failed."), file=sys.stderr)
            return 1

        code_key = f"lean_{args.target}"
        if code_key in result:
            print("Successfully translated to Lean", file=sys.stderr)  # Debugging output
            print(result[code_key])
            return 0
    print("Unexpected translation result format.", file=sys.stderr)
    print(result)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
