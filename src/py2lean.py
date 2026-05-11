import argparse
import sys
import os
sys.path.append(os.path.dirname(__file__))
from node_visitor import *

class ASTToJsonLeanVisitor(ASTToJsonLeanVisitorBase):
    """Concrete visitor that implements the translation logic for a specific subset of Python syntax."""
    pass  # For now, we only have BinOp, Constant, and Expr. We can add more visit methods as needed.
        
translator = ASTToJsonLeanVisitor()

def translate_to_json(source_code):
    """Parses Python source code and translates it to a JSON IR."""
    print(f"Translating source code:\n{source_code}", file=sys.stderr)  # Debugging output
    ast_tree = ast.parse(source_code)
    print(f"Parsed AST:\n{ast.dump(ast_tree, indent=4)}", file=sys.stderr)  # Debugging output
    data= translator.visit(ast_tree.body[0])  # Assuming we want to translate the first statement only
    print(f"Generated JSON: {json.dumps(data)}", file=sys.stderr)  # Debugging output   
    return json.dumps(data)

parent_dir = Path(__file__).parent.parent

def translate_to_lean(source_code, target="term"):
    """Translates Python source code to Lean code by first converting it to JSON and then invoking the Lean code generator."""
    json_ir = translate_to_json(source_code)
    json_task = json.dumps({"task": "translate", "ast": json.loads(json_ir)})
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
    """Command-line entry point for translating a Python file to Lean."""
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
    result = translate_to_lean(source_code, args.target)

    if isinstance(result, dict):
        if result.get("result") is False:
            print(result.get("error", "Translation failed."), file=sys.stderr)
            return 1

        code_key = f"lean_{args.target}"
        if code_key in result:
            print(f"Successfully translated to Lean", file=sys.stderr)  # Debugging output
            print(result[code_key])
            return 0
    print("Unexpected translation result format.", file=sys.stderr)
    print(result)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
