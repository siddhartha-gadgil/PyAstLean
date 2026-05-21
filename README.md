# PyAstLean

PyAstLean is a tool that converts Python code into Lean 4.

## Usage

Build the project from the repository root:

```bash
lake build
```

## Converting Python to Lean

Use the Python wrapper `src/py2lean.py` to convert a Python file to Lean.

```bash
python3 src/py2lean.py example_scripts/commands/assignment_arith.py --target command
```

That wrapper is responsible for:

1. Reads the Python file.
2. Runs the annotation pre-pass from `src/annotate_python.py`.
3. Converts the Python AST to the JSON IR in `src/node_visitor.py`.
4. Sends JSON translation requests to the Lean backend.
5. Reuses one persistent Lean backend process for the lifetime of the Python process, so
   module-level translation does not restart Lean for every top-level statement.


To see the intermediate steps in the code, run `--verbose` flag as shown below.
```bash
python3 src/py2lean.py example_scripts/commands/assignment_arith.py --target command --verbose
```

### Low-level Lean backend

The executable defined by [py2lean.lean](/home/anirudhgupta/PyAstLean/py2lean.lean:1) is the JSON backend.

It expects:

1. A JSON task string as the first argument.
2. An optional target as the second argument, usually `term` or `command`.

Example:

```bash
lake exe py2lean '{"task":"translate","ast":{"node_type":"Constant","value":1}}' term
```

Typical stdout:

```json
{"result": true, "lean_term": "(1 : Int)"}
```

The backend also supports a persistent server mode for tooling and performance-sensitive
workflows:

```bash
lake env .lake/build/bin/py2lean --server
```

It accepts one compact JSON request per line on stdin and writes one compact JSON response
per line on stdout. The Python wrapper uses this mode automatically.

## Installation

To install PyAstLean as a dependency, add the following to your `lakefile.toml`:

```toml
[[require]]
name = "PyAstLean"
git = "https://github.com/Siddhartha-Gadgil/PyAstLean.git"
rev = "v4.29.0"
```

### Dependencies

For Python-side annotation, the project uses `pyrefly` and `libcst`. Set up the Python environment with one of the following:

```bash
# If you use uv (recommended)
uv pip install -r requirements.txt
uv sync

# If you use pip
python -m venv .venv
source .venv/bin/activate
pip install -r requirements.txt
```

## Libraries

Python libraries can be supported in PyAstLean by writing Lean definitions that correspond to the Python library's API. These definitions can be made by implementing the necessary translation logic in the Lean backend, then added to PyAstLean by creating a mapping using `Mapping.lean` which is simply a map from python name for a function to Your Lean definition.

For example, see [math](./Libraries/math/) library, which uses Mathlib to implement some of the functions from Python's `math` module.

### How to add your own library

You have two options, either download a premade Lean library for that Python library(from GitHub) or write your own Lean definitions for the Python library and create Mappings for the functions you want to support.

See [Libraries](./Libraries/) for examples of how to add a library and use it.

## Testing


PyAstLeanCheck (PALC) (pronounced - "pal" + "ack" like PAL Acknowledge) is the testing framework for PyAstLean. It is used to check that the generated Lean code matches the expected output. This is based on the FileCheck utility from LLVM, but with some differences to make it more suitable for our use case.

To run all tests:
```bash
lake test
```

If you want to run a specific test case, you can do so with:
```bash
lake exe palc <case_file.py>
```
