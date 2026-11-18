"""Check the decompiler by feeding its output back through real Lean.

For every `theorem` and `def` written in a Lean source file:

1. Run the instrumented Lean on the file and capture the kernel trace.
2. Decompile each declaration's tree into Lean text (implicit arguments hidden).
3. Append that text to the original file as a new declaration `<name>_rt`.
4. Run Lean again and capture the trace of the `_rt` declarations.
5. Compare the two expression trees node by node.

A PASS means Lean's own elaborator, given only the short decompiled text,
rebuilt exactly the tree the kernel originally received. Nothing the
decompiler hid was information: type inference put all of it back.

Usage:

    python3 instrumentation/roundtrip.py MyNatSuccAdd.lean
"""

from __future__ import annotations

import argparse
import os
import re
import subprocess
import sys
import tempfile
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import decompile as dc  # noqa: E402

ROOT = Path(__file__).resolve().parents[1]
DEFAULT_LEAN = ROOT / "lean4-src/build/release/stage1/bin/lean"
SUFFIX = "_rt"


def trace(lean: Path, source: Path) -> tuple[list[dc.Declaration], str]:
    env = dict(os.environ, LEAN_KERNEL_TRACE="*")
    result = subprocess.run([str(lean), str(source)], env=env, capture_output=True, text=True)
    return dc.parse_trace(result.stderr), result.stdout


def erase_names(expr: dc.Expr) -> dc.Expr:
    """Drop binder names and metadata, which carry no meaning for the kernel."""

    match expr:
        case dc.App(fn, arg):
            return dc.App(erase_names(fn), erase_names(arg))
        case dc.Lam(_, info, domain, body):
            return dc.Lam("_", info, erase_names(domain), erase_names(body))
        case dc.Pi(_, info, domain, body):
            return dc.Pi("_", info, erase_names(domain), erase_names(body))
        case dc.Let(_, ty, value, body):
            return dc.Let("_", erase_names(ty), erase_names(value), erase_names(body))
        case dc.MData(inner):
            return erase_names(inner)
        case dc.Proj(struct, index, inner):
            return dc.Proj(struct, index, erase_names(inner))
        case _:
            return expr


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("source", type=Path)
    parser.add_argument("--lean", type=Path, default=DEFAULT_LEAN)
    parser.add_argument("--binder-types", action="store_true", help="write the type of every `fun` binder")
    parser.add_argument("--keep", type=Path, help="write the generated Lean file here")
    args = parser.parse_args()

    source_text = args.source.read_text()
    declarations, _ = trace(args.lean, args.source)
    latest = {decl.name: decl for decl in declarations}
    printer = dc.build_printer(declarations, binder_types=args.binder_types)

    # Declarations the user wrote, found by their short name in the source.
    written = set(re.findall(r"^\s*(?:theorem|def)\s+([\w.']+)", source_text, re.MULTILINE))
    targets = [
        decl
        for decl in latest.values()
        if decl.kind in ("theorem", "definition") and decl.name.rpartition(".")[2] in written
    ]

    chunks = [source_text]
    for decl in targets:
        namespace = dc.namespace_of(decl.name)
        printer.namespace = namespace
        text = printer.declaration(decl, name=printer.const_name(decl.name) + SUFFIX)
        # We are testing the kernel term, not code generation: Lean compiles
        # recursive functions from their equations, not from this term.
        if text.startswith("def "):
            text = "noncomputable " + text
        chunks.append(f"namespace {namespace}\n{text}\nend {namespace}" if namespace else text)
    generated = "\n\n".join(chunks) + "\n"

    with tempfile.TemporaryDirectory() as tmp:
        path = Path(tmp) / "roundtrip.lean"
        path.write_text(generated)
        if args.keep:
            args.keep.write_text(generated)
        redone, stdout = trace(args.lean, path)
    redone_by_name = {decl.name: decl for decl in redone}
    # Lean reports errors by line; map them back to the declaration there.
    lines = generated.splitlines()
    errors = set()
    for line_number in re.findall(r"roundtrip\.lean:(\d+):\d+: error", stdout):
        for i in range(int(line_number) - 1, -1, -1):
            found = re.match(r"(?:theorem|noncomputable def|def) ([\w.']+)", lines[i])
            if found:
                errors.add(found.group(1))
                break
    errors = {name for decl in targets for name in [decl.name + SUFFIX] if name.rpartition(".")[2] in {e.rpartition(".")[2] for e in errors}}

    failures = 0
    width = max(len(decl.name) for decl in targets)
    print(f"{'declaration':<{width}}  {'tree nodes':>10}  {'text chars':>10}  result")
    for decl in targets:
        again = redone_by_name.get(decl.name + SUFFIX)
        nodes = dc.size(decl.type) + dc.size(decl.value)
        printer.namespace = dc.namespace_of(decl.name)
        chars = len(printer.declaration(decl))
        if again is None or f"{decl.name}{SUFFIX}" in errors:
            verdict = "FAIL (Lean rejected the decompiled text)"
        elif erase_names(again.type) != erase_names(decl.type):
            verdict = "FAIL (type tree differs)"
        elif erase_names(again.value) != erase_names(decl.value):
            verdict = "FAIL (value tree differs)"
        else:
            verdict = "PASS"
        failures += verdict != "PASS"
        print(f"{decl.name:<{width}}  {nodes:>10}  {chars:>10}  {verdict}")
    if failures:
        print("\nLean output:\n" + stdout)
    sys.exit(1 if failures else 0)


if __name__ == "__main__":
    main()
