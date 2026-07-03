"""Run Lean-like phase scripts against the corresponding Python kernel.

Usage:

    python3 -B tutorial_type_checker.py all
    python3 -B tutorial_type_checker.py 01
    python3 -B tutorial_type_checker.py 03_rewrites
    python3 -B tutorial_type_checker.py 05_comm

The scripts are intentionally tiny Lean-like files containing `constant`,
`inductive`, `def`, and `theorem` declarations.  This runner does not parse full
Lean terms yet.  It extracts declaration names from the script, imports the
selected phase's `solution.py`, and asks that phase's kernel to check the AST
registered for each declaration.
"""

from __future__ import annotations

import argparse
import importlib.util
import sys
from pathlib import Path
from types import ModuleType


ROOT = Path(__file__).resolve().parent
PHASE_DIRS = {
    "01": ROOT / "phases/01_true_false",
    "02": ROOT / "phases/02_recursive_nat",
    "03": ROOT / "phases/03_rewrites",
    "04": ROOT / "phases/04_induction",
    "05": ROOT / "phases/05_comm",
}


class RunnerError(Exception):
    pass


def load_solution(phase_dir: Path) -> ModuleType:
    path = phase_dir / "solution.py"
    module_name = f"{phase_dir.name}_solution"
    spec = importlib.util.spec_from_file_location(module_name, path)
    if spec is None or spec.loader is None:
        raise RunnerError(f"cannot load {path}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[module_name] = module
    spec.loader.exec_module(module)
    return module


def load_declarations(phase_dir: Path, solution: ModuleType) -> ModuleType:
    path = phase_dir / "declarations.py"
    module_name = f"{phase_dir.name}_declarations"
    spec = importlib.util.spec_from_file_location(module_name, path)
    if spec is None or spec.loader is None:
        raise RunnerError(f"cannot load {path}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[module_name] = module
    sys.modules["solution"] = solution
    spec.loader.exec_module(module)
    return module


def strip_block_comments(text: str) -> str:
    while "/-" in text:
        start = text.index("/-")
        end = text.index("-/", start) + 2
        text = text[:start] + text[end:]
    return text


def declaration_names(phase_dir: Path) -> list[str]:
    path = phase_dir / "script.lean"
    names: list[str] = []
    for lineno, line in enumerate(strip_block_comments(path.read_text()).splitlines(), start=1):
        stripped = line.strip()
        if not stripped or stripped.startswith("--"):
            continue
        if stripped.startswith("constant "):
            names.append(stripped.split()[1])
        elif stripped.startswith("inductive "):
            names.append(stripped.split()[1])
        elif stripped.startswith("| "):
            names.append(stripped.split()[1])
        elif stripped.startswith("def ") or stripped.startswith("theorem "):
            names.append(stripped.split()[1])
        elif stripped.startswith(("fun ", "Nat.ind", "rfl", "(")):
            continue
        elif stripped in {"where"}:
            continue
        elif stripped.startswith(("forall ", "succ ", "(succ ")):
            continue
        else:
            # Continuation lines in these tutorial scripts are proof/type text.
            # Unknown top-level commands should be explicit failures.
            if not line.startswith((" ", "\t")):
                raise RunnerError(f"{path}:{lineno}: cannot understand declaration line: {stripped}")
    return names


def run_phase(phase_dir: Path) -> None:
    solution = load_solution(phase_dir)
    declarations_module = load_declarations(phase_dir, solution)
    infer = solution.infer
    check = solution.check
    declaration = declarations_module.declaration
    pretty = solution.pretty
    checker = solution.fresh_checker() if hasattr(solution, "fresh_checker") else None
    register = getattr(solution, "register_declaration", None)

    print(phase_dir.relative_to(ROOT))
    for name in declaration_names(phase_dir):
        try:
            expr, expected = declaration(name)
        except KeyError as exc:
            raise RunnerError(f"{phase_dir / 'script.lean'}: no declaration case named {name!r}") from exc
        if checker is None:
            infer(expr)
            check(expr, expected)
        else:
            if register is not None and name in getattr(solution, "REGISTER_BEFORE_CHECK", set()):
                register(checker, name)
            infer(expr, tc=checker)
            check(expr, expected, tc=checker)
            if register is not None and name not in getattr(solution, "REGISTER_BEFORE_CHECK", set()):
                register(checker, name)
        print(f"  {name} : {pretty(expected)}")


def select_phases(request: str) -> list[Path]:
    if request == "all":
        return list(PHASE_DIRS.values())
    for key, path in PHASE_DIRS.items():
        if request == key or request == path.name:
            return [path]
    known = ", ".join(["all", *PHASE_DIRS.keys(), *(p.name for p in PHASE_DIRS.values())])
    raise RunnerError(f"unknown phase {request!r}; expected one of: {known}")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("phase", nargs="?", default="all")
    args = parser.parse_args()

    for phase_dir in select_phases(args.phase):
        run_phase(phase_dir)
        print()


if __name__ == "__main__":
    main()
