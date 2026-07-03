"""Run Lean-like phase scripts against the corresponding Python kernel.

Usage:

    python3 -B tutorial_type_checker.py all
    python3 -B tutorial_type_checker.py 01
    python3 -B tutorial_type_checker.py 03_rewrites
    python3 -B tutorial_type_checker.py 05_comm

The scripts are intentionally tiny Lean-like files containing `constant`,
`inductive`, `def`, and `theorem` declarations. This runner parses the small
script subset used by the tutorial, imports the selected phase's `solution.py`,
and asks that phase's kernel to check each parsed declaration.
"""

from __future__ import annotations

import argparse
import importlib.util
import sys
from pathlib import Path
from types import ModuleType

import lean_parser
import solution_runner


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


def run_phase(phase_dir: Path) -> None:
    solution = load_solution(phase_dir)
    declarations = lean_parser.parse_script(phase_dir, solution)
    pretty = solution.pretty
    checker = solution_runner.setting_default_types(phase_dir, solution, declarations)

    print(phase_dir.relative_to(ROOT))
    for declaration in declarations:
        if solution_runner.should_register_before_check(declaration):
            solution_runner.register_declaration(solution, checker, declaration)
        declaration = lean_parser.elaborate_declaration_proof(solution, checker, declaration)
        checker.infer(declaration.expr)
        checker.check(declaration.expr, declaration.expected)
        if not solution_runner.should_register_before_check(declaration):
            solution_runner.register_declaration(solution, checker, declaration)
        print(f"  {declaration.name} : {pretty(declaration.expected)}")


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
