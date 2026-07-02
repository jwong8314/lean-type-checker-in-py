"""Run Lean-like phase scripts against the corresponding Python kernel.

Usage:

    python3 -B tutorial_type_checker.py all
    python3 -B tutorial_type_checker.py 01
    python3 -B tutorial_type_checker.py 03_rewrites
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


def script_directives(phase_dir: Path) -> list[tuple[str, str]]:
    path = phase_dir / "script.lean"
    directives: list[tuple[str, str]] = []
    for lineno, line in enumerate(path.read_text().splitlines(), start=1):
        stripped = line.strip()
        if stripped.startswith("#check "):
            directives.append(("check", stripped.removeprefix("#check ").strip()))
        elif stripped.startswith("#reject "):
            directives.append(("reject", stripped.removeprefix("#reject ").strip()))
        elif stripped.startswith("#"):
            raise RunnerError(f"{path}:{lineno}: unknown directive {stripped}")
    return directives


def run_phase(phase_dir: Path) -> None:
    solution = load_solution(phase_dir)
    infer = solution.infer
    check = solution.check
    cases = solution.SCRIPT
    pretty = solution.pretty

    print(phase_dir.relative_to(ROOT))
    for kind, name in script_directives(phase_dir):
        if name not in cases:
            raise RunnerError(f"{phase_dir / 'script.lean'}: no SCRIPT case named {name!r}")
        expr, expected, should_accept = cases[name]
        if kind == "reject":
            should_accept = False

        try:
            inferred = infer(expr)
            check(expr, expected)
        except Exception as exc:
            if should_accept:
                raise
            print(f"  rejected {name}")
            continue

        if not should_accept:
            raise RunnerError(f"{name} was expected to be rejected")
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
