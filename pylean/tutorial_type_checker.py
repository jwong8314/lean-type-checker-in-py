"""Run Lean-like chapter scripts against the corresponding Python kernel.

Usage:

    python3 -B -m pylean.tutorial_type_checker all
    python3 -B -m pylean.tutorial_type_checker 01
    python3 -B -m pylean.tutorial_type_checker 03_rewrites
    python3 -B -m pylean.tutorial_type_checker 07_comm

The scripts are intentionally tiny Lean-like files containing `constant`,
`inductive`, `def`, and `theorem` declarations. This runner parses the small
script subset used by the tutorial, imports the selected chapter's `solution.py`,
and asks that chapter's kernel to check each parsed declaration.
"""

from __future__ import annotations

import argparse
from pathlib import Path
from types import ModuleType

from pylean.chapter_loader import ChapterLoadError, load_solution_for_dir
from pylean import elaborator, lean_parser
import solution_runner


ROOT = Path(__file__).resolve().parents[1]
CHAPTER_DIRS = {
    "01": ROOT / "chapters/01_true_false",
    "02": ROOT / "chapters/02_recursive_nat",
    "03": ROOT / "chapters/03_rewrites",
    "04": ROOT / "chapters/04_rfl",
    "05": ROOT / "chapters/05_cases",
    "06": ROOT / "chapters/06_induction",
    "07": ROOT / "chapters/07_comm",
}


class RunnerError(Exception):
    pass


def load_solution(chapter_dir: Path) -> ModuleType:
    try:
        return load_solution_for_dir(chapter_dir)
    except ChapterLoadError as exc:
        raise RunnerError(str(exc)) from exc


def run_chapter(chapter_dir: Path, trace_elab: bool = False) -> None:
    solution = load_solution(chapter_dir)
    declarations = lean_parser.parse_script(chapter_dir, solution)
    checker = solution_runner.setting_default_types(chapter_dir, solution)

    print(chapter_dir.relative_to(ROOT))
    for declaration in declarations:
        if solution_runner.should_register_before_check(declaration):
            solution_runner.register_declaration(solution, checker, declaration)
        trace: list[elaborator.ElaborationTrace] | None = [] if trace_elab else None
        declaration = elaborator.elaborate_declaration(solution, checker, declaration, trace)
        if trace:
            for event in trace:
                print(f"  [elab] {event.name}")
                print(f"    syntax = {event.proof_ast!r}")
                print(f"    before = {event.before!r}")
                print(f"    after  = {event.after!r}")
        checker.infer(declaration.expr)
        checker.check(declaration.expr, declaration.expected)
        if not solution_runner.should_register_before_check(declaration):
            solution_runner.register_declaration(solution, checker, declaration)
        print(f"  {declaration.name} : {checker.pretty(declaration.expected)}")


def select_chapters(request: str) -> list[Path]:
    if request == "all":
        return list(CHAPTER_DIRS.values())
    for key, path in CHAPTER_DIRS.items():
        if request == key or request == path.name:
            return [path]
    known = ", ".join(["all", *CHAPTER_DIRS.keys(), *(p.name for p in CHAPTER_DIRS.values())])
    raise RunnerError(f"unknown chapter {request!r}; expected one of: {known}")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("chapter", nargs="?", default="all")
    parser.add_argument("--trace-elab", action="store_true", help="print proof elaboration before kernel checking")
    args = parser.parse_args()

    for chapter_dir in select_chapters(args.chapter):
        run_chapter(chapter_dir, args.trace_elab)
        print()


if __name__ == "__main__":
    main()
