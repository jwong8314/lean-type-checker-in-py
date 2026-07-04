"""Print the kernel expression trees produced from a tutorial `.lean` script."""

from __future__ import annotations

import argparse
from pathlib import Path

import solution_runner
from pylean import elaborator, lean_parser
from pylean.tutorial_type_checker import load_solution


def print_script_ast(script_path: Path) -> None:
    chapter_dir = script_path.resolve().parent
    solution = load_solution(chapter_dir)
    declarations = lean_parser.parse_script(chapter_dir, solution)
    checker = solution_runner.setting_default_types(chapter_dir, solution)

    for declaration in declarations:
        if solution_runner.should_register_before_check(declaration):
            solution_runner.register_declaration(solution, checker, declaration)

        declaration = elaborator.elaborate_declaration(solution, checker, declaration)
        print(f"{declaration.name} :")
        print(f"  kind     = {declaration.kind}")
        print(f"  expr     = {declaration.expr!r}")
        print(f"  expected = {declaration.expected!r}")
        print()

        if not solution_runner.should_register_before_check(declaration):
            solution_runner.register_declaration(solution, checker, declaration)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("script", type=Path, help="Path to a chapter script.lean file")
    args = parser.parse_args()
    print_script_ast(args.script)


if __name__ == "__main__":
    main()
