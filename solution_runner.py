"""Build checkers and register parsed script declarations.

The runner should not know the names of tutorial theorems.  It gets declaration
metadata from `pylean.lean_parser`, registers opaque constants before checking
them, and registers checked declarations afterwards. Chapter solutions may
still expose small hooks for kernel features that the script language cannot
express yet, such as installing a Python reducer.
"""

from __future__ import annotations

from pathlib import Path
from types import ModuleType
from typing import Iterable


def setting_default_types(chapter_dir: Path, solution: ModuleType, declarations: Iterable[object]):
    checker = solution.TypeChecker()
    if needs_previous_chapter_context(declarations):
        seed_previous_chapter_scripts(chapter_dir, solution, checker)
    return checker


def needs_previous_chapter_context(declarations: Iterable[object]) -> bool:
    return not any(getattr(declaration, "kind", None) == "inductive" for declaration in declarations)


def seed_previous_chapter_scripts(chapter_dir: Path, solution: ModuleType, checker) -> None:
    from pylean import lean_parser

    current_number = chapter_number(chapter_dir)
    for prior_dir in sorted(chapter_dir.parent.iterdir()):
        prior_number = chapter_number(prior_dir)
        if prior_number is None or prior_number < 2 or prior_number >= current_number:
            continue
        for declaration in lean_parser.parse_script(prior_dir, solution):
            register_declaration(solution, checker, declaration)


def chapter_number(chapter_dir: Path) -> int | None:
    try:
        return int(chapter_dir.name.split("_", 1)[0])
    except ValueError:
        return None


def should_register_before_check(declaration: object) -> bool:
    if getattr(declaration, "recursive_spec", None) is not None:
        return True
    return bool(getattr(declaration, "opaque", False))


def register_declaration(solution: ModuleType, checker, declaration: object) -> None:
    recursive_spec = getattr(declaration, "recursive_spec", None)
    if recursive_spec is not None and hasattr(checker, "add_recursive_type"):
        if declaration.name not in checker.env:
            checker.add_recursive_type(recursive_spec)
    elif declaration.name not in checker.env:
        checker.add(declaration.name, declaration.expected)

    after_register = getattr(solution, "after_register_declaration", None)
    if after_register is not None:
        after_register(checker, declaration)
