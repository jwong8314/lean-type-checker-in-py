"""Build checkers and register parsed script declarations.

The runner should not know the names of tutorial theorems.  It gets declaration
metadata from `lean_parser.py`, registers opaque constants before checking them,
and registers checked declarations afterwards.  Phase solutions may still expose
small hooks for kernel features that the script language cannot express yet,
such as installing a Python reducer.
"""

from __future__ import annotations

from pathlib import Path
from types import ModuleType
from typing import Iterable


def setting_default_types(phase_dir: Path, solution: ModuleType, declarations: Iterable[object]):
    checker = solution.TypeChecker()
    if needs_previous_phase_context(declarations):
        seed_previous_phase_scripts(phase_dir, solution, checker)
    return checker


def needs_previous_phase_context(declarations: Iterable[object]) -> bool:
    return not any(getattr(declaration, "kind", None) == "inductive" for declaration in declarations)


def seed_previous_phase_scripts(phase_dir: Path, solution: ModuleType, checker) -> None:
    import lean_parser

    current_number = phase_number(phase_dir)
    for prior_dir in sorted(phase_dir.parent.iterdir()):
        prior_number = phase_number(prior_dir)
        if prior_number is None or prior_number < 2 or prior_number >= current_number:
            continue
        for declaration in lean_parser.parse_script(prior_dir, solution):
            register_declaration(solution, checker, declaration)


def phase_number(phase_dir: Path) -> int | None:
    try:
        return int(phase_dir.name.split("_", 1)[0])
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
