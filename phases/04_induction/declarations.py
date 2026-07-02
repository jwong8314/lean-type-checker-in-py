"""AST bridge for phase 4 script declarations."""

from __future__ import annotations

import solution


def declaration(name: str):
    if name == "succ_add":
        return solution.theorem_proof(), solution.theorem_type()
    raise KeyError(name)
