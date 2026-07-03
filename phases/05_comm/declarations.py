"""AST bridge for phase 5 script declarations."""

from __future__ import annotations

import solution


def declaration(name: str):
    if name == "zero_add":
        return solution.zero_add_case()
    if name == "succ_add_succ":
        return solution.succ_add_succ_case()
    if name == "add_assoc":
        return solution.add_assoc_case()
    if name == "add_comm":
        return solution.add_comm_case()
    raise KeyError(name)
