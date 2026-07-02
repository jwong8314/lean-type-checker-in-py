"""AST bridge for phase 3 script declarations."""

from __future__ import annotations

import solution


def declaration(name: str):
    if name == "Eq":
        return solution.eq_decl_case()
    if name == "rfl_nat":
        return solution.rfl_nat_case()
    if name == "add":
        return solution.add_decl_case()
    if name == "add_zero":
        return solution.add_zero_case()
    if name == "add_succ":
        return solution.add_succ_case()
    if name == "rw":
        return solution.rw_case()
    if name == "add_zero_by_rfl":
        return solution.add_zero_by_rfl_case()
    if name == "add_succ_by_rfl":
        return solution.add_succ_by_rfl_case()
    if name == "rewrite_step":
        return solution.rewrite_step_case()
    raise KeyError(name)
