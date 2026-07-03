"""AST bridge for phase 5 script declarations."""

from __future__ import annotations

import solution


def declaration(name: str):
    if name == "MyNat":
        return solution.mynat_case()
    if name == "zero":
        return solution.zero_case()
    if name == "succ":
        return solution.succ_case()
    if name == "add":
        return solution.add_case()
    if name == "my_add_zero":
        return solution.my_add_zero_case()
    if name == "my_add_succ":
        return solution.my_add_succ_case()
    if name == "succ_add":
        return solution.succ_add_case()
    if name == "zero_add":
        return solution.zero_add_case()
    if name == "succ_add_succ":
        return solution.succ_add_succ_case()
    if name == "add_assoc":
        return solution.add_assoc_case()
    if name == "add_comm":
        return solution.add_comm_case()
    if name == "add_right_comm":
        return solution.add_right_comm_case()
    raise KeyError(name)
