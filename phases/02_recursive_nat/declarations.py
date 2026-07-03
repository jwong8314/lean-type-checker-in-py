"""AST bridge for phase 2 script declarations."""

from __future__ import annotations

import solution


def declaration(name: str):
    if name == "MyNat":
        return solution.MyNat, solution.Type
    if name == "zero":
        return solution.zero, solution.MyNat
    if name == "succ":
        return solution.succ, solution.arrow(solution.MyNat, solution.MyNat)
    if name == "one":
        return solution.one, solution.MyNat
    if name == "two":
        return solution.two, solution.MyNat
    raise KeyError(name)
