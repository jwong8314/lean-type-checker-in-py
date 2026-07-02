"""AST bridge for phase 2 script declarations."""

from __future__ import annotations

import solution


def declaration(name: str):
    if name == "Nat":
        return solution.Nat, solution.Type
    if name == "zero":
        return solution.zero, solution.Nat
    if name == "succ":
        return solution.succ, solution.arrow(solution.Nat, solution.Nat)
    if name == "one":
        return solution.one, solution.Nat
    if name == "two":
        return solution.two, solution.Nat
    raise KeyError(name)
