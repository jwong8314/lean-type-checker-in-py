"""AST bridge for phase 2 script declarations."""

from __future__ import annotations

import solution


def one():
    return solution.apps(solution.succ, solution.zero)


def two():
    return solution.apps(solution.succ, one())


def eq_type():
    return solution.arrow(
        solution.Type,
        solution.arrow(solution.MyNat, solution.arrow(solution.MyNat, solution.Prop)),
    )


def rfl_nat_type():
    x = solution.Var("x")
    return solution.Pi("x", solution.MyNat, solution.Eq(solution.MyNat, x, x))


def declaration(name: str):
    if name == "MyNat":
        return solution.MyNat, solution.Type
    if name == "zero":
        return solution.zero, solution.MyNat
    if name == "succ":
        return solution.succ, solution.arrow(solution.MyNat, solution.MyNat)
    if name == "one":
        return one(), solution.MyNat
    if name == "two":
        return two(), solution.MyNat
    if name == "Eq":
        return solution.EqConst, eq_type()
    if name == "rfl_nat":
        x = solution.Var("x")
        return solution.Lam("x", solution.MyNat, solution.Refl(solution.MyNat, x)), rfl_nat_type()
    raise KeyError(name)
