"""Substitution: the operations that move between `BVar` and real terms.

Mirrors `src/kernel/instantiate.cpp` and `src/kernel/abstract.cpp`.
"""

from __future__ import annotations

from .expr import App, BVar, Const, Expr, FVar, Lam, Let, Level, Pi, Proj, Sort
from .level import instantiate_level


def instantiate(body: Expr, value: Expr, depth: int = 0) -> Expr:
    """Replace the variable bound `depth` binders above `body` with `value`.

    `body` is what sits under a binder, so its `BVar(0)` (at the top; `BVar(1)`
    under one more binder, and so on) refers to that binder. `value` must
    contain no dangling `BVar`.
    """

    raise NotImplementedError("TODO: instantiate")


def abstract(expr: Expr, fvar: FVar, depth: int = 0) -> Expr:
    """The inverse of `instantiate`: replace `fvar` with the right `BVar`."""

    raise NotImplementedError("TODO: abstract")


def mk_pi(fvars: list[FVar], body: Expr) -> Expr:
    """Build `Π fvars, body`, binding each free variable. (Given.)"""

    for fvar in reversed(fvars):
        body = Pi(fvar.name, fvar.info, fvar.type, abstract(body, fvar))
    return body


def mk_lambda(fvars: list[FVar], body: Expr) -> Expr:
    """Build `fun fvars => body`, binding each free variable. (Given.)"""

    for fvar in reversed(fvars):
        body = Lam(fvar.name, fvar.info, fvar.type, abstract(body, fvar))
    return body


def has_loose_bvar(expr: Expr, index: int) -> bool:
    """Does `expr` mention the variable bound `index` binders above it? (Given.)"""

    match expr:
        case BVar(i):
            return i == index
        case App(fn, arg):
            return has_loose_bvar(fn, index) or has_loose_bvar(arg, index)
        case Lam(_, _, domain, body) | Pi(_, _, domain, body):
            return has_loose_bvar(domain, index) or has_loose_bvar(body, index + 1)
        case Let(_, ty, value, body):
            return has_loose_bvar(ty, index) or has_loose_bvar(value, index) or has_loose_bvar(body, index + 1)
        case Proj(_, _, inner):
            return has_loose_bvar(inner, index)
        case _:
            return False


def instantiate_level_params(expr: Expr, subst: dict[str, Level]) -> Expr:
    """Replace universe parameters throughout an expression."""

    raise NotImplementedError("TODO: instantiate_level_params")


def occurs(name: str, expr: Expr) -> bool:
    """Does the constant `name` appear anywhere in `expr`? (Given.)"""

    match expr:
        case Const(n, _):
            return n == name
        case App(fn, arg):
            return occurs(name, fn) or occurs(name, arg)
        case Lam(_, _, domain, body) | Pi(_, _, domain, body):
            return occurs(name, domain) or occurs(name, body)
        case Let(_, ty, value, body):
            return occurs(name, ty) or occurs(name, value) or occurs(name, body)
        case Proj(_, _, inner):
            return occurs(name, inner)
        case FVar():
            return False
        case _:
            return False
