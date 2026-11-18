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

    # BEGIN SOLUTION
    match body:
        case BVar(index):
            if index == depth:
                return value
            return BVar(index - 1) if index > depth else body
        case App(fn, arg):
            return App(instantiate(fn, value, depth), instantiate(arg, value, depth))
        case Lam(name, info, domain, inner):
            return Lam(name, info, instantiate(domain, value, depth), instantiate(inner, value, depth + 1))
        case Pi(name, info, domain, inner):
            return Pi(name, info, instantiate(domain, value, depth), instantiate(inner, value, depth + 1))
        case Let(name, ty, val, inner):
            return Let(
                name, instantiate(ty, value, depth), instantiate(val, value, depth), instantiate(inner, value, depth + 1)
            )
        case Proj(struct, index, inner):
            return Proj(struct, index, instantiate(inner, value, depth))
        case _:
            return body
    # END SOLUTION


def abstract(expr: Expr, fvar: FVar, depth: int = 0) -> Expr:
    """The inverse of `instantiate`: replace `fvar` with the right `BVar`."""

    # BEGIN SOLUTION
    match expr:
        case FVar():
            return BVar(depth) if expr is fvar else expr
        case App(fn, arg):
            return App(abstract(fn, fvar, depth), abstract(arg, fvar, depth))
        case Lam(name, info, domain, inner):
            return Lam(name, info, abstract(domain, fvar, depth), abstract(inner, fvar, depth + 1))
        case Pi(name, info, domain, inner):
            return Pi(name, info, abstract(domain, fvar, depth), abstract(inner, fvar, depth + 1))
        case Let(name, ty, val, inner):
            return Let(name, abstract(ty, fvar, depth), abstract(val, fvar, depth), abstract(inner, fvar, depth + 1))
        case Proj(struct, index, inner):
            return Proj(struct, index, abstract(inner, fvar, depth))
        case _:
            return expr
    # END SOLUTION


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

    # BEGIN SOLUTION
    if not subst:
        return expr
    match expr:
        case Sort(level):
            return Sort(instantiate_level(level, subst))
        case Const(name, levels):
            return Const(name, tuple(instantiate_level(level, subst) for level in levels))
        case App(fn, arg):
            return App(instantiate_level_params(fn, subst), instantiate_level_params(arg, subst))
        case Lam(name, info, domain, body):
            return Lam(name, info, instantiate_level_params(domain, subst), instantiate_level_params(body, subst))
        case Pi(name, info, domain, body):
            return Pi(name, info, instantiate_level_params(domain, subst), instantiate_level_params(body, subst))
        case Let(name, ty, value, body):
            return Let(
                name,
                instantiate_level_params(ty, subst),
                instantiate_level_params(value, subst),
                instantiate_level_params(body, subst),
            )
        case Proj(struct, index, inner):
            return Proj(struct, index, instantiate_level_params(inner, subst))
        case _:
            return expr
    # END SOLUTION


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
