"""Expression trees and universe levels. (Given: nothing to implement here.)

These classes mirror the kernel's C++ `expr` and `level` types one for one.
The trace printed by the instrumented kernel uses the same constructor names,
so a trace is a direct picture of the values defined in this file.
"""

from __future__ import annotations

from dataclasses import dataclass
from itertools import count

# --------------------------------------------------------------------------
# Universe levels (used from Chapter 2 on).
# --------------------------------------------------------------------------


@dataclass(frozen=True)
class Level:
    pass


@dataclass(frozen=True)
class Zero(Level):
    pass


@dataclass(frozen=True)
class Succ(Level):
    pred: Level


@dataclass(frozen=True)
class Max(Level):
    lhs: Level
    rhs: Level


@dataclass(frozen=True)
class IMax(Level):
    """`imax u v` is `0` when `v` is `0`, and `max u v` otherwise."""

    lhs: Level
    rhs: Level


@dataclass(frozen=True)
class Param(Level):
    name: str


def level_of_nat(n: int) -> Level:
    level: Level = Zero()
    for _ in range(n):
        level = Succ(level)
    return level


# --------------------------------------------------------------------------
# Expressions.
# --------------------------------------------------------------------------


@dataclass(frozen=True)
class Expr:
    pass


@dataclass(frozen=True)
class BVar(Expr):
    """A bound variable. `index` counts binders outward, starting at 0."""

    index: int


@dataclass(frozen=True, eq=False)
class FVar(Expr):
    """A free variable: a bound variable whose binder we have stepped inside.

    Never appears in a trace. The type checker creates one each time it goes
    under a `Lam` or `Pi`, so that the body has no dangling `BVar`. Two free
    variables are equal only if they are the same object.
    """

    name: str
    type: Expr
    info: str = "default"

    _ids = count()

    def __post_init__(self) -> None:
        object.__setattr__(self, "id", next(FVar._ids))

    # Identity, not structure: two variables with the same name and type are
    # still different variables.
    def __eq__(self, other: object) -> bool:
        return self is other

    def __hash__(self) -> int:
        return id(self)

    def __repr__(self) -> str:
        return f"FVar({self.name}#{self.id})"


@dataclass(frozen=True)
class Sort(Expr):
    level: Level


@dataclass(frozen=True)
class Const(Expr):
    name: str
    levels: tuple[Level, ...] = ()


@dataclass(frozen=True)
class App(Expr):
    fn: Expr
    arg: Expr


@dataclass(frozen=True)
class Lam(Expr):
    name: str
    info: str  # default, implicit, strict_implicit, inst_implicit
    domain: Expr
    body: Expr


@dataclass(frozen=True)
class Pi(Expr):
    name: str
    info: str
    domain: Expr
    body: Expr


@dataclass(frozen=True)
class Let(Expr):
    name: str
    type: Expr
    value: Expr
    body: Expr


@dataclass(frozen=True)
class Lit(Expr):
    kind: str  # "nat" or "string"
    value: str


@dataclass(frozen=True)
class Proj(Expr):
    """Field number `index` (from 0) of a value of structure `struct`."""

    struct: str
    index: int
    expr: Expr


Prop = Sort(Zero())
Type = Sort(Succ(Zero()))


def spine(expr: Expr) -> tuple[Expr, list[Expr]]:
    """Split `f a b c` into `(f, [a, b, c])`."""

    args: list[Expr] = []
    while isinstance(expr, App):
        args.append(expr.arg)
        expr = expr.fn
    args.reverse()
    return expr, args


def mk_app(fn: Expr, args: list[Expr] | tuple[Expr, ...]) -> Expr:
    for arg in args:
        fn = App(fn, arg)
    return fn


def erase_binder_names(expr: Expr) -> Expr:
    """Replace every binder name with `_`. Names never matter to the kernel."""

    match expr:
        case App(fn, arg):
            return App(erase_binder_names(fn), erase_binder_names(arg))
        case Lam(_, info, domain, body):
            return Lam("_", info, erase_binder_names(domain), erase_binder_names(body))
        case Pi(_, info, domain, body):
            return Pi("_", info, erase_binder_names(domain), erase_binder_names(body))
        case Let(_, ty, value, body):
            return Let("_", erase_binder_names(ty), erase_binder_names(value), erase_binder_names(body))
        case Proj(struct, index, inner):
            return Proj(struct, index, erase_binder_names(inner))
        case _:
            return expr
