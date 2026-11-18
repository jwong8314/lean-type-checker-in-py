"""Universe levels: substitution, simplification, and comparison.

Mirrors `src/kernel/level.cpp`. The algorithm for `leq` follows the one used
by Lean's kernel and by the independent checkers `lean4lean` and `nanoda`.
"""

from __future__ import annotations

from .expr import IMax, Level, Max, Param, Succ, Zero


def instantiate_level(level: Level, subst: dict[str, Level]) -> Level:
    """Replace each `Param(name)` with `subst[name]`."""

    # BEGIN SOLUTION
    match level:
        case Param(name):
            return subst.get(name, level)
        case Succ(pred):
            return Succ(instantiate_level(pred, subst))
        case Max(lhs, rhs):
            return Max(instantiate_level(lhs, subst), instantiate_level(rhs, subst))
        case IMax(lhs, rhs):
            return IMax(instantiate_level(lhs, subst), instantiate_level(rhs, subst))
        case _:
            return level
    # END SOLUTION


def level_params(level: Level) -> set[str]:
    """Names of all universe parameters that occur in `level`."""

    # BEGIN SOLUTION
    match level:
        case Param(name):
            return {name}
        case Succ(pred):
            return level_params(pred)
        case Max(lhs, rhs) | IMax(lhs, rhs):
            return level_params(lhs) | level_params(rhs)
        case _:
            return set()
    # END SOLUTION


def simplify(level: Level) -> Level:
    """Remove the easy redundancies.

    - `max 0 u = u`, `max u 0 = u`
    - `imax u 0 = 0`
    - `imax u (succ v) = max u (succ v)`   (the right side is never 0)
    - `imax 0 u = u`
    """

    # BEGIN SOLUTION
    match level:
        case Succ(pred):
            return Succ(simplify(pred))
        case Max(lhs, rhs):
            lhs, rhs = simplify(lhs), simplify(rhs)
            if isinstance(lhs, Zero):
                return rhs
            if isinstance(rhs, Zero) or lhs == rhs:
                return lhs
            return Max(lhs, rhs)
        case IMax(lhs, rhs):
            lhs, rhs = simplify(lhs), simplify(rhs)
            if isinstance(rhs, Zero):
                return rhs
            if isinstance(rhs, Succ):
                return simplify(Max(lhs, rhs))
            if isinstance(lhs, Zero) or lhs == rhs:
                return rhs
            return IMax(lhs, rhs)
        case _:
            return level
    # END SOLUTION


def leq(a: Level, b: Level, diff: int = 0) -> bool:
    """Is `a <= b + diff` for every assignment of the parameters?"""

    # BEGIN SOLUTION
    a, b = simplify(a), simplify(b)
    match a, b:
        case Zero(), _ if diff >= 0:
            return True
        case _, Zero() if diff < 0:
            return False
        case Param(x), Param(y):
            return x == y and diff >= 0
        case Param(_), Zero():
            return False
        case Zero(), Param(_):
            return diff >= 0
        case Succ(pred), _:
            return leq(pred, b, diff - 1)
        case _, Succ(pred):
            return leq(a, pred, diff + 1)
        case Max(lhs, rhs), _:
            return leq(lhs, b, diff) and leq(rhs, b, diff)
        case (Param(_) | Zero()), Max(lhs, rhs):
            return leq(a, lhs, diff) or leq(a, rhs, diff)
        case IMax(_, _), IMax(_, _) if a == b:
            return diff >= 0
        case (IMax(_, Param(p)), _) | (_, IMax(_, Param(p))):
            # `imax u p` depends on whether `p` is 0. Try both.
            zero = {p: Zero()}
            succ = {p: Succ(Param(p))}
            return leq(instantiate_level(a, zero), instantiate_level(b, zero), diff) and leq(
                instantiate_level(a, succ), instantiate_level(b, succ), diff
            )
        case IMax(x, IMax(y, z)), _:
            return leq(Max(IMax(x, z), IMax(y, z)), b, diff)
        case IMax(x, Max(y, z)), _:
            return leq(Max(IMax(x, y), IMax(x, z)), b, diff)
        case _, IMax(x, IMax(y, z)):
            return leq(a, Max(IMax(x, z), IMax(y, z)), diff)
        case _, IMax(x, Max(y, z)):
            return leq(a, Max(IMax(x, y), IMax(x, z)), diff)
    raise AssertionError(f"leq: unhandled case {a!r} <= {b!r}")
    # END SOLUTION


def is_equiv(a: Level, b: Level) -> bool:
    """Are the two levels equal for every assignment of the parameters?"""

    # BEGIN SOLUTION
    return a == b or (leq(a, b) and leq(b, a))
    # END SOLUTION
