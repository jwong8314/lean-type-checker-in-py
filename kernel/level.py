"""Universe levels: substitution, simplification, and comparison.

Mirrors `src/kernel/level.cpp`. The algorithm for `leq` follows the one used
by Lean's kernel and by the independent checkers `lean4lean` and `nanoda`.
"""

from __future__ import annotations

from .expr import IMax, Level, Max, Param, Succ, Zero


def instantiate_level(level: Level, subst: dict[str, Level]) -> Level:
    """Replace each `Param(name)` with `subst[name]`."""

    raise NotImplementedError("TODO: instantiate_level")


def level_params(level: Level) -> set[str]:
    """Names of all universe parameters that occur in `level`."""

    raise NotImplementedError("TODO: level_params")


def simplify(level: Level) -> Level:
    """Remove the easy redundancies.

    - `max 0 u = u`, `max u 0 = u`
    - `imax u 0 = 0`
    - `imax u (succ v) = max u (succ v)`   (the right side is never 0)
    - `imax 0 u = u`
    """

    raise NotImplementedError("TODO: simplify")


def leq(a: Level, b: Level, diff: int = 0) -> bool:
    """Is `a <= b + diff` for every assignment of the parameters?"""

    raise NotImplementedError("TODO: leq")


def is_equiv(a: Level, b: Level) -> bool:
    """Are the two levels equal for every assignment of the parameters?"""

    raise NotImplementedError("TODO: is_equiv")
