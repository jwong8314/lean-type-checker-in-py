"""Chapter 5: the `rw` tactic, as a function that builds a proof term.

This file is *not* part of the kernel. It is a piece of the elaborator: the
large, untrusted program that turns what you type into the trees the kernel
checks. Mirrors `Lean.MVarId.rewrite` in `src/Lean/Meta/Tactic/Rewrite.lean`.

`rw [h]` with `h : lhs = rhs` on a goal `G` produces

    Eq.mpr (id (congrArg (fun _a => G[lhs := _a]) h)) ?rest

where `?rest` is a proof of the new goal `G[lhs := rhs]`.
"""

from __future__ import annotations

from .environment import KernelError
from .expr import App, BVar, Const, Expr, Lam, Let, Pi, Proj, Sort, Succ, mk_app, spine
from .level import simplify
from .subst import instantiate
from .typechecker import TypeChecker


def kabstract(expr: Expr, pattern: Expr, depth: int = 0) -> Expr:
    """Replace every occurrence of `pattern` in `expr` with a bound variable.

    The result is meant to sit under one new binder, so an occurrence at the
    top becomes `BVar(0)`, one under a binder becomes `BVar(1)`, and so on.
    Occurrences are found by plain structural equality.
    """

    raise NotImplementedError("TODO: kabstract")


def rewrite(checker: TypeChecker, goal: Expr, h: Expr) -> tuple[Expr, Expr]:
    """Rewrite `goal` with the equation proved by `h`.

    Returns `(new_goal, eq_proof)` where `eq_proof : goal = new_goal`.
    Raises `KernelError` when `h` is not an equation, when its left-hand side
    does not occur in the goal, or when the motive does not type check.
    """

    raise NotImplementedError("TODO: rewrite")


def mk_eq_mpr(checker: TypeChecker, goal: Expr, new_goal: Expr, eq_proof: Expr, rest: Expr) -> Expr:
    """Turn a proof of the new goal into a proof of the old one.

    Given `eq_proof : goal = new_goal` and `rest : new_goal`, build exactly
    what Lean builds:

        @Eq.mpr goal new_goal (@id (goal = new_goal) eq_proof) rest

    The `id` does nothing; Lean inserts it to remember the intended type.
    """

    raise NotImplementedError("TODO: mk_eq_mpr")
