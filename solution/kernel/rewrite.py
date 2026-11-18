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

    # BEGIN SOLUTION
    if expr == pattern:
        return BVar(depth)
    match expr:
        case App(fn, arg):
            return App(kabstract(fn, pattern, depth), kabstract(arg, pattern, depth))
        case Lam(name, info, domain, body):
            return Lam(name, info, kabstract(domain, pattern, depth), kabstract(body, pattern, depth + 1))
        case Pi(name, info, domain, body):
            return Pi(name, info, kabstract(domain, pattern, depth), kabstract(body, pattern, depth + 1))
        case Let(name, ty, value, body):
            return Let(
                name,
                kabstract(ty, pattern, depth),
                kabstract(value, pattern, depth),
                kabstract(body, pattern, depth + 1),
            )
        case Proj(struct, index, inner):
            return Proj(struct, index, kabstract(inner, pattern, depth))
        case _:
            return expr
    # END SOLUTION


def rewrite(checker: TypeChecker, goal: Expr, h: Expr) -> tuple[Expr, Expr]:
    """Rewrite `goal` with the equation proved by `h`.

    Returns `(new_goal, eq_proof)` where `eq_proof : goal = new_goal`.
    Raises `KernelError` when `h` is not an equation, when its left-hand side
    does not occur in the goal, or when the motive does not type check.
    """

    # BEGIN SOLUTION
    head, args = spine(checker.whnf(checker.infer(h)))
    if not (isinstance(head, Const) and head.name == "Eq" and len(args) == 3):
        raise KernelError("rw: equality proof expected")
    alpha, lhs, rhs = args
    abstracted = kabstract(goal, lhs)
    if abstracted == goal:
        raise KernelError("rw: did not find an instance of the pattern in the goal")
    motive = Lam("_a", "default", alpha, abstracted)
    new_goal = instantiate(abstracted, rhs)
    try:
        checker.infer(motive)
    except KernelError as error:
        raise KernelError("rw: motive is not type correct") from error
    beta = checker.infer(goal)  # the goal is a proposition, so this is `Prop`
    u = simplify(checker.ensure_sort(checker.infer(alpha)).level)
    v = simplify(checker.ensure_sort(checker.infer(beta)).level)
    eq_proof = mk_app(Const("congrArg", (u, v)), [alpha, beta, lhs, rhs, motive, h])
    return new_goal, eq_proof
    # END SOLUTION


def mk_eq_mpr(checker: TypeChecker, goal: Expr, new_goal: Expr, eq_proof: Expr, rest: Expr) -> Expr:
    """Turn a proof of the new goal into a proof of the old one.

    Given `eq_proof : goal = new_goal` and `rest : new_goal`, build exactly
    what Lean builds:

        @Eq.mpr goal new_goal (@id (goal = new_goal) eq_proof) rest

    The `id` does nothing; Lean inserts it to remember the intended type.
    """

    # BEGIN SOLUTION
    goal_sort = checker.ensure_sort(checker.infer(goal))
    u = simplify(goal_sort.level)
    eq_type = mk_app(Const("Eq", (Succ(u),)), [Sort(u), goal, new_goal])
    hinted = mk_app(Const("id", (simplify(checker.ensure_sort(checker.infer(eq_type)).level),)), [eq_type, eq_proof])
    return mk_app(Const("Eq.mpr", (u,)), [goal, new_goal, hinted, rest])
    # END SOLUTION
