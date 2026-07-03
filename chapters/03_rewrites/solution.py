"""Chapter 3 solution: equality, rfl, computation, and a tiny rewrite."""

from __future__ import annotations

from typing import Callable

from .expressions import (
    Eq,
    EqConst,
    Lam,
    Refl,
    SuccCongr,
    add,
    alpha_equal,
    atom,
    p2,
    pretty,
    subst,
)


Reducer = Callable[["TypeChecker", p2.Expr], p2.Expr | None]


class TypeChecker(p2.TypeChecker):
    def __init__(self) -> None:
        super().__init__()
        self.reducers: dict[str, Reducer] = {}

    def add_reducer(self, name: str, reducer: Reducer) -> None:
        self.reducers[name] = reducer

    def infer(self, expr: p2.Expr, ctx: dict[str, p2.Expr] | None = None) -> p2.Expr:
        ctx = {} if ctx is None else ctx
        match expr:
            case p2.App(fn, arg):
                fn_ty = self.infer(fn, ctx)
                if not isinstance(fn_ty, p2.Pi):
                    raise p2.TypeError(f"expected function type, got {pretty(fn_ty)}")
                self.check(arg, fn_ty.domain, ctx)
                return subst(fn_ty.body, fn_ty.var, arg)
            case Lam(var, domain, body):
                if not isinstance(self.infer(domain, ctx), p2.Sort):
                    raise p2.TypeError(f"lambda domain is not a sort: {pretty(domain)}")
                return p2.Pi(var, domain, self.infer(body, ctx | {var: domain}))
            case Eq(ty, lhs, rhs):
                self.check(ty, p2.Type, ctx)
                self.check(lhs, ty, ctx)
                self.check(rhs, ty, ctx)
                return p2.Prop
            case Refl(ty, value):
                self.check(ty, p2.Type, ctx)
                self.check(value, ty, ctx)
                return Eq(ty, value, value)
            case SuccCongr(proof):
                proof_ty = self.whnf(self.infer(proof, ctx))
                if not isinstance(proof_ty, Eq):
                    raise p2.TypeError("succ congruence expected an equality proof")
                self.check(proof_ty.ty, p2.Type, ctx)
                if not self.defeq(proof_ty.ty, p2.MyNat):
                    raise p2.TypeError("succ congruence only handles MyNat equalities in this tutorial")
                return Eq(p2.MyNat, p2.apps(p2.succ, proof_ty.lhs), p2.apps(p2.succ, proof_ty.rhs))
            case _:
                return super().infer(expr, ctx)

    def whnf(self, expr: p2.Expr) -> p2.Expr:
        while True:
            match expr:
                case p2.App(fn, arg):
                    fn = self.whnf(fn)
                    if isinstance(fn, Lam):
                        expr = subst(fn.body, fn.var, arg)
                        continue
                    rebuilt = p2.App(fn, arg)
                    reduced = self.try_reduce(rebuilt)
                    if reduced is not None:
                        expr = reduced
                        continue
                    return rebuilt
                case _:
                    return expr

    def normalize(self, expr: p2.Expr) -> p2.Expr:
        expr = self.whnf(expr)
        match expr:
            case p2.App(fn, arg):
                return self.whnf(p2.App(self.normalize(fn), self.normalize(arg)))
            case p2.Pi(var, domain, body):
                return p2.Pi(var, self.normalize(domain), self.normalize(body))
            case Lam(var, domain, body):
                return Lam(var, self.normalize(domain), self.normalize(body))
            case Eq(ty, lhs, rhs):
                return Eq(self.normalize(ty), self.normalize(lhs), self.normalize(rhs))
            case Refl(ty, value):
                return Refl(self.normalize(ty), self.normalize(value))
            case SuccCongr(proof):
                return SuccCongr(self.normalize(proof))
            case _:
                return expr

    def defeq(self, left: p2.Expr, right: p2.Expr) -> bool:
        return left == right

    def try_reduce(self, expr: p2.Expr) -> p2.Expr | None:
        head, _ = p2.spine(expr)
        if isinstance(head, p2.Const) and head.name in self.reducers:
            return self.reducers[head.name](self, expr)
        return None

    def pretty(self, expr: p2.Expr) -> str:
        return pretty(expr)

    def execute_tactics(self, goal: p2.Expr, tactics, lower_expr) -> p2.Expr:
        if len(tactics) == 1 and tactics[0].__class__.__name__ == "RflNode":
            if not isinstance(goal, Eq):
                raise p2.TypeError("rfl expected an equality goal")
            return Refl(goal.ty, goal.rhs)
        for tactic in reversed(tactics):
            if tactic.__class__.__name__ == "RwNode":
                if not tactic.args:
                    raise p2.TypeError("rw expects at least one rewrite rule")
                return rewrite_goal(self, goal, lower_expr(tactic.args[-1]))
        return super().execute_tactics(goal, tactics, lower_expr)


def nat_add_reducer(tc: TypeChecker, expr: p2.Expr) -> p2.Expr | None:
    head, args = p2.spine(expr)
    if not (isinstance(head, p2.Const) and head.name == "add" and len(args) == 2):
        return None
    first, second = args
    second = tc.whnf(second)
    if alpha_equal(second, p2.zero):
        return first
    second_head, second_args = p2.spine(second)
    if isinstance(second_head, p2.Const) and second_head.name == "succ" and len(second_args) == 1:
        return p2.apps(p2.succ, p2.apps(add, first, second_args[0]))
    return None


def rewrite_goal(tc: TypeChecker, goal: p2.Expr, proof: p2.Expr) -> p2.Expr:
    """Elaborate `rw proof` for the tiny Chapter 3 rewrite language.

    The tactic layer is where we inspect the current goal and turn rewrite
    syntax into a regular proof object. The kernel then only sees
    `SuccCongr(proof)`, not a primitive `rw`.
    """

    proof_ty = tc.whnf(tc.infer(proof))
    if not isinstance(goal, Eq) or not isinstance(proof_ty, Eq):
        raise p2.TypeError("rw expected an equality goal and equality proof")
    expected = Eq(p2.MyNat, p2.apps(p2.succ, proof_ty.lhs), p2.apps(p2.succ, proof_ty.rhs))
    if not tc.defeq(goal, expected):
        raise p2.TypeError(f"rw produced {pretty(expected)}, but goal is {pretty(goal)}")
    return SuccCongr(proof)


def after_register_declaration(tc: TypeChecker, declaration) -> None:
    if declaration.name in {"add_zero", "add_succ"}:
        tc.add_reducer("add", nat_add_reducer)
