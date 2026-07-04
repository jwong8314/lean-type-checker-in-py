"""Chapter 5 solution: disjunctions, `cases`, and contradiction."""

from __future__ import annotations

from .expressions import FalseElim, FalseProp, Or, OrCases, OrInl, OrInr, p2, p3, p4


for _name in dir(p4):
    if not _name.startswith("_") and _name not in globals():
        globals()[_name] = getattr(p4, _name)


class TypeChecker(p4.TypeChecker):
    def infer(self, expr: p2.Expr, ctx: dict[str, p2.Expr] | None = None) -> p2.Expr:
        ctx = {} if ctx is None else ctx
        match expr:
            case Or(left, right):
                self.check(left, p2.Prop, ctx)
                self.check(right, p2.Prop, ctx)
                return p2.Prop
            case OrInl(left, right, proof):
                self.check(left, p2.Prop, ctx)
                self.check(right, p2.Prop, ctx)
                self.check(proof, left, ctx)
                return Or(left, right)
            case OrInr(left, right, proof):
                self.check(left, p2.Prop, ctx)
                self.check(right, p2.Prop, ctx)
                self.check(proof, right, ctx)
                return Or(left, right)
            case OrCases(target, left_case, right_case):
                target_ty = self.whnf(self.infer(target, ctx))
                if not isinstance(target_ty, Or):
                    raise p2.TypeError("cases expected a disjunction proof")
                left_case_ty = self.whnf(self.infer(left_case, ctx))
                right_case_ty = self.whnf(self.infer(right_case, ctx))
                if not isinstance(left_case_ty, p2.Pi) or not self.defeq(left_case_ty.domain, target_ty.left):
                    raise p2.TypeError("left case has the wrong type")
                if not isinstance(right_case_ty, p2.Pi) or not self.defeq(right_case_ty.domain, target_ty.right):
                    raise p2.TypeError("right case has the wrong type")
                if not self.defeq(left_case_ty.body, right_case_ty.body):
                    raise p2.TypeError("cases branches produce different goals")
                return left_case_ty.body
            case FalseElim(goal, proof):
                self.check(goal, p2.Prop, ctx)
                self.check(proof, FalseProp, ctx)
                return goal
            case _:
                return super().infer(expr, ctx)

    def normalize(self, expr: p2.Expr) -> p2.Expr:
        expr = self.whnf(expr)
        match expr:
            case Or(left, right):
                return Or(self.normalize(left), self.normalize(right))
            case OrInl(left, right, proof):
                return OrInl(self.normalize(left), self.normalize(right), self.normalize(proof))
            case OrInr(left, right, proof):
                return OrInr(self.normalize(left), self.normalize(right), self.normalize(proof))
            case OrCases(target, left_case, right_case):
                return OrCases(self.normalize(target), self.normalize(left_case), self.normalize(right_case))
            case FalseElim(goal, proof):
                return FalseElim(self.normalize(goal), self.normalize(proof))
            case _:
                return super().normalize(expr)

    def defeq(self, left: p2.Expr, right: p2.Expr) -> bool:
        return self.normalize(left) == self.normalize(right)

    def pretty(self, expr: p2.Expr) -> str:
        return pretty(expr)


def subst(expr: p2.Expr, var: str, replacement: p2.Expr) -> p2.Expr:
    match expr:
        case Or(left, right):
            return Or(subst(left, var, replacement), subst(right, var, replacement))
        case OrInl(left, right, proof):
            return OrInl(subst(left, var, replacement), subst(right, var, replacement), subst(proof, var, replacement))
        case OrInr(left, right, proof):
            return OrInr(subst(left, var, replacement), subst(right, var, replacement), subst(proof, var, replacement))
        case OrCases(target, left_case, right_case):
            return OrCases(subst(target, var, replacement), subst(left_case, var, replacement), subst(right_case, var, replacement))
        case FalseElim(goal, proof):
            return FalseElim(subst(goal, var, replacement), subst(proof, var, replacement))
        case _:
            return p3.subst(expr, var, replacement)


def pretty(expr: p2.Expr) -> str:
    match expr:
        case p2.Pi("_", domain, body):
            return f"{atom(domain)} -> {pretty(body)}"
        case p2.Pi(var, domain, body):
            return f"forall ({var} : {pretty(domain)}), {pretty(body)}"
        case Or(left, right):
            return f"{atom(left)} or {atom(right)}"
        case OrInl(left, right, proof):
            return f"or_inl {atom(left)} {atom(right)} {atom(proof)}"
        case OrInr(left, right, proof):
            return f"or_inr {atom(left)} {atom(right)} {atom(proof)}"
        case OrCases(target, left_case, right_case):
            return f"cases {atom(target)} {atom(left_case)} {atom(right_case)}"
        case FalseElim(goal, proof):
            return f"false_elim {atom(goal)} {atom(proof)}"
        case _:
            return p4.pretty(expr)


def atom(expr: p2.Expr) -> str:
    if isinstance(expr, (p2.Sort, p2.Const, p2.Var)):
        return pretty(expr)
    return f"({pretty(expr)})"
