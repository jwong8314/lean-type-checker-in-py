"""Phase 5 solution: use induction results to prove commutativity."""

from __future__ import annotations

import importlib.util
import sys
from dataclasses import dataclass
from pathlib import Path


def load_phase4():
    path = Path(__file__).resolve().parents[1] / "04_induction/solution.py"
    spec = importlib.util.spec_from_file_location("phase4_solution", path)
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


p4 = load_phase4()
p3 = p4.p3
p2 = p4.p2

zero_add = p2.Const("zero_add")
succ_add = p2.Const("succ_add")
succ_add_succ = p2.Const("succ_add_succ")
add_assoc = p2.Const("add_assoc")
add_comm = p2.Const("add_comm")


@dataclass(frozen=True)
class EqSymm(p2.Expr):
    proof: p2.Expr


@dataclass(frozen=True)
class EqTrans(p2.Expr):
    left: p2.Expr
    right: p2.Expr


class TypeChecker(p4.TypeChecker):
    def infer(self, expr: p2.Expr, ctx: dict[str, p2.Expr] | None = None) -> p2.Expr:
        ctx = {} if ctx is None else ctx
        match expr:
            case p2.App(fn, arg):
                fn_ty = self.infer(fn, ctx)
                if not isinstance(fn_ty, p2.Pi):
                    raise p2.TypeError(f"expected function type, got {pretty(fn_ty)}")
                self.check(arg, fn_ty.domain, ctx)
                return p3.subst(fn_ty.body, fn_ty.var, arg)
            case EqSymm(proof):
                proof_ty = self.whnf(self.infer(proof, ctx))
                if not isinstance(proof_ty, p3.Eq):
                    raise p2.TypeError("symm expected an equality proof")
                return p3.Eq(proof_ty.ty, proof_ty.rhs, proof_ty.lhs)
            case EqTrans(left, right):
                left_ty = self.whnf(self.infer(left, ctx))
                right_ty = self.whnf(self.infer(right, ctx))
                if not isinstance(left_ty, p3.Eq) or not isinstance(right_ty, p3.Eq):
                    raise p2.TypeError("trans expected equality proofs")
                if not self.defeq(left_ty.ty, right_ty.ty):
                    raise p2.TypeError("trans equalities are over different types")
                if not self.defeq(left_ty.rhs, right_ty.lhs):
                    raise p2.TypeError(
                        f"trans midpoint mismatch: {p3.pretty(left_ty.rhs)} and {p3.pretty(right_ty.lhs)}"
                    )
                return p3.Eq(left_ty.ty, left_ty.lhs, right_ty.rhs)
            case _:
                return super().infer(expr, ctx)

    def normalize(self, expr: p2.Expr) -> p2.Expr:
        expr = self.whnf(expr)
        match expr:
            case EqSymm(proof):
                return EqSymm(self.normalize(proof))
            case EqTrans(left, right):
                return EqTrans(self.normalize(left), self.normalize(right))
            case _:
                return super().normalize(expr)


def phase5_checker() -> TypeChecker:
    tc = TypeChecker()
    tc.add_recursive_type(p2.nat_type_spec())
    tc.add("add", p2.arrow(p2.Nat, p2.arrow(p2.Nat, p2.Nat)))
    tc.add_reducer("add", p3.nat_add_reducer)
    tc.add("succ_add", p4.theorem_type())
    return tc


def fresh_checker() -> TypeChecker:
    return phase5_checker()


def register_declaration(tc: TypeChecker, name: str) -> None:
    if name == "zero_add":
        tc.add("zero_add", zero_add_type())
    elif name == "succ_add_succ":
        tc.add("succ_add_succ", succ_add_succ_type())
    elif name == "add_assoc":
        tc.add("add_assoc", add_assoc_type())
    elif name == "add_comm":
        tc.add("add_comm", add_comm_type())


def theorem_app(theorem: p2.Expr, *args: p2.Expr) -> p2.Expr:
    return p2.apps(theorem, *args)


def zero_add_type() -> p2.Expr:
    a = p2.Var("a")
    return p2.Pi("a", p2.Nat, p3.Eq(p2.Nat, p2.apps(p3.add, p2.zero, a), a))


def zero_add_case() -> tuple[p2.Expr, p2.Expr]:
    a = p2.Var("a")
    n = p2.Var("n")
    ih = p2.Var("ih")

    def motive_at(x: p2.Expr) -> p2.Expr:
        return p3.Eq(p2.Nat, p2.apps(p3.add, p2.zero, x), x)

    motive = p3.Lam("a", p2.Nat, motive_at(p2.Var("a")))
    base = p3.Refl(p2.Nat, p2.zero)
    step = p3.Lam("n", p2.Nat, p3.Lam("ih", motive_at(n), p3.Rw(ih)))
    proof = p3.Lam("a", p2.Nat, p4.Induction("Nat", motive, (base, step), a))
    return proof, zero_add_type()


def succ_add_succ_type() -> p2.Expr:
    a = p2.Var("a")
    b = p2.Var("b")
    lhs = p2.apps(p3.add, p2.apps(p2.succ, a), p2.apps(p2.succ, b))
    rhs = p2.apps(p2.succ, p2.apps(p2.succ, p2.apps(p3.add, a, b)))
    return p2.Pi("a", p2.Nat, p2.Pi("b", p2.Nat, p3.Eq(p2.Nat, lhs, rhs)))


def succ_add_succ_case() -> tuple[p2.Expr, p2.Expr]:
    a = p2.Var("a")
    b = p2.Var("b")
    proof = p3.Lam("a", p2.Nat, p3.Lam("b", p2.Nat, p3.Rw(theorem_app(succ_add, a, b))))
    return proof, succ_add_succ_type()


def add_assoc_type() -> p2.Expr:
    a = p2.Var("a")
    b = p2.Var("b")
    c = p2.Var("c")
    lhs = p2.apps(p3.add, p2.apps(p3.add, a, b), c)
    rhs = p2.apps(p3.add, a, p2.apps(p3.add, b, c))
    return p2.Pi("a", p2.Nat, p2.Pi("b", p2.Nat, p2.Pi("c", p2.Nat, p3.Eq(p2.Nat, lhs, rhs))))


def add_assoc_case() -> tuple[p2.Expr, p2.Expr]:
    a = p2.Var("a")
    b = p2.Var("b")
    c = p2.Var("c")
    n = p2.Var("n")
    ih = p2.Var("ih")

    def motive_at(x: p2.Expr) -> p2.Expr:
        return p3.Eq(
            p2.Nat,
            p2.apps(p3.add, p2.apps(p3.add, a, b), x),
            p2.apps(p3.add, a, p2.apps(p3.add, b, x)),
        )

    motive = p3.Lam("c", p2.Nat, motive_at(p2.Var("c")))
    base = p3.Refl(p2.Nat, p2.apps(p3.add, a, b))
    step = p3.Lam("n", p2.Nat, p3.Lam("ih", motive_at(n), p3.Rw(ih)))
    body = p4.Induction("Nat", motive, (base, step), c)
    proof = p3.Lam("a", p2.Nat, p3.Lam("b", p2.Nat, p3.Lam("c", p2.Nat, body)))
    return proof, add_assoc_type()


def add_comm_type() -> p2.Expr:
    a = p2.Var("a")
    b = p2.Var("b")
    return p2.Pi("a", p2.Nat, p2.Pi("b", p2.Nat, p3.Eq(p2.Nat, p2.apps(p3.add, a, b), p2.apps(p3.add, b, a))))


def add_comm_case() -> tuple[p2.Expr, p2.Expr]:
    a = p2.Var("a")
    b = p2.Var("b")
    n = p2.Var("n")
    ih = p2.Var("ih")

    def motive_at(x: p2.Expr) -> p2.Expr:
        return p3.Eq(p2.Nat, p2.apps(p3.add, a, x), p2.apps(p3.add, x, a))

    motive = p3.Lam("b", p2.Nat, motive_at(p2.Var("b")))
    base = EqSymm(theorem_app(zero_add, a))
    step_left = p3.Rw(ih)
    step_right = EqSymm(theorem_app(succ_add, n, a))
    step = p3.Lam("n", p2.Nat, p3.Lam("ih", motive_at(n), EqTrans(step_left, step_right)))
    body = p4.Induction("Nat", motive, (base, step), b)
    proof = p3.Lam("a", p2.Nat, p3.Lam("b", p2.Nat, body))
    return proof, add_comm_type()


def pretty(expr: p2.Expr) -> str:
    match expr:
        case EqSymm(proof):
            return f"symm ({pretty(proof)})"
        case EqTrans(left, right):
            return f"trans ({pretty(left)}) ({pretty(right)})"
        case _:
            return p4.pretty(expr)


DEFAULT_CHECKER = phase5_checker()
for _name in ("zero_add", "succ_add_succ", "add_assoc", "add_comm"):
    register_declaration(DEFAULT_CHECKER, _name)


def infer(expr: p2.Expr, ctx: dict[str, p2.Expr] | None = None, tc: TypeChecker | None = None) -> p2.Expr:
    tc = DEFAULT_CHECKER if tc is None else tc
    return tc.infer(expr, ctx)


def check(expr: p2.Expr, expected: p2.Expr, ctx: dict[str, p2.Expr] | None = None, tc: TypeChecker | None = None) -> None:
    tc = DEFAULT_CHECKER if tc is None else tc
    tc.check(expr, expected, ctx)
