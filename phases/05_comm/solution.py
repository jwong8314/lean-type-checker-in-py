"""Phase 5 solution: check the raw MyNat commutativity script."""

from __future__ import annotations

import importlib.util
import sys
from dataclasses import dataclass
from pathlib import Path

from expressions import Type


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

MyNat = p2.Const("MyNat")
zero = p2.Const("zero")
succ = p2.Const("succ")
add = p2.Const("add")
my_add_zero = p2.Const("my_add_zero")
my_add_succ = p2.Const("my_add_succ")
zero_add = p2.Const("zero_add")
succ_add = p2.Const("succ_add")
succ_add_succ = p2.Const("succ_add_succ")
add_assoc = p2.Const("add_assoc")
add_comm = p2.Const("add_comm")
add_right_comm = p2.Const("add_right_comm")


@dataclass(frozen=True)
class EqSymm(p2.Expr):
    proof: p2.Expr


@dataclass(frozen=True)
class EqTrans(p2.Expr):
    left: p2.Expr
    right: p2.Expr


@dataclass(frozen=True)
class EqCongrAddLeft(p2.Expr):
    left_arg: p2.Expr
    proof: p2.Expr


class TypeChecker(p4.TypeChecker):
    def infer(self, expr: p2.Expr, ctx: dict[str, p2.Expr] | None = None) -> p2.Expr:
        ctx = {} if ctx is None else ctx
        match expr:
            case p2.App(fn, arg):
                fn_ty = self.infer(fn, ctx)
                if not isinstance(fn_ty, p2.Pi):
                    raise p2.TypeError(f"expected function type, got {pretty(fn_ty)}")
                self.check(arg, fn_ty.domain, ctx)
                return subst(fn_ty.body, fn_ty.var, arg)
            case p3.Rw(proof):
                proof_ty = self.whnf(self.infer(proof, ctx))
                if not isinstance(proof_ty, p3.Eq):
                    raise p2.TypeError("rw expected an equality proof")
                self.check(proof_ty.ty, Type, ctx)
                if not self.defeq(proof_ty.ty, MyNat):
                    raise p2.TypeError("phase 5 rw only handles MyNat equalities")
                return p3.Eq(MyNat, p2.apps(succ, proof_ty.lhs), p2.apps(succ, proof_ty.rhs))
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
            case EqCongrAddLeft(left_arg, proof):
                self.check(left_arg, MyNat, ctx)
                proof_ty = self.whnf(self.infer(proof, ctx))
                if not isinstance(proof_ty, p3.Eq) or not self.defeq(proof_ty.ty, MyNat):
                    raise p2.TypeError("add-left congruence expected a MyNat equality")
                lhs = p2.apps(add, left_arg, proof_ty.lhs)
                rhs = p2.apps(add, left_arg, proof_ty.rhs)
                return p3.Eq(MyNat, lhs, rhs)
            case _:
                return super().infer(expr, ctx)

    def normalize(self, expr: p2.Expr) -> p2.Expr:
        expr = self.whnf(expr)
        match expr:
            case EqSymm(proof):
                return EqSymm(self.normalize(proof))
            case EqTrans(left, right):
                return EqTrans(self.normalize(left), self.normalize(right))
            case EqCongrAddLeft(left_arg, proof):
                return EqCongrAddLeft(self.normalize(left_arg), self.normalize(proof))
            case _:
                return super().normalize(expr)

    def pretty(self, expr: p2.Expr) -> str:
        return pretty(expr)


def mynat_type_spec() -> p2.RecursiveTypeSpec:
    return p2.RecursiveTypeSpec(
        "MyNat",
        Type,
        (
            p2.ConstructorSpec("zero", ()),
            p2.ConstructorSpec("succ", (MyNat,)),
        ),
    )


def theorem_app(theorem: p2.Expr, *args: p2.Expr) -> p2.Expr:
    return p2.apps(theorem, *args)


def free_vars(expr: p2.Expr) -> set[str]:
    match expr:
        case p2.Sort() | p2.Const():
            return set()
        case p2.Var(name):
            return {name}
        case p2.App(fn, arg):
            return free_vars(fn) | free_vars(arg)
        case p2.Pi(var, domain, body):
            return free_vars(domain) | (free_vars(body) - {var})
        case p3.Lam(var, domain, body):
            return free_vars(domain) | (free_vars(body) - {var})
        case p3.Eq(ty, lhs, rhs):
            return free_vars(ty) | free_vars(lhs) | free_vars(rhs)
        case p3.Refl(ty, value):
            return free_vars(ty) | free_vars(value)
        case p3.Rw(proof):
            return free_vars(proof)
        case p4.Induction(_, motive, cases, target):
            result = free_vars(motive) | free_vars(target)
            for case in cases:
                result |= free_vars(case)
            return result
        case EqSymm(proof):
            return free_vars(proof)
        case EqTrans(left, right):
            return free_vars(left) | free_vars(right)
        case EqCongrAddLeft(left_arg, proof):
            return free_vars(left_arg) | free_vars(proof)
        case _:
            raise p2.TypeError(f"cannot collect free variables in {expr!r}")


def fresh_name(base: str, blocked: set[str]) -> str:
    candidate = f"{base}'"
    while candidate in blocked:
        candidate += "'"
    return candidate


def subst(expr: p2.Expr, var: str, replacement: p2.Expr) -> p2.Expr:
    """Capture-avoiding substitution for the syntax used in this phase."""

    match expr:
        case p2.Sort() | p2.Const():
            return expr
        case p2.Var(name):
            return replacement if name == var else expr
        case p2.App(fn, arg):
            return p2.App(subst(fn, var, replacement), subst(arg, var, replacement))
        case p2.Pi(bound, domain, body):
            domain = subst(domain, var, replacement)
            if bound == var:
                return p2.Pi(bound, domain, body)
            if bound in free_vars(replacement):
                fresh = fresh_name(bound, free_vars(body) | free_vars(replacement) | {var})
                body = subst(body, bound, p2.Var(fresh))
                bound = fresh
            return p2.Pi(bound, domain, subst(body, var, replacement))
        case p3.Lam(bound, domain, body):
            domain = subst(domain, var, replacement)
            if bound == var:
                return p3.Lam(bound, domain, body)
            if bound in free_vars(replacement):
                fresh = fresh_name(bound, free_vars(body) | free_vars(replacement) | {var})
                body = subst(body, bound, p2.Var(fresh))
                bound = fresh
            return p3.Lam(bound, domain, subst(body, var, replacement))
        case p3.Eq(ty, lhs, rhs):
            return p3.Eq(subst(ty, var, replacement), subst(lhs, var, replacement), subst(rhs, var, replacement))
        case p3.Refl(ty, value):
            return p3.Refl(subst(ty, var, replacement), subst(value, var, replacement))
        case p3.Rw(proof):
            return p3.Rw(subst(proof, var, replacement))
        case p4.Induction(type_name, motive, cases, target):
            return p4.Induction(
                type_name,
                subst(motive, var, replacement),
                tuple(subst(case, var, replacement) for case in cases),
                subst(target, var, replacement),
            )
        case EqSymm(proof):
            return EqSymm(subst(proof, var, replacement))
        case EqTrans(left, right):
            return EqTrans(subst(left, var, replacement), subst(right, var, replacement))
        case EqCongrAddLeft(left_arg, proof):
            return EqCongrAddLeft(subst(left_arg, var, replacement), subst(proof, var, replacement))
        case _:
            raise p2.TypeError(f"cannot substitute in {expr!r}")


def mynat_case() -> tuple[p2.Expr, p2.Expr]:
    return MyNat, Type


def zero_case() -> tuple[p2.Expr, p2.Expr]:
    return zero, MyNat


def succ_case() -> tuple[p2.Expr, p2.Expr]:
    return succ, p2.arrow(MyNat, MyNat)


def add_type() -> p2.Expr:
    return p2.arrow(MyNat, p2.arrow(MyNat, MyNat))


def add_case() -> tuple[p2.Expr, p2.Expr]:
    return add, add_type()


def after_register_declaration(tc: TypeChecker, declaration) -> None:
    if declaration.name == "add":
        tc.add_reducer("add", p3.nat_add_reducer)


def my_add_zero_type() -> p2.Expr:
    a = p2.Var("a")
    return p2.Pi("a", MyNat, p3.Eq(MyNat, p2.apps(add, a, zero), a))


def my_add_zero_case() -> tuple[p2.Expr, p2.Expr]:
    a = p2.Var("a")
    return p3.Lam("a", MyNat, p3.Refl(MyNat, a)), my_add_zero_type()


def my_add_succ_type() -> p2.Expr:
    a = p2.Var("a")
    b = p2.Var("b")
    lhs = p2.apps(add, a, p2.apps(succ, b))
    rhs = p2.apps(succ, p2.apps(add, a, b))
    return p2.Pi("a", MyNat, p2.Pi("b", MyNat, p3.Eq(MyNat, lhs, rhs)))


def my_add_succ_case() -> tuple[p2.Expr, p2.Expr]:
    a = p2.Var("a")
    b = p2.Var("b")
    value = p2.apps(succ, p2.apps(add, a, b))
    proof = p3.Lam("a", MyNat, p3.Lam("b", MyNat, p3.Refl(MyNat, value)))
    return proof, my_add_succ_type()


def succ_add_type() -> p2.Expr:
    a = p2.Var("a")
    b = p2.Var("b")
    lhs = p2.apps(add, p2.apps(succ, a), b)
    rhs = p2.apps(succ, p2.apps(add, a, b))
    return p2.Pi("a", MyNat, p2.Pi("b", MyNat, p3.Eq(MyNat, lhs, rhs)))


def succ_add_case() -> tuple[p2.Expr, p2.Expr]:
    a = p2.Var("a")
    n = p2.Var("n")
    ih = p2.Var("ih")

    def motive_at(x: p2.Expr) -> p2.Expr:
        return p3.Eq(
            MyNat,
            p2.apps(add, p2.apps(succ, a), x),
            p2.apps(succ, p2.apps(add, a, x)),
        )

    motive = p3.Lam("b", MyNat, motive_at(p2.Var("b")))
    base = p3.Refl(MyNat, p2.apps(succ, a))
    step = p3.Lam("n", MyNat, p3.Lam("ih", motive_at(n), theorem_app(succ_add_succ, a, n, ih)))
    body = p4.Induction("MyNat", motive, (base, step), p2.Var("b"))
    return p3.Lam("a", MyNat, p3.Lam("b", MyNat, body)), succ_add_type()


def succ_add_succ_type() -> p2.Expr:
    a = p2.Var("a")
    b = p2.Var("b")
    ih = p3.Eq(MyNat, p2.apps(add, p2.apps(succ, a), b), p2.apps(succ, p2.apps(add, a, b)))
    lhs = p2.apps(add, p2.apps(succ, a), p2.apps(succ, b))
    rhs = p2.apps(succ, p2.apps(succ, p2.apps(add, a, b)))
    return p2.Pi("a", MyNat, p2.Pi("b", MyNat, p2.Pi("ih", ih, p3.Eq(MyNat, lhs, rhs))))


def succ_add_succ_case() -> tuple[p2.Expr, p2.Expr]:
    a = p2.Var("a")
    b = p2.Var("b")
    ih = p2.Var("ih")
    ih_type = p3.Eq(MyNat, p2.apps(add, p2.apps(succ, a), b), p2.apps(succ, p2.apps(add, a, b)))
    proof = p3.Lam("a", MyNat, p3.Lam("b", MyNat, p3.Lam("ih", ih_type, p3.Rw(ih))))
    return proof, succ_add_succ_type()


def zero_add_type() -> p2.Expr:
    a = p2.Var("a")
    return p2.Pi("a", MyNat, p3.Eq(MyNat, p2.apps(add, zero, a), a))


def zero_add_case() -> tuple[p2.Expr, p2.Expr]:
    a = p2.Var("a")
    n = p2.Var("n")
    ih = p2.Var("ih")

    def motive_at(x: p2.Expr) -> p2.Expr:
        return p3.Eq(MyNat, p2.apps(add, zero, x), x)

    motive = p3.Lam("a", MyNat, motive_at(p2.Var("a")))
    base = p3.Refl(MyNat, zero)
    step = p3.Lam("n", MyNat, p3.Lam("ih", motive_at(n), p3.Rw(ih)))
    proof = p3.Lam("a", MyNat, p4.Induction("MyNat", motive, (base, step), a))
    return proof, zero_add_type()


def add_comm_type() -> p2.Expr:
    a = p2.Var("a")
    b = p2.Var("b")
    return p2.Pi("a", MyNat, p2.Pi("b", MyNat, p3.Eq(MyNat, p2.apps(add, a, b), p2.apps(add, b, a))))


def add_comm_case() -> tuple[p2.Expr, p2.Expr]:
    a = p2.Var("a")
    b = p2.Var("b")
    n = p2.Var("n")
    ih = p2.Var("ih")

    def motive_at(x: p2.Expr) -> p2.Expr:
        return p3.Eq(MyNat, p2.apps(add, a, x), p2.apps(add, x, a))

    motive = p3.Lam("b", MyNat, motive_at(p2.Var("b")))
    base = EqSymm(theorem_app(zero_add, a))
    step_left = p3.Rw(ih)
    step_right = EqSymm(theorem_app(succ_add, n, a))
    step = p3.Lam("n", MyNat, p3.Lam("ih", motive_at(n), EqTrans(step_left, step_right)))
    body = p4.Induction("MyNat", motive, (base, step), b)
    proof = p3.Lam("a", MyNat, p3.Lam("b", MyNat, body))
    return proof, add_comm_type()


def add_assoc_type() -> p2.Expr:
    a = p2.Var("a")
    b = p2.Var("b")
    c = p2.Var("c")
    lhs = p2.apps(add, p2.apps(add, a, b), c)
    rhs = p2.apps(add, a, p2.apps(add, b, c))
    return p2.Pi("a", MyNat, p2.Pi("b", MyNat, p2.Pi("c", MyNat, p3.Eq(MyNat, lhs, rhs))))


def add_assoc_case() -> tuple[p2.Expr, p2.Expr]:
    a = p2.Var("a")
    b = p2.Var("b")
    c = p2.Var("c")
    n = p2.Var("n")
    ih = p2.Var("ih")

    def motive_at(x: p2.Expr) -> p2.Expr:
        return p3.Eq(
            MyNat,
            p2.apps(add, p2.apps(add, a, b), x),
            p2.apps(add, a, p2.apps(add, b, x)),
        )

    motive = p3.Lam("c", MyNat, motive_at(p2.Var("c")))
    base = p3.Refl(MyNat, p2.apps(add, a, b))
    step = p3.Lam("n", MyNat, p3.Lam("ih", motive_at(n), p3.Rw(ih)))
    body = p4.Induction("MyNat", motive, (base, step), c)
    proof = p3.Lam("a", MyNat, p3.Lam("b", MyNat, p3.Lam("c", MyNat, body)))
    return proof, add_assoc_type()


def add_right_comm_type() -> p2.Expr:
    a = p2.Var("a")
    b = p2.Var("b")
    c = p2.Var("c")
    lhs = p2.apps(add, p2.apps(add, a, b), c)
    rhs = p2.apps(add, p2.apps(add, a, c), b)
    return p2.Pi("a", MyNat, p2.Pi("b", MyNat, p2.Pi("c", MyNat, p3.Eq(MyNat, lhs, rhs))))


def add_right_comm_case() -> tuple[p2.Expr, p2.Expr]:
    a = p2.Var("a")
    b = p2.Var("b")
    c = p2.Var("c")
    p1 = theorem_app(add_assoc, a, b, c)
    p2_ = EqCongrAddLeft(a, theorem_app(add_comm, b, c))
    p3_ = EqSymm(theorem_app(add_assoc, a, c, b))
    proof = p3.Lam("a", MyNat, p3.Lam("b", MyNat, p3.Lam("c", MyNat, EqTrans(EqTrans(p1, p2_), p3_))))
    return proof, add_right_comm_type()


def pretty(expr: p2.Expr) -> str:
    match expr:
        case EqSymm(proof):
            return f"symm ({pretty(proof)})"
        case EqTrans(left, right):
            return f"trans ({pretty(left)}) ({pretty(right)})"
        case EqCongrAddLeft(left_arg, proof):
            return f"congr_add_left {p3.atom(left_arg)} ({pretty(proof)})"
        case p2.App(_, _):
            head, args = p2.spine(expr)
            if isinstance(head, p2.Const) and head.name == "succ" and len(args) == 1:
                return f"succ {p3.atom(args[0])}"
            if isinstance(head, p2.Const) and head.name == "add" and len(args) == 2:
                return f"{p3.atom(args[0])} + {p3.atom(args[1])}"
            return p4.pretty(expr)
        case _:
            return p4.pretty(expr)
