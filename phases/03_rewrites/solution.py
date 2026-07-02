"""Phase 3 solution: equality, rfl, computation, and a tiny rewrite."""

from __future__ import annotations

import importlib.util
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Callable


def load_phase2():
    path = Path(__file__).resolve().parents[1] / "02_recursive_nat/solution.py"
    spec = importlib.util.spec_from_file_location("phase2_solution", path)
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


p2 = load_phase2()


@dataclass(frozen=True)
class Lam(p2.Expr):
    var: str
    domain: p2.Expr
    body: p2.Expr


@dataclass(frozen=True)
class Eq(p2.Expr):
    ty: p2.Expr
    lhs: p2.Expr
    rhs: p2.Expr


@dataclass(frozen=True)
class Refl(p2.Expr):
    ty: p2.Expr
    value: p2.Expr


@dataclass(frozen=True)
class CongSucc(p2.Expr):
    proof: p2.Expr


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
            case CongSucc(proof):
                proof_ty = self.whnf(self.infer(proof, ctx))
                if not isinstance(proof_ty, Eq):
                    raise p2.TypeError("congr_succ expected an equality proof")
                self.check(proof_ty.ty, p2.Type, ctx)
                if not self.defeq(proof_ty.ty, p2.Nat):
                    raise p2.TypeError("congr_succ only handles Nat equalities in this tutorial")
                return Eq(p2.Nat, p2.apps(p2.succ, proof_ty.lhs), p2.apps(p2.succ, proof_ty.rhs))
            case _:
                return super().infer(expr, ctx)

    def check(self, expr: p2.Expr, expected: p2.Expr, ctx: dict[str, p2.Expr] | None = None) -> None:
        actual = self.infer(expr, ctx)
        if not self.defeq(actual, expected):
            raise p2.TypeError(f"expected {pretty(expected)}, got {pretty(actual)}")

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
            case CongSucc(proof):
                return CongSucc(self.normalize(proof))
            case _:
                return expr

    def defeq(self, left: p2.Expr, right: p2.Expr) -> bool:
        return alpha_equal(self.normalize(left), self.normalize(right))

    def try_reduce(self, expr: p2.Expr) -> p2.Expr | None:
        head, _ = p2.spine(expr)
        if isinstance(head, p2.Const) and head.name in self.reducers:
            return self.reducers[head.name](self, expr)
        return None


add = p2.Const("add")
EqConst = p2.Const("Eq")
add_zero = p2.Const("add_zero")
add_succ = p2.Const("add_succ")


def subst(expr: p2.Expr, var: str, replacement: p2.Expr) -> p2.Expr:
    match expr:
        case p2.Sort() | p2.Const():
            return expr
        case p2.Var(name):
            return replacement if name == var else expr
        case p2.App(fn, arg):
            return p2.App(subst(fn, var, replacement), subst(arg, var, replacement))
        case p2.Pi(bound, domain, body):
            if bound == var:
                return p2.Pi(bound, subst(domain, var, replacement), body)
            return p2.Pi(bound, subst(domain, var, replacement), subst(body, var, replacement))
        case Lam(bound, domain, body):
            if bound == var:
                return Lam(bound, subst(domain, var, replacement), body)
            return Lam(bound, subst(domain, var, replacement), subst(body, var, replacement))
        case Eq(ty, lhs, rhs):
            return Eq(subst(ty, var, replacement), subst(lhs, var, replacement), subst(rhs, var, replacement))
        case Refl(ty, value):
            return Refl(subst(ty, var, replacement), subst(value, var, replacement))
        case CongSucc(proof):
            return CongSucc(subst(proof, var, replacement))
        case _:
            raise p2.TypeError(f"cannot substitute in {expr!r}")


def alpha_equal(left: p2.Expr, right: p2.Expr, env: dict[str, str] | None = None) -> bool:
    env = {} if env is None else env
    match left, right:
        case p2.Sort(l1), p2.Sort(l2):
            return l1 == l2
        case p2.Const(n1), p2.Const(n2):
            return n1 == n2
        case p2.Var(n1), p2.Var(n2):
            return env.get(n1, n1) == n2
        case p2.App(f1, a1), p2.App(f2, a2):
            return alpha_equal(f1, f2, env) and alpha_equal(a1, a2, env)
        case p2.Pi(v1, d1, b1), p2.Pi(v2, d2, b2):
            return alpha_equal(d1, d2, env) and alpha_equal(b1, b2, env | {v1: v2})
        case Lam(v1, d1, b1), Lam(v2, d2, b2):
            return alpha_equal(d1, d2, env) and alpha_equal(b1, b2, env | {v1: v2})
        case Eq(t1, l1, r1), Eq(t2, l2, r2):
            return alpha_equal(t1, t2, env) and alpha_equal(l1, l2, env) and alpha_equal(r1, r2, env)
        case Refl(t1, v1), Refl(t2, v2):
            return alpha_equal(t1, t2, env) and alpha_equal(v1, v2, env)
        case CongSucc(p1), CongSucc(p2_):
            return alpha_equal(p1, p2_, env)
        case _:
            return False


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


def register_declaration(tc: TypeChecker, name: str) -> None:
    """Update the checker environment when script.lean reaches a declaration."""

    if name == "Eq":
        tc.add("Eq", eq_decl_case()[1])
    elif name == "rfl_nat":
        tc.add("rfl_nat", rfl_nat_type())
    elif name == "add":
        tc.add("add", add_decl_case()[1])
    elif name == "add_zero":
        tc.add("add_zero", add_zero_type())
        tc.add_reducer("add", nat_add_reducer)
    elif name == "add_succ":
        tc.add("add_succ", add_succ_type())
        tc.add_reducer("add", nat_add_reducer)
    elif name == "congr_succ":
        tc.add("congr_succ", congr_succ_type())
    elif name in {"add_zero_by_rfl", "add_succ_by_rfl", "rewrite_step"}:
        # Theorems do not add new computation behavior in this toy kernel.
        if name == "add_zero_by_rfl":
            tc.add(name, add_zero_by_rfl_case()[1])
        elif name == "add_succ_by_rfl":
            tc.add(name, add_succ_by_rfl_case()[1])
        elif name == "rewrite_step":
            tc.add(name, rewrite_step_case()[1])


def phase3_checker() -> TypeChecker:
    tc = TypeChecker()
    tc.add_recursive_type(p2.nat_type_spec())
    return tc


def fresh_checker() -> TypeChecker:
    return phase3_checker()


def pretty(expr: p2.Expr) -> str:
    match expr:
        case Eq(_, lhs, rhs):
            return f"{pretty(lhs)} = {pretty(rhs)}"
        case Refl(ty, value):
            return f"rfl@{pretty(ty)} {atom(value)}"
        case CongSucc(proof):
            return f"congr_succ {atom(proof)}"
        case Lam(var, domain, body):
            return f"fun ({var} : {pretty(domain)}) => {pretty(body)}"
        case p2.Pi("_", domain, body):
            return f"{atom(domain)} -> {pretty(body)}"
        case p2.Pi(var, domain, body):
            return f"forall ({var} : {pretty(domain)}), {pretty(body)}"
        case p2.App(_, _):
            head, args = p2.spine(expr)
            if isinstance(head, p2.Const) and head.name == "succ" and len(args) == 1:
                return f"succ {atom(args[0])}"
            if isinstance(head, p2.Const) and head.name == "add" and len(args) == 2:
                return f"{atom(args[0])} + {atom(args[1])}"
            return p2.pretty(expr)
        case _:
            return p2.pretty(expr)


def atom(expr: p2.Expr) -> str:
    if isinstance(expr, (p2.Sort, p2.Const, p2.Var)):
        return pretty(expr)
    return f"({pretty(expr)})"


def eq_decl_case() -> tuple[p2.Expr, p2.Expr]:
    return EqConst, p2.arrow(p2.Type, p2.arrow(p2.Nat, p2.arrow(p2.Nat, p2.Prop)))


def rfl_nat_type() -> p2.Expr:
    x = p2.Var("x")
    return p2.Pi("x", p2.Nat, Eq(p2.Nat, x, x))


def rfl_nat_case() -> tuple[p2.Expr, p2.Expr]:
    x = p2.Var("x")
    return Lam("x", p2.Nat, Refl(p2.Nat, x)), rfl_nat_type()


def add_decl_case() -> tuple[p2.Expr, p2.Expr]:
    return add, p2.arrow(p2.Nat, p2.arrow(p2.Nat, p2.Nat))


def add_zero_type() -> p2.Expr:
    a = p2.Var("a")
    return p2.Pi("a", p2.Nat, Eq(p2.Nat, p2.apps(add, a, p2.zero), a))


def add_zero_case() -> tuple[p2.Expr, p2.Expr]:
    return add_zero, add_zero_type()


def add_succ_type() -> p2.Expr:
    a = p2.Var("a")
    b = p2.Var("b")
    return p2.Pi("a", p2.Nat, p2.Pi("b", p2.Nat, Eq(p2.Nat, p2.apps(add, a, p2.apps(p2.succ, b)), p2.apps(p2.succ, p2.apps(add, a, b)))))


def add_succ_case() -> tuple[p2.Expr, p2.Expr]:
    return add_succ, add_succ_type()


def congr_succ_type() -> p2.Expr:
    x = p2.Var("x")
    y = p2.Var("y")
    premise = Eq(p2.Nat, x, y)
    conclusion = Eq(p2.Nat, p2.apps(p2.succ, x), p2.apps(p2.succ, y))
    return p2.Pi("x", p2.Nat, p2.Pi("y", p2.Nat, p2.arrow(premise, conclusion)))


def congr_succ_case() -> tuple[p2.Expr, p2.Expr]:
    x = p2.Var("x")
    y = p2.Var("y")
    h = p2.Var("h")
    premise = Eq(p2.Nat, x, y)
    proof = Lam("x", p2.Nat, Lam("y", p2.Nat, Lam("h", premise, CongSucc(h))))
    return proof, congr_succ_type()


def add_zero_by_rfl_case() -> tuple[p2.Expr, p2.Expr]:
    a = p2.Var("a")
    proof = Lam("a", p2.Nat, Refl(p2.Nat, a))
    expected = p2.Pi("a", p2.Nat, Eq(p2.Nat, p2.apps(add, a, p2.zero), a))
    return proof, expected


def add_succ_by_rfl_case() -> tuple[p2.Expr, p2.Expr]:
    a = p2.Var("a")
    n = p2.Var("n")
    proof = Lam("a", p2.Nat, Lam("n", p2.Nat, Refl(p2.Nat, p2.apps(p2.succ, p2.apps(add, a, n)))))
    expected = p2.Pi("a", p2.Nat, p2.Pi("n", p2.Nat, Eq(p2.Nat, p2.apps(add, a, p2.apps(p2.succ, n)), p2.apps(p2.succ, p2.apps(add, a, n)))))
    return proof, expected


def rewrite_step_case() -> tuple[p2.Expr, p2.Expr]:
    a = p2.Var("a")
    n = p2.Var("n")
    ih = p2.Var("ih")
    premise = Eq(p2.Nat, p2.apps(add, p2.apps(p2.succ, a), n), p2.apps(p2.succ, p2.apps(add, a, n)))
    goal = Eq(p2.Nat, p2.apps(add, p2.apps(p2.succ, a), p2.apps(p2.succ, n)), p2.apps(p2.succ, p2.apps(p2.succ, p2.apps(add, a, n))))
    proof = Lam("a", p2.Nat, Lam("n", p2.Nat, Lam("ih", premise, CongSucc(ih))))
    expected = p2.Pi("a", p2.Nat, p2.Pi("n", p2.Nat, p2.arrow(premise, goal)))
    return proof, expected


REGISTER_BEFORE_CHECK = {
    "Eq",
    "rfl_nat",
    "add",
    "add_zero",
    "add_succ",
    "congr_succ",
}


DEFAULT_CHECKER = phase3_checker()
for _name in (
    "Eq",
    "rfl_nat",
    "add",
    "add_zero",
    "add_succ",
    "congr_succ",
    "add_zero_by_rfl",
    "add_succ_by_rfl",
    "rewrite_step",
):
    register_declaration(DEFAULT_CHECKER, _name)


def infer(expr: p2.Expr, ctx: dict[str, p2.Expr] | None = None, tc: TypeChecker | None = None) -> p2.Expr:
    tc = DEFAULT_CHECKER if tc is None else tc
    return tc.infer(expr, ctx)


def check(expr: p2.Expr, expected: p2.Expr, ctx: dict[str, p2.Expr] | None = None, tc: TypeChecker | None = None) -> None:
    tc = DEFAULT_CHECKER if tc is None else tc
    tc.check(expr, expected, ctx)
