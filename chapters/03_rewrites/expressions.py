"""Chapter 3 expression nodes: equality, lambdas, and succ congruence."""

from __future__ import annotations

import importlib.util
import sys
from dataclasses import dataclass
from pathlib import Path


def load_chapter2():
    path = Path(__file__).resolve().parents[1] / "02_recursive_nat/solution.py"
    spec = importlib.util.spec_from_file_location("chapter2_solution", path)
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


p2 = load_chapter2()


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
class SuccCongr(p2.Expr):
    proof: p2.Expr


add = p2.Const("add")
EqConst = p2.Const("Eq")


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
        case SuccCongr(proof):
            return SuccCongr(subst(proof, var, replacement))
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
        case SuccCongr(p1), SuccCongr(p2_):
            return alpha_equal(p1, p2_, env)
        case _:
            return False


def pretty(expr: p2.Expr) -> str:
    match expr:
        case Eq(_, lhs, rhs):
            return f"{pretty(lhs)} = {pretty(rhs)}"
        case Refl(ty, value):
            return f"rfl@{pretty(ty)} {atom(value)}"
        case SuccCongr(proof):
            return f"succ_congr {atom(proof)}"
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
