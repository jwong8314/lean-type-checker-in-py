"""Phase 4 solution: induction over the recursive MyNat declaration."""

from __future__ import annotations

import importlib.util
import sys
from dataclasses import dataclass
from pathlib import Path


def load_phase3():
    path = Path(__file__).resolve().parents[1] / "03_rewrites/solution.py"
    spec = importlib.util.spec_from_file_location("phase3_solution", path)
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


p3 = load_phase3()
p2 = p3.p2


@dataclass(frozen=True)
class Induction(p2.Expr):
    type_name: str
    motive: p2.Expr
    cases: tuple[p2.Expr, ...]
    target: p2.Expr


class TypeChecker(p3.TypeChecker):
    def infer(self, expr: p2.Expr, ctx: dict[str, p2.Expr] | None = None) -> p2.Expr:
        ctx = {} if ctx is None else ctx
        match expr:
            case Induction(type_name, motive, cases, target):
                spec = self.recursive_types.get(type_name)
                if spec is None:
                    raise p2.TypeError(f"{type_name} is not a recursive type")
                if len(cases) != len(spec.constructors):
                    raise p2.TypeError(f"expected {len(spec.constructors)} cases")

                motive_ty = self.infer(motive, ctx)
                if not isinstance(motive_ty, p2.Pi) or not self.defeq(motive_ty.domain, p2.Const(type_name)):
                    raise p2.TypeError("bad induction motive")

                for constructor, case in zip(spec.constructors, cases):
                    self.check(case, induction_case_type(spec, constructor, motive), ctx)

                self.check(target, p2.Const(type_name), ctx)
                return p2.apps(motive, target)
            case _:
                return super().infer(expr, ctx)

    def normalize(self, expr: p2.Expr) -> p2.Expr:
        expr = self.whnf(expr)
        match expr:
            case Induction(type_name, motive, cases, target):
                return Induction(
                    type_name,
                    self.normalize(motive),
                    tuple(self.normalize(case) for case in cases),
                    self.normalize(target),
                )
            case _:
                return super().normalize(expr)

    def pretty(self, expr: p2.Expr) -> str:
        return pretty(expr)


def induction_case_type(spec: p2.RecursiveTypeSpec, constructor: p2.ConstructorSpec, motive: p2.Expr) -> p2.Expr:
    """Derive one case type from a recursive constructor.

    For `succ : MyNat -> MyNat`, this returns:

        forall n : MyNat, motive n -> motive (succ n)
    """

    type_const = p2.Const(spec.name)
    arg_vars = tuple(p2.Var(f"{constructor.name}_arg{i}") for i, _ in enumerate(constructor.arg_types))
    constructor_value = p2.apps(p2.Const(constructor.name), *arg_vars)
    result: p2.Expr = p2.apps(motive, constructor_value)

    binders: list[tuple[str, p2.Expr]] = []
    for arg_var, arg_type in zip(arg_vars, constructor.arg_types):
        binders.append((arg_var.name, arg_type))
        if p3.alpha_equal(arg_type, type_const):
            binders.append((f"{arg_var.name}_ih", p2.apps(motive, arg_var)))

    for name, ty in reversed(binders):
        result = p2.Pi(name, ty, result)
    return result


def theorem_type() -> p2.Expr:
    a = p2.Var("a")
    b = p2.Var("b")
    lhs = p2.apps(p3.add, p2.apps(p2.succ, a), b)
    rhs = p2.apps(p2.succ, p2.apps(p3.add, a, b))
    return p2.Pi("a", p2.MyNat, p2.Pi("b", p2.MyNat, p3.Eq(p2.MyNat, lhs, rhs)))


def theorem_proof() -> p2.Expr:
    a = p2.Var("a")
    n = p2.Var("n")
    ih = p2.Var("ih")

    def motive_at(x: p2.Expr) -> p2.Expr:
        return p3.Eq(
            p2.MyNat,
            p2.apps(p3.add, p2.apps(p2.succ, a), x),
            p2.apps(p2.succ, p2.apps(p3.add, a, x)),
        )

    motive = p3.Lam("b", p2.MyNat, motive_at(p2.Var("b")))
    base = p3.Refl(p2.MyNat, p2.apps(p2.succ, a))
    step = p3.Lam("n", p2.MyNat, p3.Lam("ih", motive_at(n), p3.Rw(ih)))
    body = Induction("MyNat", motive, (base, step), p2.Var("b"))
    return p3.Lam("a", p2.MyNat, p3.Lam("b", p2.MyNat, body))


def after_register_declaration(tc: TypeChecker, declaration) -> None:
    if declaration.name in {"add_zero", "add_succ"}:
        tc.add_reducer("add", p3.nat_add_reducer)


def pretty(expr: p2.Expr) -> str:
    match expr:
        case Induction(type_name, motive, cases, target):
            rendered_cases = " ".join(p3.atom(case) for case in cases)
            return f"induction[{type_name}] {p3.atom(motive)} {rendered_cases} {p3.atom(target)}"
        case _:
            return p3.pretty(expr)
