"""Chapter 2 solution: declare MyNat as a recursive type."""

from __future__ import annotations

from dataclasses import dataclass

from pylean.expressions import Const, Expr, Prop, Sort, Type
from pylean.type_checker import TypeChecker as AbstractTypeChecker
from pylean.type_checker import TypeCheckerError as TypeError


@dataclass(frozen=True)
class Var(Expr):
    name: str


@dataclass(frozen=True)
class App(Expr):
    fn: Expr
    arg: Expr


@dataclass(frozen=True)
class Pi(Expr):
    var: str
    domain: Expr
    body: Expr


@dataclass(frozen=True)
class Lam(Expr):
    var: str
    domain: Expr
    body: Expr


@dataclass(frozen=True)
class Eq(Expr):
    ty: Expr
    lhs: Expr
    rhs: Expr


@dataclass(frozen=True)
class Refl(Expr):
    ty: Expr
    value: Expr


@dataclass(frozen=True)
class ConstructorSpec:
    name: str
    arg_types: tuple[Expr, ...]


@dataclass(frozen=True)
class RecursiveTypeSpec:
    name: str
    sort: Sort
    constructors: tuple[ConstructorSpec, ...]


def apps(fn: Expr, *args: Expr) -> Expr:
    for arg in args:
        fn = App(fn, arg)
    return fn


def arrow(domain: Expr, body: Expr) -> Pi:
    return Pi("_", domain, body)


def constructor_type(result_type: Expr, arg_types: tuple[Expr, ...]) -> Expr:
    ty = result_type
    for arg_type in reversed(arg_types):
        ty = arrow(arg_type, ty)
    return ty


def subst(expr: Expr, var: str, replacement: Expr) -> Expr:
    match expr:
        case Sort() | Const():
            return expr
        case Var(name):
            return replacement if name == var else expr
        case App(fn, arg):
            return App(subst(fn, var, replacement), subst(arg, var, replacement))
        case Pi(bound, domain, body):
            domain = subst(domain, var, replacement)
            if bound == var:
                return Pi(bound, domain, body)
            return Pi(bound, domain, subst(body, var, replacement))
        case Lam(bound, domain, body):
            domain = subst(domain, var, replacement)
            if bound == var:
                return Lam(bound, domain, body)
            return Lam(bound, domain, subst(body, var, replacement))
        case Eq(ty, lhs, rhs):
            return Eq(subst(ty, var, replacement), subst(lhs, var, replacement), subst(rhs, var, replacement))
        case Refl(ty, value):
            return Refl(subst(ty, var, replacement), subst(value, var, replacement))
        case _:
            raise TypeError(f"cannot substitute in {expr!r}")


class TypeChecker(AbstractTypeChecker):
    def __init__(self) -> None:
        super().__init__()
        self.recursive_types: dict[str, RecursiveTypeSpec] = {}

    def add_recursive_type(self, spec: RecursiveTypeSpec) -> None:
        self.recursive_types[spec.name] = spec
        result_type = Const(spec.name)
        self.add(spec.name, spec.sort)
        for constructor in spec.constructors:
            self.add(constructor.name, constructor_type(result_type, constructor.arg_types))

    def infer(self, expr: Expr, ctx: dict[str, Expr] | None = None) -> Expr:
        ctx = {} if ctx is None else ctx
        match expr:
            case Sort(level):
                return Sort(level + 1)
            case Const(name):
                if name not in self.env:
                    raise TypeError(f"unknown constant {name}")
                return self.env[name]
            case Var(name):
                if name not in ctx:
                    raise TypeError(f"unknown variable {name}")
                return ctx[name]
            case App(fn, arg):
                fn_ty = self.infer(fn, ctx)
                if not isinstance(fn_ty, Pi):
                    raise TypeError(f"expected function type, got {pretty(fn_ty)}")
                self.check(arg, fn_ty.domain, ctx)
                return subst(fn_ty.body, fn_ty.var, arg)
            case Pi(var, domain, body):
                self.check(domain, Type, ctx)
                self.check(body, Type, ctx | {var: domain})
                return Type
            case Lam(var, domain, body):
                if not isinstance(self.infer(domain, ctx), Sort):
                    raise TypeError(f"lambda domain is not a sort: {pretty(domain)}")
                return Pi(var, domain, self.infer(body, ctx | {var: domain}))
            case Eq(ty, lhs, rhs):
                self.check(ty, Type, ctx)
                self.check(lhs, ty, ctx)
                self.check(rhs, ty, ctx)
                return Prop
            case Refl(ty, value):
                self.check(ty, Type, ctx)
                self.check(value, ty, ctx)
                return Eq(ty, value, value)
            case _:
                raise TypeError(f"cannot infer {expr!r}")

    def pretty(self, expr: Expr) -> str:
        return pretty(expr)

    def execute_tactics(self, goal: Expr, tactics, lower_expr) -> Expr:
        if len(tactics) == 1 and tactics[0].__class__.__name__ == "RflNode":
            if not isinstance(goal, Eq):
                raise TypeError("rfl expected an equality goal")
            return Refl(goal.ty, goal.rhs)
        return super().execute_tactics(goal, tactics, lower_expr)


MyNat = Const("MyNat")
zero = Const("zero")
succ = Const("succ")
EqConst = Const("Eq")


def mynat_type_spec() -> RecursiveTypeSpec:
    return RecursiveTypeSpec(
        "MyNat",
        Type,
        (
            ConstructorSpec("zero", ()),
            ConstructorSpec("succ", (MyNat,)),
        ),
    )


def pretty(expr: Expr) -> str:
    match expr:
        case Sort(0):
            return "Prop"
        case Sort(1):
            return "Type"
        case Const(name) | Var(name):
            return name
        case App(_, _):
            head, args = spine(expr)
            return f"{pretty(head)} " + " ".join(atom(arg) for arg in args)
        case Pi("_", domain, body):
            return f"{atom(domain)} -> {pretty(body)}"
        case Pi(var, domain, body):
            return f"forall ({var} : {pretty(domain)}), {pretty(body)}"
        case Lam(var, domain, body):
            return f"fun ({var} : {pretty(domain)}) => {pretty(body)}"
        case Eq(_, lhs, rhs):
            return f"{pretty(lhs)} = {pretty(rhs)}"
        case Refl(ty, value):
            return f"rfl@{pretty(ty)} {atom(value)}"
        case _:
            return repr(expr)


def atom(expr: Expr) -> str:
    if isinstance(expr, (Sort, Const, Var)):
        return pretty(expr)
    return f"({pretty(expr)})"


def spine(expr: Expr) -> tuple[Expr, list[Expr]]:
    args: list[Expr] = []
    while isinstance(expr, App):
        args.append(expr.arg)
        expr = expr.fn
    args.reverse()
    return expr, args
