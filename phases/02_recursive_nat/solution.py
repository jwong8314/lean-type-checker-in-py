"""Phase 2 solution: declare Nat as a recursive type."""

from __future__ import annotations

from dataclasses import dataclass

from expressions import Const, Expr, Prop, Sort, Type


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
class ConstructorSpec:
    name: str
    arg_types: tuple[Expr, ...]


@dataclass(frozen=True)
class RecursiveTypeSpec:
    name: str
    sort: Sort
    constructors: tuple[ConstructorSpec, ...]


class TypeError(Exception):
    pass


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
        case _:
            raise TypeError(f"cannot substitute in {expr!r}")


class TypeChecker:
    def __init__(self) -> None:
        self.env: dict[str, Expr] = {}
        self.recursive_types: dict[str, RecursiveTypeSpec] = {}

    def add(self, name: str, ty: Expr) -> None:
        self.env[name] = ty

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
            case _:
                raise TypeError(f"cannot infer {expr!r}")

    def check(self, expr: Expr, expected: Expr, ctx: dict[str, Expr] | None = None) -> None:
        actual = self.infer(expr, ctx)
        if actual != expected:
            raise TypeError(f"expected {pretty(expected)}, got {pretty(actual)}")


Nat = Const("Nat")
zero = Const("zero")
succ = Const("succ")


def nat_type_spec() -> RecursiveTypeSpec:
    return RecursiveTypeSpec(
        "Nat",
        Type,
        (
            ConstructorSpec("zero", ()),
            ConstructorSpec("succ", (Nat,)),
        ),
    )


def phase2_checker() -> TypeChecker:
    tc = TypeChecker()
    tc.add_recursive_type(nat_type_spec())
    return tc


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


one = apps(succ, zero)
two = apps(succ, one)
DEFAULT_CHECKER = phase2_checker()


def infer(expr: Expr, ctx: dict[str, Expr] | None = None) -> Expr:
    return DEFAULT_CHECKER.infer(expr, ctx)


def check(expr: Expr, expected: Expr, ctx: dict[str, Expr] | None = None) -> None:
    DEFAULT_CHECKER.check(expr, expected, ctx)

