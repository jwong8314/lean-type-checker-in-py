"""Phase 1 solution: propositions as types."""

from __future__ import annotations

from expressions import Const, Expr, Prop, Sort, Type


class TypeError(Exception):
    pass


class TypeChecker:
    def __init__(self) -> None:
        self.env: dict[str, Expr] = {}

    def add(self, name: str, ty: Expr) -> None:
        self.env[name] = ty

    def infer(self, expr: Expr) -> Expr:
        match expr:
            case Sort(level):
                return Sort(level + 1)
            case Const(name):
                if name not in self.env:
                    raise TypeError(f"unknown constant {name}")
                return self.env[name]
            case _:
                raise TypeError(f"cannot infer {expr!r}")

    def check(self, expr: Expr, expected: Expr) -> None:
        actual = self.infer(expr)
        if actual != expected:
            raise TypeError(f"expected {pretty(expected)}, got {pretty(actual)}")


TrueProp = Const("True")
FalseProp = Const("False")
true_intro = Const("true_intro")

DEFAULT_TYPES = {
    "True": Prop,
    "False": Prop,
    "true_intro": TrueProp,
}


def setting_default_types() -> TypeChecker:
    tc = TypeChecker()
    for name, ty in DEFAULT_TYPES.items():
        tc.add(name, ty)
    return tc


def pretty(expr: Expr) -> str:
    match expr:
        case Sort(0):
            return "Prop"
        case Sort(1):
            return "Type"
        case Sort(level):
            return f"Type {level - 1}"
        case Const(name):
            return name
        case _:
            return repr(expr)


DEFAULT_CHECKER = setting_default_types()


def infer(expr: Expr) -> Expr:
    return DEFAULT_CHECKER.infer(expr)


def check(expr: Expr, expected: Expr) -> None:
    DEFAULT_CHECKER.check(expr, expected)
