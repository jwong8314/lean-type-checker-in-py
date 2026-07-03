"""Chapter 1 solution: propositions as types."""

from __future__ import annotations

from pylean.type_checker import TypeChecker as AbstractTypeChecker
from pylean.type_checker import TypeCheckerError as TypeError

from .expressions import Const, Expr, FalseProp, Prop, Sort, TrueProp, Type, true_intro


class TypeChecker(AbstractTypeChecker):
    def __init__(self) -> None:
        super().__init__()
        self.definitions: dict[str, Expr] = {}
        self.add("True", Prop)
        self.add("True.intro", Const("True"))

    def add_definition(self, name: str, ty: Expr, value: Expr) -> None:
        self.add(name, ty)
        self.definitions[name] = value

    def infer(self, expr: Expr, ctx: dict[str, Expr] | None = None) -> Expr:
        match expr:
            case Sort(level):
                return Sort(level + 1)
            case Const(name):
                if name not in self.env:
                    raise TypeError(f"unknown constant {name}")
                return self.env[name]
            case _:
                raise TypeError(f"cannot infer {expr!r}")

    def check(self, expr: Expr, expected: Expr, ctx: dict[str, Expr] | None = None) -> None:
        actual = self.unfold_defs(self.infer(expr, ctx))
        expected = self.unfold_defs(expected)
        if not self.defeq(actual, expected):
            raise TypeError(f"expected {self.pretty(expected)}, got {self.pretty(actual)}")

    def unfold_defs(self, expr: Expr) -> Expr:
        match expr:
            case Const(name) if name in self.definitions:
                return self.unfold_defs(self.definitions[name])
            case _:
                return expr

    def pretty(self, expr: Expr) -> str:
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
