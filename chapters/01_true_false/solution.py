"""Chapter 1 solution: propositions as types."""

from __future__ import annotations

from pylean.expressions import Const, Expr, Prop, Sort, Type
from pylean.type_checker import TypeChecker as AbstractTypeChecker
from pylean.type_checker import TypeCheckerError as TypeError


class TypeChecker(AbstractTypeChecker):
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


TrueProp = Const("True")
FalseProp = Const("False")
true_intro = Const("true_intro")
