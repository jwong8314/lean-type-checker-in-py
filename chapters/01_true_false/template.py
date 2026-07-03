"""Chapter 1 template: fill in the tiny propositions-as-types checker.

This file is intentionally incomplete. Use `solution.py` only after trying to
fill in each TODO yourself.
"""

from __future__ import annotations

from pylean.type_checker import TypeChecker as AbstractTypeChecker
from pylean.type_checker import TypeCheckerError as TypeError

from .expressions import Const, Expr, Prop, Sort


class TypeChecker(AbstractTypeChecker):
    def __init__(self) -> None:
        super().__init__()
        self.definitions: dict[str, Expr] = {}

        # TODO: register the initial truth constants.
        # Hint: the environment should know `True : Prop`.
        self.add("True", ...)

        # TODO: register the constructor/proof for True.
        # Hint: `True.intro` should have type `True`.
        self.add("True.intro", ...)

    def add_definition(self, name: str, ty: Expr, value: Expr) -> None:
        self.add(name, ty)
        self.definitions[name] = value

    def infer(self, expr: Expr, ctx: dict[str, Expr] | None = None) -> Expr:
        match expr:
            # TODO: implement the Sort rule.
            # Hint: `Prop = Sort(0)`, `Type = Sort(1)`, so Sort(n) has type Sort(n + 1).
            case Sort(level):
                raise NotImplementedError("TODO: infer the type of a Sort")

            case Const(name):
                if name not in self.env:
                    raise TypeError(f"unknown constant {name}")
                return self.env[name]

            case _:
                raise TypeError(f"cannot infer {expr!r}")

    def check(self, expr: Expr, expected: Expr, ctx: dict[str, Expr] | None = None) -> None:
        # TODO: infer the actual type of `expr`, then unfold transparent definitions.
        actual = ...

        # TODO: unfold transparent definitions in the expected type too.
        expected = None

        # Leave as is: the base `defeq` is exact structural equality.
        if not self.defeq(actual, expected):
            raise TypeError(f"expected {self.pretty(expected)}, got {self.pretty(actual)}")

    def unfold_defs(self, expr: Expr) -> Expr:
        match expr:
            # TODO: if this is a defined constant, recursively unfold its value.
            case Const(name) if name in self.definitions:
                return None

            # TODO: otherwise, return the expression unchanged.
            case _:
                return None

    def pretty(self, expr: Expr) -> str:
        match expr:
            # TODO: pretty-print Prop.
            # Hint: Prop is Sort(0).
            case Sort(0):
                return None

            # TODO: pretty-print Type.
            case Sort(1):
                return None

            # TODO: pretty-print higher sorts.
            case Sort(level):
                return None

            # TODO: pretty-print constants by name.
            case Const(name):
                return None

            # TODO: decide how to render unknown expression forms.
            case _:
                return None
