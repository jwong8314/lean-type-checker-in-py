"""Shared abstract type checker used by every tutorial phase."""

from __future__ import annotations

from abc import ABC, abstractmethod
from typing import Any

from expressions import Const, Expr


class TypeCheckerError(Exception):
    pass


class TypeChecker(ABC):
    def __init__(self) -> None:
        self.env: dict[str, Expr] = {}
        self.recursive_types: dict[str, Any] = {}

    def add(self, name: str, ty: Expr) -> None:
        self.env[name] = ty

    def add_recursive_type(self, spec: Any) -> None:
        self.recursive_types[spec.name] = spec
        result_type = Const(spec.name)
        self.add(spec.name, spec.sort)
        for constructor in spec.constructors:
            self.add(constructor.name, self.constructor_type(result_type, constructor.arg_types))

    def constructor_type(self, result_type: Expr, arg_types: tuple[Expr, ...]) -> Expr:
        raise TypeCheckerError("this phase does not support recursive constructors")

    @abstractmethod
    def infer(self, expr: Expr, ctx: dict[str, Expr] | None = None) -> Expr:
        pass

    def check(self, expr: Expr, expected: Expr, ctx: dict[str, Expr] | None = None) -> None:
        actual = self.infer(expr, ctx)
        if not self.defeq(actual, expected):
            raise TypeCheckerError(f"expected {self.pretty(expected)}, got {self.pretty(actual)}")

    def defeq(self, left: Expr, right: Expr) -> bool:
        return left == right

    def pretty(self, expr: Expr) -> str:
        return repr(expr)
