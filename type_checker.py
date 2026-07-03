"""Shared abstract type checker used by every tutorial phase."""

from __future__ import annotations

from abc import ABC, abstractmethod

from expressions import Expr


class TypeCheckerError(Exception):
    pass


class TypeChecker(ABC):
    def __init__(self) -> None:
        self.env: dict[str, Expr] = {}

    def add(self, name: str, ty: Expr) -> None:
        self.env[name] = ty

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
