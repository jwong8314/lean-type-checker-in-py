"""Shared abstract type checker used by every tutorial phase."""

from __future__ import annotations

from abc import ABC, abstractmethod
from collections.abc import Callable, Sequence

from expressions import Expr


class TypeCheckerError(Exception):
    """Raised when a term cannot be inferred or checked."""

    pass


class TypeChecker(ABC):
    """Shared shell for every tutorial type checker.

    Phase solutions inherit this class and customize `infer`. The base class
    only knows about global constants, generic checking, and definitional
    equality; later phases add richer syntax and behavior.
    """

    def __init__(self) -> None:
        """Start with an empty global environment."""

        self.env: dict[str, Expr] = {}

    def add(self, name: str, ty: Expr) -> None:
        """Register a global constant and its type."""

        self.env[name] = ty

    @abstractmethod
    def infer(self, expr: Expr, ctx: dict[str, Expr] | None = None) -> Expr:
        """Infer the type of an expression.

        Each phase implements this because each phase introduces new expression
        forms. The optional `ctx` stores local variables introduced by binders.
        """

        pass

    def check(self, expr: Expr, expected: Expr, ctx: dict[str, Expr] | None = None) -> None:
        """Verify that an expression has the expected type."""

        actual = self.infer(expr, ctx)
        if not self.defeq(actual, expected):
            raise TypeCheckerError(f"expected {self.pretty(expected)}, got {self.pretty(actual)}")

    def defeq(self, left: Expr, right: Expr) -> bool:
        """Return whether two expressions are definitionally equal."""

        return left == right

    def pretty(self, expr: Expr) -> str:
        """Render an expression for error messages."""

        return repr(expr)

    def execute_tactics(
        self,
        goal: Expr,
        tactics: Sequence[object],
        lower_expr: Callable[[object], Expr],
    ) -> Expr:
        """Elaborate a small tactic script into a proof term.

        Tactics are not kernel primitives: this helper belongs to the
        tutorial runner/elaboration layer. Phase checkers override it as they
        learn the proof-term constructors that tactics should produce.
        """

        raise TypeCheckerError("this phase does not support tactic execution")
