"""Chapter 1 solution: propositions as types."""

from __future__ import annotations

import importlib.util
import sys
from pathlib import Path

from pylean.type_checker import TypeChecker as AbstractTypeChecker
from pylean.type_checker import TypeCheckerError as TypeError


def load_expressions():
    path = Path(__file__).resolve().with_name("expressions.py")
    spec = importlib.util.spec_from_file_location("chapter1_expressions", path)
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


exprs = load_expressions()

Const = exprs.Const
Expr = exprs.Expr
Prop = exprs.Prop
Sort = exprs.Sort
Type = exprs.Type
TrueProp = exprs.TrueProp
FalseProp = exprs.FalseProp
true_intro = exprs.true_intro


class TypeChecker(AbstractTypeChecker):
    def __init__(self) -> None:
        super().__init__()
        self.add("True", Prop)
        self.add("True.intro", Const("True"))

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

    def defeq(self, left: Expr, right: Expr) -> bool:
        if left == right:
            return True
        return {left, right} == {Const("True"), Const("TrueProp")}

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
