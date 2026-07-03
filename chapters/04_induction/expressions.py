"""Chapter 4 expression nodes for induction and equality chaining."""

from __future__ import annotations

import importlib.util
import sys
from dataclasses import dataclass
from pathlib import Path


def load_chapter3():
    path = Path(__file__).resolve().parents[1] / "03_rewrites/solution.py"
    spec = importlib.util.spec_from_file_location("chapter3_solution", path)
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


p3 = load_chapter3()
p2 = p3.p2


@dataclass(frozen=True)
class Induction(p2.Expr):
    type_name: str
    motive: p2.Expr
    cases: tuple[p2.Expr, ...]
    target: p2.Expr


@dataclass(frozen=True)
class EqSymm(p2.Expr):
    proof: p2.Expr


@dataclass(frozen=True)
class EqTrans(p2.Expr):
    left: p2.Expr
    right: p2.Expr
