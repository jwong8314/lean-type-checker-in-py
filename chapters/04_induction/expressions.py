"""Chapter 4 expression nodes for induction and equality chaining."""

from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path

from pylean.chapter_loader import load_solution_for_dir


p3 = load_solution_for_dir(Path(__file__).resolve().parents[1] / "03_rewrites")
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
