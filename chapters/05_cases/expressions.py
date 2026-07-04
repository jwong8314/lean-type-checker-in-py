"""Chapter 5 expression nodes for disjunctions, cases, and contradiction."""

from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path

from pylean.chapter_loader import load_solution_for_dir


p4 = load_solution_for_dir(Path(__file__).resolve().parents[1] / "04_rfl")
p3 = p4.p3
p2 = p3.p2

for _name in dir(p4):
    if not _name.startswith("_"):
        globals()[_name] = getattr(p4, _name)

FalseProp = p2.Const("False")


@dataclass(frozen=True)
class Or(p2.Expr):
    left: p2.Expr
    right: p2.Expr


@dataclass(frozen=True)
class OrInl(p2.Expr):
    left: p2.Expr
    right: p2.Expr
    proof: p2.Expr


@dataclass(frozen=True)
class OrInr(p2.Expr):
    left: p2.Expr
    right: p2.Expr
    proof: p2.Expr


@dataclass(frozen=True)
class OrCases(p2.Expr):
    target: p2.Expr
    left_case: p2.Expr
    right_case: p2.Expr


@dataclass(frozen=True)
class FalseElim(p2.Expr):
    goal: p2.Expr
    proof: p2.Expr

