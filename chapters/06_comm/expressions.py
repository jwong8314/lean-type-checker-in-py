"""Chapter 6 expression nodes for commutativity proof combinators."""

from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path

from pylean.chapter_loader import load_solution_for_dir


p4 = load_solution_for_dir(Path(__file__).resolve().parents[1] / "05_induction")
p3 = p4.p3
p2 = p4.p2

MyNat = p2.Const("MyNat")
zero = p2.Const("zero")
succ = p2.Const("succ")
add = p2.Const("add")
zero_add = p2.Const("zero_add")
succ_add = p2.Const("succ_add")
succ_add_succ = p2.Const("succ_add_succ")
add_assoc = p2.Const("add_assoc")
add_comm = p2.Const("add_comm")
add_right_comm = p2.Const("add_right_comm")


@dataclass(frozen=True)
class EqSymm(p2.Expr):
    proof: p2.Expr


@dataclass(frozen=True)
class EqTrans(p2.Expr):
    left: p2.Expr
    right: p2.Expr


@dataclass(frozen=True)
class EqCongrAddLeft(p2.Expr):
    left_arg: p2.Expr
    proof: p2.Expr
