"""Chapter 5 constants for disjunctions, cases, and contradiction.

Lean core does not have separate expression nodes for `Or`, `Or.inl`,
`Or.inr`, `Or.elim`, or `False.elim`. They are constants applied with `App`,
so this chapter reuses the Chapter 4 kernel expression language.
"""

from __future__ import annotations

from pathlib import Path

from pylean.chapter_loader import load_solution_for_dir


p4 = load_solution_for_dir(Path(__file__).resolve().parents[1] / "04_rfl")
p3 = p4.p3
p2 = p3.p2

for _name in dir(p4):
    if not _name.startswith("_"):
        globals()[_name] = getattr(p4, _name)

FalseProp = p2.Const("False")
false_elim = p2.Const("False.elim")
or_const = p2.Const("Or")
or_inl = p2.Const("Or.inl")
or_inr = p2.Const("Or.inr")
or_elim = p2.Const("Or.elim")
