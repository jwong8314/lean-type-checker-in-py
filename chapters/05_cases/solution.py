"""Chapter 5 solution: disjunctions, `cases`, and contradiction.

The kernel expression language is unchanged from Chapter 4. Disjunction and
false elimination are ordinary environment constants used through `App`.
"""

from __future__ import annotations

from .expressions import FalseProp, false_elim, or_const, or_elim, or_inl, or_inr, p4


for _name in dir(p4):
    if not _name.startswith("_") and _name not in globals():
        globals()[_name] = getattr(p4, _name)


TypeChecker = p4.TypeChecker
