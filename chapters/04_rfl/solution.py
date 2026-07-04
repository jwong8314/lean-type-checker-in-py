"""Chapter 4 solution: reuse Chapter 3 kernel, introduce `rfl` elaboration."""

from __future__ import annotations

from .expressions import p3


TypeChecker = p3.TypeChecker

for _name in dir(p3):
    if not _name.startswith("_"):
        globals()[_name] = getattr(p3, _name)

