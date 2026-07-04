"""Chapter 4 reuses Chapter 3 syntax and introduces `rfl` elaboration."""

from __future__ import annotations

from pathlib import Path

from pylean.chapter_loader import load_solution_for_dir


p3 = load_solution_for_dir(Path(__file__).resolve().parents[1] / "03_rewrites")

for _name in dir(p3):
    if not _name.startswith("_"):
        globals()[_name] = getattr(p3, _name)

