"""Run every tutorial solution, phase by phase."""

from __future__ import annotations

import runpy
from pathlib import Path


ROOT = Path(__file__).resolve().parent
PHASES = (
    ROOT / "phases/01_true_false/solution.py",
    ROOT / "phases/02_recursive_nat/solution.py",
    ROOT / "phases/03_rewrites/solution.py",
    ROOT / "phases/04_induction/solution.py",
)


def main() -> None:
    for path in PHASES:
        print(path.relative_to(ROOT))
        runpy.run_path(str(path), run_name="__main__")
        print()


if __name__ == "__main__":
    main()
