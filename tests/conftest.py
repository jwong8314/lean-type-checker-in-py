"""Choose which kernel the tests exercise.

    pytest                          # your work in kernel/
    KERNEL_IMPL=solution pytest     # the reference in solution/kernel/
"""

from __future__ import annotations

import os
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
IMPL = os.environ.get("KERNEL_IMPL", "kernel")
if IMPL == "solution":
    sys.path.insert(0, str(ROOT / "solution"))
elif IMPL != "kernel":
    sys.path.insert(0, IMPL)  # any other directory that contains a `kernel` package
else:
    sys.path.insert(0, str(ROOT))
sys.path.insert(0, str(Path(__file__).resolve().parent))
sys.setrecursionlimit(100_000)
