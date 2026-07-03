"""Load chapter files as synthetic packages.

Chapter directory names such as `01_true_false` are great for tutorial ordering
but awkward as Python package names. This helper gives each chapter a safe
package name so files inside the chapter can use normal relative imports like
`from .expressions import Expr`.
"""

from __future__ import annotations

import importlib.util
import re
import sys
import types
from pathlib import Path
from types import ModuleType


class ChapterLoadError(Exception):
    pass


def load_solution_for_dir(chapter_dir: Path) -> ModuleType:
    return load_chapter_module(chapter_dir, "solution")


def load_chapter_module(chapter_dir: Path, module_name: str) -> ModuleType:
    chapter_dir = chapter_dir.resolve()
    package_name = chapter_package_name(chapter_dir)
    ensure_package(package_name, chapter_dir)
    qualified_name = f"{package_name}.{module_name}"
    if qualified_name in sys.modules:
        return sys.modules[qualified_name]

    path = chapter_dir / f"{module_name}.py"
    spec = importlib.util.spec_from_file_location(qualified_name, path)
    if spec is None or spec.loader is None:
        raise ChapterLoadError(f"cannot load {path}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[qualified_name] = module
    spec.loader.exec_module(module)
    return module


def ensure_package(package_name: str, chapter_dir: Path) -> None:
    root_name, _, _ = package_name.partition(".")
    if root_name not in sys.modules:
        root = types.ModuleType(root_name)
        root.__path__ = []
        sys.modules[root_name] = root

    if package_name in sys.modules:
        return
    package = types.ModuleType(package_name)
    package.__path__ = [str(chapter_dir)]
    package.__package__ = package_name
    sys.modules[package_name] = package


def chapter_package_name(chapter_dir: Path) -> str:
    safe_name = re.sub(r"\W", "_", chapter_dir.name)
    if safe_name[:1].isdigit():
        safe_name = f"chapter_{safe_name}"
    return f"pylean_loaded_chapters.{safe_name}"
