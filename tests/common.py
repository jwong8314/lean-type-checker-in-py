"""Helpers shared by the chapter tests."""

from __future__ import annotations

from pathlib import Path

from kernel.check import Result, check_trace
from kernel.environment import Environment
from kernel.trace import Declaration, load_trace

CHAPTERS = Path(__file__).resolve().parents[1] / "chapters"


def trace_path(chapter: str) -> Path:
    return next(CHAPTERS.glob(f"{chapter}_*")) / "examples.trace"


def replay(chapter: str, only: set[str] | None = None) -> tuple[Environment, dict[str, Result]]:
    """Run a chapter's trace through the kernel; return the environment and results by name."""

    env = Environment()
    results = check_trace(trace_path(chapter), env, only)
    return env, {result.name: result for result in results}


def declarations(chapter: str) -> dict[str, Declaration]:
    """The checked (not imported) declarations of a chapter's trace, by name."""

    return {decl.name: decl for decl in load_trace(trace_path(chapter)) if not decl.imported}


def assert_all_checked(results: dict[str, Result], names: set[str] | None = None) -> None:
    failed = [f"{r.name}: {r.detail}" for r in results.values() if r.status == "FAILED"]
    assert not failed, "the kernel rejected:\n" + "\n".join(failed)
    for name in names or ():
        assert results[name].status == "checked", f"{name} was {results[name].status}, expected checked"
