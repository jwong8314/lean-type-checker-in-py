"""Read a kernel trace into `Declaration` values. (Given.)

See `instrumentation/README.md` for the trace format.
"""

from __future__ import annotations

import re
from dataclasses import dataclass
from pathlib import Path

from .expr import App, BVar, Const, Expr, IMax, Lam, Let, Level, Lit, Max, Param, Pi, Proj, Sort, Succ, Zero, level_of_nat


@dataclass
class Declaration:
    kind: str  # axiom, definition, theorem, opaque, inductive, constructor, recursor, quot
    name: str
    universe_params: tuple[str, ...]
    type: Expr
    value: Expr | None = None
    num_params: int | None = None  # inductive types only
    safety: str | None = None  # "unsafe" or "partial" when the kernel does not fully check it
    imported: bool = False  # True for `reference` blocks: already checked by Lean elsewhere


class TraceError(Exception):
    pass


HEADER = re.compile(r"^\[kernel-trace\] (?!end )(.+) (\S+)$")
BINDER = re.compile(r"^(Lam|Pi) (.*) \((\w+)\)$")
CONST = re.compile(r"^Const (.*?)(?: \[(.*)\])?$")


def parse_level(text: str) -> Level:
    """Parse the kernel's level syntax, e.g. `succ (max 1 u)`."""

    tokens = re.findall(r"[()]|[^\s()]+", text)
    pos = 0

    def atom() -> Level:
        nonlocal pos
        token = tokens[pos]
        pos += 1
        if token == "(":
            level = term()
            pos += 1  # closing parenthesis
            return level
        if token.isdigit():
            return level_of_nat(int(token))
        return Param(token)

    def term() -> Level:
        nonlocal pos
        token = tokens[pos]
        if token == "succ":
            pos += 1
            return Succ(atom())
        if token in ("max", "imax"):
            # `max a b c` means `max a (max b c)`.
            pos += 1
            parts = [atom()]
            while pos < len(tokens) and tokens[pos] != ")":
                parts.append(atom())
            level = parts.pop()
            while parts:
                level = Max(parts.pop(), level) if token == "max" else IMax(parts.pop(), level)
            return level
        return atom()

    return term()


def parse_trace(text: str) -> list[Declaration]:
    lines = text.splitlines()
    declarations: list[Declaration] = []
    i = 0
    while i < len(lines):
        header = HEADER.match(lines[i])
        if header is None:
            i += 1
            continue
        kind, name = header.group(1), header.group(2)
        imported = kind.startswith("reference ")
        kind = kind.removeprefix("reference ").removeprefix("mutual ")
        decl = Declaration(kind, name, (), Sort(Zero()), imported=imported)
        i += 1
        while not lines[i].startswith("[kernel-trace] end "):
            line = lines[i]
            if line.startswith("  universe params:"):
                decl.universe_params = tuple(line.split(":", 1)[1].split())
                i += 1
            elif line.startswith("  params:"):
                decl.num_params = int(line.split(":", 1)[1])
                i += 1
            elif line.startswith("  safety:"):
                decl.safety = line.split(":", 1)[1].strip()
                i += 1
            elif line == "  type:":
                decl.type, i = parse_expr(lines, i + 1, 2)
            elif line == "  value:":
                decl.value, i = parse_expr(lines, i + 1, 2)
            else:
                raise TraceError(f"unexpected line {i + 1}: {line!r}")
        i += 1
        declarations.append(decl)
    return declarations


def load_trace(path: str | Path) -> list[Declaration]:
    return parse_trace(Path(path).read_text())


def parse_expr(lines: list[str], i: int, depth: int) -> tuple[Expr, int]:
    """Parse the node at `lines[i]`, which must be indented by `depth`."""

    line = lines[i]
    indent = "  " * depth
    if not line.startswith(indent) or line[len(indent) :].startswith(" "):
        raise TraceError(f"bad indentation at line {i + 1}: {line!r}")
    text = line[len(indent) :]
    i += 1

    def child() -> Expr:
        nonlocal i
        expr, i = parse_expr(lines, i, depth + 1)
        return expr

    if text == "App":
        fn = child()
        return App(fn, child()), i
    if text == "MData":
        return child(), i  # metadata is ignored by the kernel, so drop it here
    binder = BINDER.match(text)
    if binder is not None:
        domain = child()
        body = child()
        cls = Lam if binder.group(1) == "Lam" else Pi
        return cls(binder.group(2), binder.group(3), domain, body), i
    head, _, rest = text.partition(" ")
    if head == "BVar":
        return BVar(int(rest)), i
    if head == "Sort":
        return Sort(parse_level(rest)), i
    if head == "Const":
        const = CONST.match(text)
        levels = tuple(parse_level(level) for level in const.group(2).split(", ")) if const.group(2) else ()
        return Const(const.group(1), levels), i
    if head == "Let":
        ty = child()
        value = child()
        return Let(rest, ty, value, child()), i
    if head == "Lit":
        kind, _, value = rest.partition(" ")
        return Lit(kind, value), i
    if head == "Proj":
        struct, _, index = rest.rpartition(" ")
        return Proj(struct, int(index), child()), i
    raise TraceError(f"unknown node at line {i}: {text!r}")
