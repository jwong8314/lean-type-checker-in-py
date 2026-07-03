"""Shared expression nodes used by every tutorial chapter."""

from __future__ import annotations

from dataclasses import dataclass


@dataclass(frozen=True)
class Expr:
    pass


@dataclass(frozen=True)
class Sort(Expr):
    level: int


@dataclass(frozen=True)
class Const(Expr):
    name: str


Prop = Sort(0)
Type = Sort(1)
