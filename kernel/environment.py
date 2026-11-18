"""The environment: every constant the kernel has accepted so far. (Given.)"""

from __future__ import annotations

from dataclasses import dataclass, field

from .expr import Expr


class KernelError(Exception):
    """Raised whenever the kernel rejects something."""


@dataclass
class ConstantInfo:
    name: str
    kind: str  # axiom, definition, theorem, opaque, inductive, constructor, recursor, quot
    universe_params: tuple[str, ...]
    type: Expr
    value: Expr | None = None  # definitions and theorems

    # inductive types
    num_params: int = 0
    num_indices: int = 0
    constructors: tuple[str, ...] = ()

    # constructors (and recursors, for `inductive`)
    inductive: str = ""
    constructor_index: int = 0
    num_fields: int = 0

    # recursors
    num_minors: int = 0
    rules: tuple[Expr, ...] = ()  # one right-hand side per constructor
    k: bool = False


@dataclass
class Environment:
    constants: dict[str, ConstantInfo] = field(default_factory=dict)

    def add(self, info: ConstantInfo) -> None:
        if info.name in self.constants:
            raise KernelError(f"constant already declared: {info.name}")
        self.constants[info.name] = info

    def get(self, name: str) -> ConstantInfo:
        if name not in self.constants:
            raise KernelError(f"unknown constant: {name}")
        return self.constants[name]

    def find(self, name: str) -> ConstantInfo | None:
        return self.constants.get(name)
