"""Tiny elaboration phase between parsing and kernel checking.

Lean's real frontend elaborates parser syntax and tactics into explicit core
terms before the C++ kernel sees a declaration. This module gives the tutorial
runner the same visible phase boundary: parser output still remembers proof
syntax, and elaboration turns it into chapter-specific kernel expressions.
"""

from __future__ import annotations

from dataclasses import dataclass
from types import ModuleType

from pylean import lean_parser


@dataclass(frozen=True)
class ElaborationTrace:
    """One proof elaboration step for optional debugging output."""

    name: str
    proof_ast: object
    before: object
    after: object


def elaborate_declaration(
    solution: ModuleType,
    checker,
    declaration: lean_parser.ParsedDeclaration,
    trace: list[ElaborationTrace] | None = None,
) -> lean_parser.ParsedDeclaration:
    """Elaborate one parsed declaration into a kernel-checkable declaration."""

    if declaration.proof_ast is None:
        return declaration

    expr = lean_parser.lower_proof(
        solution,
        checker,
        declaration.name,
        declaration.proof_ast,
        declaration.expected,
    )
    if trace is not None:
        trace.append(ElaborationTrace(declaration.name, declaration.proof_ast, declaration.expr, expr))
    return lean_parser.ParsedDeclaration(
        declaration.name,
        expr,
        declaration.expected,
        declaration.kind,
        declaration.opaque,
        declaration.recursive_spec,
        declaration.proof_ast,
    )


def elaborate_declarations(
    solution: ModuleType,
    checker,
    declarations: list[lean_parser.ParsedDeclaration],
    trace: list[ElaborationTrace] | None = None,
) -> list[lean_parser.ParsedDeclaration]:
    """Elaborate a batch of parsed declarations."""

    return [elaborate_declaration(solution, checker, declaration, trace) for declaration in declarations]

