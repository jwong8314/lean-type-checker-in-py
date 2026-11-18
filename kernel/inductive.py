"""Inductive types: checking a declaration and generating its recursor.

Mirrors `src/kernel/inductive.cpp`, restricted to a single inductive type that
is not nested inside another type constructor. Mutual and nested inductive
types are rejected with a clear error.

Given an inductive type

    inductive I (params) : (indices) → Sort l
      | c₁ : (fields₁) → I params idx₁
      | ...

the kernel adds `I`, each `cᵢ`, and a recursor

    I.rec : {params} → {motive : (indices) → I params indices → Sort u}
          → (minor₁) → ... → {indices} → (t : I params indices) → motive indices t

where `minorᵢ : (fieldsᵢ) → (ih for each recursive field) → motive idxᵢ (cᵢ params fieldsᵢ)`,
together with one computation rule per constructor:

    I.rec params motive minors idxᵢ (cᵢ params fields)  ~>  minorᵢ fields ihs
"""

from __future__ import annotations

from dataclasses import dataclass

from .environment import ConstantInfo, Environment, KernelError
from .expr import Const, Expr, FVar, Param, Pi, Sort, Zero, mk_app, spine
from .level import is_equiv, leq
from .subst import has_loose_bvar, instantiate, mk_lambda, mk_pi, occurs
from .trace import Declaration
from .typechecker import TypeChecker


@dataclass
class Constructor:
    name: str
    fields: list[FVar]
    indices: list[Expr]  # the index arguments of the constructor's result type
    # For each recursive field: (field, binders xs, index arguments) where the
    # field has type `(xs) → I params indices`.
    recursive: list[tuple[FVar, list[FVar], list[Expr]]]


def add_inductive(env: Environment, decl: Declaration, constructors: list[Declaration], check: bool = True) -> None:
    """Add an inductive type, its constructors, and its recursor to `env`.

    With `check=False` the declaration is trusted (it was imported) and only
    the recursor is generated.
    """

    name, universe_params, num_params = decl.name, decl.universe_params, decl.num_params or 0
    levels = tuple(Param(p) for p in universe_params)
    checker = TypeChecker(env, universe_params)

    # --- 1. The type itself: (params) → (indices) → Sort l -----------------
    raise NotImplementedError("TODO: add_inductive")

    # --- 2. Each constructor: (params) → (fields) → I params indices --------
    raise NotImplementedError("TODO: add_inductive")

    # --- 3. Which universe may the recursor eliminate into? -----------------
    raise NotImplementedError("TODO: add_inductive")

    # --- 4. The recursor's type ---------------------------------------------
    raise NotImplementedError("TODO: add_inductive")

    # --- 5. One computation rule per constructor ----------------------------
    raise NotImplementedError("TODO: add_inductive")

    # --- 6. Add the recursor --------------------------------------------------
    raise NotImplementedError("TODO: add_inductive")


def recursive_field(
    checker: TypeChecker, name: str, num_params: int, field_type: Expr, check: bool
) -> tuple[list[FVar], list[Expr]] | None:
    """Is this field a recursive occurrence of the type being defined?

    Returns `(xs, indices)` when the field has type `(xs) → I params indices`,
    and `None` when it does not mention `I` at all. Anything else violates
    strict positivity and is rejected: `I` may not appear to the left of an
    arrow, or inside another type.
    """

    raise NotImplementedError("TODO: recursive_field")


def elim_only_at_universe_zero(checker: TypeChecker, result_level, ctors: list[Constructor]) -> bool:
    """May the recursor only build proofs (`motive : ... → Prop`)?

    A type that is not a proposition can eliminate into any universe. A
    proposition may do so only if examining a proof reveals no information:
    it has no constructors, or exactly one constructor whose every field is
    either itself a proof or already determined by the type's indices.
    """

    raise NotImplementedError("TODO: elim_only_at_universe_zero")


def infer_implicit(ty: Expr) -> Expr:
    """Mark a recursor argument implicit when a later explicit argument's type
    mentions it (so it can always be worked out from that argument). (Given.)

    Mirrors `infer_implicit(rec_ty, strict = true)` in `src/kernel/expr.cpp`.
    """

    if not isinstance(ty, Pi):
        return ty
    body = infer_implicit(ty.body)
    info = ty.info
    if info == "default" and in_explicit_domain(body, 0):
        info = "implicit"
    return Pi(ty.name, info, ty.domain, body)


def in_explicit_domain(ty: Expr, index: int) -> bool:
    if not isinstance(ty, Pi):
        return False
    return (ty.info == "default" and has_loose_bvar(ty.domain, index)) or in_explicit_domain(ty.body, index + 1)
