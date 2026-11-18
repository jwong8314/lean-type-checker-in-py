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
    # BEGIN SOLUTION
    if check:
        checker.ensure_sort(checker.infer(decl.type))
    params: list[FVar] = []
    indices: list[FVar] = []
    ty = decl.type
    while True:
        ty = checker.whnf(ty) if not isinstance(ty, Pi) else ty
        if not isinstance(ty, Pi):
            break
        fvar = FVar(ty.name, ty.domain, ty.info)
        (params if len(params) < num_params else indices).append(fvar)
        ty = instantiate(ty.body, fvar)
    if len(params) != num_params or not isinstance(ty, Sort):
        raise KernelError(f"{name}: the type of an inductive type must end in a Sort")
    result_level = ty.level
    env.add(
        ConstantInfo(
            name,
            "inductive",
            universe_params,
            decl.type,
            num_params=num_params,
            num_indices=len(indices),
            constructors=tuple(c.name for c in constructors),
        )
    )
    # END SOLUTION

    # --- 2. Each constructor: (params) → (fields) → I params indices --------
    # BEGIN SOLUTION
    self_applied = mk_app(Const(name, levels), params)
    ctors: list[Constructor] = []
    for index, ctor_decl in enumerate(constructors):
        if check:
            checker.ensure_sort(checker.infer(ctor_decl.type))
        ty = ctor_decl.type
        for param in params:
            if not isinstance(ty, Pi) or (check and not checker.is_def_eq(ty.domain, param.type)):
                raise KernelError(f"{ctor_decl.name}: constructor parameters must match the inductive type's")
            ty = instantiate(ty.body, param)
        fields: list[FVar] = []
        recursive: list[tuple[FVar, list[FVar], list[Expr]]] = []
        while isinstance(ty, Pi):
            field = FVar(ty.name, ty.domain, ty.info)
            if check:
                # A field may not live in a bigger universe than the type itself
                # (unless the type is a proposition).
                field_level = checker.ensure_sort(checker.infer(ty.domain)).level
                if not is_equiv(result_level, Zero()) and not leq(field_level, result_level):
                    raise KernelError(f"{ctor_decl.name}: universe level of field '{ty.name}' is too big")
            rec = recursive_field(checker, name, num_params, ty.domain, check)
            if rec is not None:
                recursive.append((field, *rec))
            fields.append(field)
            ty = instantiate(ty.body, field)
        head, args = spine(ty)
        if head != Const(name, levels) or len(args) != num_params + len(indices):
            raise KernelError(f"{ctor_decl.name}: constructor must return {name}")
        if any(arg is not param for arg, param in zip(args, params)):
            raise KernelError(f"{ctor_decl.name}: constructor must return {name} applied to its parameters")
        ctors.append(Constructor(ctor_decl.name, fields, args[num_params:], recursive))
        env.add(
            ConstantInfo(
                ctor_decl.name,
                "constructor",
                universe_params,
                ctor_decl.type,
                inductive=name,
                constructor_index=index,
                num_params=num_params,
                num_fields=len(fields),
            )
        )
    # END SOLUTION

    # --- 3. Which universe may the recursor eliminate into? -----------------
    # BEGIN SOLUTION
    rec_universe_params = universe_params
    if elim_only_at_universe_zero(checker, result_level, ctors):
        elim_level = Zero()
    else:
        fresh, n = "u", 0
        while fresh in universe_params:
            n += 1
            fresh = f"u_{n}"
        elim_level = Param(fresh)
        rec_universe_params = (fresh, *universe_params)
    # END SOLUTION

    # --- 4. The recursor's type ---------------------------------------------
    # BEGIN SOLUTION
    major = FVar("t", mk_app(self_applied, indices))
    motive = FVar("motive", mk_pi([*indices, major], Sort(elim_level)))
    minors: list[FVar] = []
    for ctor in ctors:
        ihs = [
            FVar(f"{field.name}_ih", mk_pi(xs, mk_app(motive, [*idx, mk_app(field, xs)])))
            for field, xs, idx in ctor.recursive
        ]
        result = mk_app(motive, [*ctor.indices, mk_app(Const(ctor.name, levels), [*params, *ctor.fields])])
        minors.append(FVar(ctor.name.rpartition(".")[2], mk_pi([*ctor.fields, *ihs], result)))
    rec_type = mk_pi([*params, motive, *minors, *indices, major], mk_app(motive, [*indices, major]))
    rec_type = infer_implicit(rec_type)
    # END SOLUTION

    # --- 5. One computation rule per constructor ----------------------------
    # BEGIN SOLUTION
    rec_const = Const(f"{name}.rec", tuple(Param(p) for p in rec_universe_params))
    rec_prefix = mk_app(rec_const, [*params, motive, *minors])
    rules: list[Expr] = []
    for ctor, minor in zip(ctors, minors):
        ihs = [
            mk_lambda(xs, mk_app(rec_prefix, [*idx, mk_app(field, xs)])) for field, xs, idx in ctor.recursive
        ]
        rhs = mk_app(minor, [*ctor.fields, *ihs])
        rules.append(mk_lambda([*params, motive, *minors, *ctor.fields], rhs))
    # END SOLUTION

    # --- 6. Add the recursor --------------------------------------------------
    # BEGIN SOLUTION
    # "K": a proposition with one constructor that has no fields (like `Eq`).
    k = is_equiv(result_level, Zero()) and len(ctors) == 1 and not ctors[0].fields
    env.add(
        ConstantInfo(
            f"{name}.rec",
            "recursor",
            rec_universe_params,
            rec_type,
            inductive=name,
            num_params=num_params,
            num_indices=len(indices),
            num_minors=len(ctors),
            rules=tuple(rules),
            k=k,
        )
    )
    # END SOLUTION


def recursive_field(
    checker: TypeChecker, name: str, num_params: int, field_type: Expr, check: bool
) -> tuple[list[FVar], list[Expr]] | None:
    """Is this field a recursive occurrence of the type being defined?

    Returns `(xs, indices)` when the field has type `(xs) → I params indices`,
    and `None` when it does not mention `I` at all. Anything else violates
    strict positivity and is rejected: `I` may not appear to the left of an
    arrow, or inside another type.
    """

    # BEGIN SOLUTION
    if not occurs(name, field_type):
        return None
    xs: list[FVar] = []
    ty = checker.whnf(field_type)
    while isinstance(ty, Pi):
        if occurs(name, ty.domain):
            raise KernelError(f"{name}: non-positive occurrence of the type being defined")
        x = FVar(ty.name, ty.domain, ty.info)
        xs.append(x)
        ty = checker.whnf(instantiate(ty.body, x))
    head, args = spine(ty)
    if not isinstance(head, Const) or head.name != name:
        raise KernelError(f"{name}: nested inductive types are not supported by this kernel")
    if any(occurs(name, arg) for arg in args):
        raise KernelError(f"{name}: invalid recursive occurrence of the type being defined")
    return xs, args[num_params:]
    # END SOLUTION


def elim_only_at_universe_zero(checker: TypeChecker, result_level, ctors: list[Constructor]) -> bool:
    """May the recursor only build proofs (`motive : ... → Prop`)?

    A type that is not a proposition can eliminate into any universe. A
    proposition may do so only if examining a proof reveals no information:
    it has no constructors, or exactly one constructor whose every field is
    either itself a proof or already determined by the type's indices.
    """

    # BEGIN SOLUTION
    if not is_equiv(result_level, Zero()):
        return False
    if len(ctors) == 0:
        return False
    if len(ctors) > 1:
        return True
    ctor = ctors[0]
    for field in ctor.fields:
        if checker.is_prop(field.type):
            continue
        if not any(index is field for index in ctor.indices):
            return True
    return False
    # END SOLUTION


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
