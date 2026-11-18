"""The type checker: `infer`, `whnf`, and `is_def_eq`.

Mirrors `src/kernel/type_checker.cpp`. Method names follow the C++ ones so
the two can be read side by side.
"""

from __future__ import annotations

from .environment import ConstantInfo, Environment, KernelError
from .expr import App, BVar, Const, Expr, FVar, IMax, Lam, Let, Lit, Pi, Proj, Sort, Succ, Zero, mk_app, spine
from .level import is_equiv, level_params
from .subst import abstract, instantiate, instantiate_level_params


class TypeChecker:
    def __init__(self, env: Environment, universe_params: tuple[str, ...] = ()) -> None:
        self.env = env
        self.universe_params = universe_params  # the ones the current declaration may use

    # ----------------------------------------------------------------------
    # infer: compute the type of an expression, checking it on the way
    # ----------------------------------------------------------------------

    def infer(self, expr: Expr) -> Expr:
        """Return the type of `expr`, or raise `KernelError` if it is ill-typed."""

        match expr:
            case Const(name, levels):
                # Chapter 1. Look the constant up; Chapter 3 adds universe levels.
                raise NotImplementedError("TODO: infer")
            case Sort(level):
                # Chapter 1. `Sort u : Sort (u+1)`.
                raise NotImplementedError("TODO: infer")
            case FVar():
                # Chapter 2. A free variable carries its own type.
                raise NotImplementedError("TODO: infer")
            case BVar(_):
                raise KernelError("loose bound variable: step inside binders with `instantiate` first")
            case Pi(name, info, domain, body):
                # Chapter 2. `(x : A) → B` lives in `Sort (imax u v)` where
                # `A : Sort u` and `B : Sort v`.
                raise NotImplementedError("TODO: infer")
            case Lam(name, info, domain, body):
                # Chapter 2. `fun (x : A) => b` has type `(x : A) → B` where `b : B`.
                raise NotImplementedError("TODO: infer")
            case App(fn, arg):
                # Chapter 2. `f a : B[x := a]` when `f : (x : A) → B` and `a : A`.
                raise NotImplementedError("TODO: infer")
            case Let(_, ty, value, body):
                raise NotImplementedError("TODO: infer")
            case Proj(_, index, struct):
                # Chapter 5.
                return self.infer_proj(index, struct)
            case Lit(kind, _):
                return Const("Nat" if kind == "nat" else "String")
        raise KernelError(f"cannot infer the type of {expr!r}")

    def check_level(self, level) -> None:
        """A declaration may only use the universe parameters it declares."""

        unknown = level_params(level) - set(self.universe_params)
        if unknown:
            raise KernelError(f"undeclared universe parameter: {sorted(unknown)[0]}")

    def ensure_sort(self, ty: Expr) -> Sort:
        """`ty` must be (reducible to) a `Sort`; return that `Sort`."""

        raise NotImplementedError("TODO: ensure_sort")

    def ensure_pi(self, ty: Expr) -> Pi:
        """`ty` must be (reducible to) a `Pi`; return that `Pi`."""

        raise NotImplementedError("TODO: ensure_pi")

    def is_prop(self, ty: Expr) -> bool:
        """Is `ty` a proposition, i.e. does it have type `Prop`?"""

        raise NotImplementedError("TODO: is_prop")

    def infer_proj(self, index: int, struct: Expr) -> Expr:
        """Type of field `index` of `struct`."""

        raise NotImplementedError("TODO: infer_proj")

    # ----------------------------------------------------------------------
    # whnf: reduce until the outermost constructor of the term is fixed
    # ----------------------------------------------------------------------

    def whnf_core(self, expr: Expr) -> Expr:
        """Weak head normal form *without* unfolding definitions.

        Applies beta (Chapter 2), `let` substitution, recursor computation
        (Chapter 3), and projection (Chapter 5).
        """

        raise NotImplementedError("TODO: whnf_core")

    def reduce_recursor(self, head: Expr, args: list[Expr]) -> Expr | None:
        """`I.rec ... (ctor fields)  ~>  minor fields ih...`, or `None` if stuck."""

        raise NotImplementedError("TODO: reduce_recursor")

    def to_constructor_when_k(self, rec: ConstantInfo, major: Expr) -> Expr:
        """For types like `Eq`: any proof of `a = a` may be treated as `Eq.refl a`."""

        raise NotImplementedError("TODO: to_constructor_when_k")

    def reduce_proj(self, index: int, struct: Expr) -> Expr | None:
        """`(Ctor params fields).index  ~>  fields[index]`, or `None` if stuck."""

        raise NotImplementedError("TODO: reduce_proj")

    def unfold_definition(self, expr: Expr) -> Expr | None:
        """Replace the head constant with its definition (delta), or `None`."""

        raise NotImplementedError("TODO: unfold_definition")

    def whnf(self, expr: Expr) -> Expr:
        """Weak head normal form, unfolding definitions as needed."""

        raise NotImplementedError("TODO: whnf")

    # ----------------------------------------------------------------------
    # is_def_eq: definitional equality
    # ----------------------------------------------------------------------

    def is_def_eq(self, t: Expr, s: Expr) -> bool:
        """Are `t` and `s` equal up to computation?"""

        raise NotImplementedError("TODO: is_def_eq")

    # (Add helper functions here as you need them.)


def nat_literal_to_constructor(literal: Lit) -> Expr:
    """`0` is `Nat.zero`; `n+1` is `Nat.succ n`. (Given.)

    Lean stores natural number literals as big integers for speed. They only
    appear once the standard library is involved (Chapter 5).
    """

    n = int(literal.value)
    return Const("Nat.zero") if n == 0 else App(Const("Nat.succ"), Lit("nat", str(n - 1)))


# --------------------------------------------------------------------------
# Adding declarations. Mirrors `src/kernel/environment.cpp`.
# --------------------------------------------------------------------------


def check_constant_type(env: Environment, name: str, universe_params: tuple[str, ...], ty: Expr) -> TypeChecker:
    """Checks shared by every kind of declaration; returns a checker to reuse."""

    if len(set(universe_params)) != len(universe_params):
        raise KernelError(f"{name}: duplicate universe parameter")
    checker = TypeChecker(env, universe_params)
    checker.ensure_sort(checker.infer(ty))
    return checker


def add_axiom(env: Environment, name: str, universe_params: tuple[str, ...], ty: Expr) -> None:
    """Accept a constant with no value. Only its type is checked."""

    raise NotImplementedError("TODO: add_axiom")


def add_definition(
    env: Environment, name: str, universe_params: tuple[str, ...], ty: Expr, value: Expr, kind: str = "definition"
) -> None:
    """Accept `name : ty := value` if `value` really has type `ty`.

    `kind` is "definition" or "theorem". A theorem's type must be a proposition.
    """

    raise NotImplementedError("TODO: add_definition")
