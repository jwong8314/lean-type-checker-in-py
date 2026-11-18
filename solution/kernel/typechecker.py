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
                # BEGIN SOLUTION
                info = self.env.get(name)
                if len(levels) != len(info.universe_params):
                    raise KernelError(f"{name} expects {len(info.universe_params)} universe levels, got {len(levels)}")
                for level in levels:
                    self.check_level(level)
                return instantiate_level_params(info.type, dict(zip(info.universe_params, levels)))
                # END SOLUTION
            case Sort(level):
                # Chapter 1. `Sort u : Sort (u+1)`.
                # BEGIN SOLUTION
                self.check_level(level)
                return Sort(Succ(level))
                # END SOLUTION
            case FVar():
                # Chapter 2. A free variable carries its own type.
                # BEGIN SOLUTION
                return expr.type
                # END SOLUTION
            case BVar(_):
                raise KernelError("loose bound variable: step inside binders with `instantiate` first")
            case Pi(name, info, domain, body):
                # Chapter 2. `(x : A) → B` lives in `Sort (imax u v)` where
                # `A : Sort u` and `B : Sort v`.
                # BEGIN SOLUTION
                domain_level = self.ensure_sort(self.infer(domain)).level
                fvar = FVar(name, domain, info)
                body_level = self.ensure_sort(self.infer(instantiate(body, fvar))).level
                return Sort(IMax(domain_level, body_level))
                # END SOLUTION
            case Lam(name, info, domain, body):
                # Chapter 2. `fun (x : A) => b` has type `(x : A) → B` where `b : B`.
                # BEGIN SOLUTION
                self.ensure_sort(self.infer(domain))
                fvar = FVar(name, domain, info)
                body_type = self.infer(instantiate(body, fvar))
                return Pi(name, info, domain, abstract(body_type, fvar))
                # END SOLUTION
            case App(fn, arg):
                # Chapter 2. `f a : B[x := a]` when `f : (x : A) → B` and `a : A`.
                # BEGIN SOLUTION
                fn_type = self.ensure_pi(self.infer(fn))
                arg_type = self.infer(arg)
                if not self.is_def_eq(arg_type, fn_type.domain):
                    raise KernelError(
                        f"application type mismatch: argument has type\n  {arg_type}\nbut function expects\n  {fn_type.domain}"
                    )
                return instantiate(fn_type.body, arg)
                # END SOLUTION
            case Let(_, ty, value, body):
                # BEGIN SOLUTION
                self.ensure_sort(self.infer(ty))
                if not self.is_def_eq(self.infer(value), ty):
                    raise KernelError("let: value does not have the declared type")
                return self.infer(instantiate(body, value))
                # END SOLUTION
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

        # BEGIN SOLUTION
        ty = self.whnf(ty)
        if not isinstance(ty, Sort):
            raise KernelError(f"type expected, got something of type {ty!r}")
        return ty
        # END SOLUTION

    def ensure_pi(self, ty: Expr) -> Pi:
        """`ty` must be (reducible to) a `Pi`; return that `Pi`."""

        # BEGIN SOLUTION
        ty = self.whnf(ty)
        if not isinstance(ty, Pi):
            raise KernelError(f"function expected, got something of type {ty!r}")
        return ty
        # END SOLUTION

    def is_prop(self, ty: Expr) -> bool:
        """Is `ty` a proposition, i.e. does it have type `Prop`?"""

        # BEGIN SOLUTION
        return is_equiv(self.ensure_sort(self.infer(ty)).level, Zero())
        # END SOLUTION

    def infer_proj(self, index: int, struct: Expr) -> Expr:
        """Type of field `index` of `struct`."""

        # BEGIN SOLUTION
        head, params = spine(self.whnf(self.infer(struct)))
        if not isinstance(head, Const) or self.env.get(head.name).kind != "inductive":
            raise KernelError("projection: not a structure")
        inductive = self.env.get(head.name)
        ctor = self.env.get(inductive.constructors[0])
        ty = instantiate_level_params(ctor.type, dict(zip(ctor.universe_params, head.levels)))
        for param in params:
            ty = instantiate(self.ensure_pi(ty).body, param)
        # The type of a field can mention earlier fields: those are projections too.
        for i in range(index):
            ty = instantiate(self.ensure_pi(ty).body, Proj(head.name, i, struct))
        return self.ensure_pi(ty).domain
        # END SOLUTION

    # ----------------------------------------------------------------------
    # whnf: reduce until the outermost constructor of the term is fixed
    # ----------------------------------------------------------------------

    def whnf_core(self, expr: Expr) -> Expr:
        """Weak head normal form *without* unfolding definitions.

        Applies beta (Chapter 2), `let` substitution, recursor computation
        (Chapter 3), and projection (Chapter 5).
        """

        # BEGIN SOLUTION
        while True:
            match expr:
                case Let(_, _, value, body):
                    expr = instantiate(body, value)
                case Proj(_, index, struct):
                    reduced = self.reduce_proj(index, struct)
                    if reduced is None:
                        return expr
                    expr = reduced
                case App(_, _):
                    head, args = spine(expr)
                    new_head = self.whnf_core(head)
                    if isinstance(new_head, Lam):
                        # beta: (fun x => b) a  ~>  b[x := a]
                        used = 0
                        while isinstance(new_head, Lam) and used < len(args):
                            new_head = instantiate(new_head.body, args[used])
                            used += 1
                        expr = mk_app(new_head, args[used:])
                    elif new_head is not head:
                        expr = mk_app(new_head, args)
                    else:
                        reduced = self.reduce_recursor(head, args)
                        if reduced is None:
                            return expr
                        expr = reduced
                case _:
                    return expr
        # END SOLUTION

    def reduce_recursor(self, head: Expr, args: list[Expr]) -> Expr | None:
        """`I.rec ... (ctor fields)  ~>  minor fields ih...`, or `None` if stuck."""

        # BEGIN SOLUTION
        if not isinstance(head, Const):
            return None
        rec = self.env.find(head.name)
        if rec is None or rec.kind != "recursor":
            return None
        major_index = rec.num_params + 1 + rec.num_minors + rec.num_indices
        if len(args) <= major_index:
            return None
        major = self.whnf(args[major_index])
        if isinstance(major, Lit) and major.kind == "nat":
            major = nat_literal_to_constructor(major)
        if rec.k:
            major = self.to_constructor_when_k(rec, major)
        ctor_head, ctor_args = spine(major)
        if not isinstance(ctor_head, Const):
            return None
        ctor = self.env.find(ctor_head.name)
        if ctor is None or ctor.kind != "constructor" or ctor.inductive != rec.inductive:
            return None
        rule = instantiate_level_params(rec.rules[ctor.constructor_index], dict(zip(rec.universe_params, head.levels)))
        # rule = fun params motive minors fields => ...
        result = mk_app(rule, args[: rec.num_params + 1 + rec.num_minors])
        result = mk_app(result, ctor_args[ctor.num_params :])
        return mk_app(result, args[major_index + 1 :])
        # END SOLUTION

    def to_constructor_when_k(self, rec: ConstantInfo, major: Expr) -> Expr:
        """For types like `Eq`: any proof of `a = a` may be treated as `Eq.refl a`."""

        # BEGIN SOLUTION
        head, args = spine(self.whnf(self.infer(major)))
        if not isinstance(head, Const) or head.name != rec.inductive:
            return major
        ctor_name = self.env.get(rec.inductive).constructors[0]
        candidate = mk_app(Const(ctor_name, head.levels), args[: rec.num_params])
        if not self.is_def_eq(self.infer(candidate), mk_app(head, args)):
            return major
        return candidate
        # END SOLUTION

    def reduce_proj(self, index: int, struct: Expr) -> Expr | None:
        """`(Ctor params fields).index  ~>  fields[index]`, or `None` if stuck."""

        # BEGIN SOLUTION
        head, args = spine(self.whnf(struct))
        if not isinstance(head, Const):
            return None
        ctor = self.env.find(head.name)
        if ctor is None or ctor.kind != "constructor" or ctor.num_params + index >= len(args):
            return None
        return args[ctor.num_params + index]
        # END SOLUTION

    def unfold_definition(self, expr: Expr) -> Expr | None:
        """Replace the head constant with its definition (delta), or `None`."""

        # BEGIN SOLUTION
        head, args = spine(expr)
        if not isinstance(head, Const):
            return None
        info = self.env.find(head.name)
        if info is None or info.kind not in ("definition", "theorem") or info.value is None:
            return None
        if len(head.levels) != len(info.universe_params):
            return None
        value = instantiate_level_params(info.value, dict(zip(info.universe_params, head.levels)))
        return mk_app(value, args)
        # END SOLUTION

    def whnf(self, expr: Expr) -> Expr:
        """Weak head normal form, unfolding definitions as needed."""

        # BEGIN SOLUTION
        while True:
            expr = self.whnf_core(expr)
            unfolded = self.unfold_definition(expr)
            if unfolded is None:
                return expr
            expr = unfolded
        # END SOLUTION

    # ----------------------------------------------------------------------
    # is_def_eq: definitional equality
    # ----------------------------------------------------------------------

    def is_def_eq(self, t: Expr, s: Expr) -> bool:
        """Are `t` and `s` equal up to computation?"""

        # BEGIN SOLUTION
        if t is s or t == s:
            return True
        t, s = self.whnf_core(t), self.whnf_core(s)
        quick = self.quick_is_def_eq(t, s)
        if quick is not None:
            return quick
        if self.is_def_eq_proof_irrel(t, s):
            return True

        # Lazy delta reduction: unfold definitions one step at a time, and stop
        # as soon as the two sides look alike. Unfolding everything first would
        # be correct but can be far slower.
        while True:
            t_info, s_info = self.delta_info(t), self.delta_info(s)
            if t_info is None and s_info is None:
                break
            if t_info is not None and t_info is s_info and self.is_def_eq_app(t, s):
                return True
            unfold_t = s_info is None or (t_info is not None and self.height(t_info) >= self.height(s_info))
            unfold_s = t_info is None or (s_info is not None and self.height(s_info) >= self.height(t_info))
            if unfold_t:
                t = self.whnf_core(self.unfold_definition(t))
            if unfold_s:
                s = self.whnf_core(self.unfold_definition(s))
            quick = self.quick_is_def_eq(t, s)
            if quick is not None:
                return quick

        match t, s:
            case Const(n1, l1), Const(n2, l2):
                return n1 == n2 and all(is_equiv(a, b) for a, b in zip(l1, l2, strict=True))
            case FVar(), FVar():
                return t is s
            case Proj(_, i1, e1), Proj(_, i2, e2) if i1 == i2 and self.is_def_eq(e1, e2):
                return True
            case App(_, _), App(_, _) if self.is_def_eq_app(t, s):
                return True
            case Lit(_, _), Lit(_, _):
                return t == s
            case (Lit("nat", _), other) | (other, Lit("nat", _)) if isinstance(spine(other)[0], Const):
                # `3` against `Nat.succ n`: unpack one layer of the literal.
                literal = t if isinstance(t, Lit) else s
                return self.is_def_eq_app(nat_literal_to_constructor(literal), other)
        return self.try_eta(t, s) or self.try_eta(s, t)
        # END SOLUTION

    # BEGIN SOLUTION
    def quick_is_def_eq(self, t: Expr, s: Expr) -> bool | None:
        """Cases decided by shape alone. `None` means "keep going"."""

        if t is s or t == s:
            return True
        match t, s:
            case Sort(l1), Sort(l2):
                return is_equiv(l1, l2)
            case (Lam(name, info, d1, b1), Lam(_, _, d2, b2)) | (Pi(name, info, d1, b1), Pi(_, _, d2, b2)):
                if not self.is_def_eq(d1, d2):
                    return False
                fvar = FVar(name, d1, info)
                return self.is_def_eq(instantiate(b1, fvar), instantiate(b2, fvar))
        return None

    def is_def_eq_app(self, t: Expr, s: Expr) -> bool:
        """`f a b` vs `g c d`: same number of arguments, all pairwise equal."""

        t_head, t_args = spine(t)
        s_head, s_args = spine(s)
        if len(t_args) != len(s_args):
            return False
        return self.is_def_eq(t_head, s_head) and all(self.is_def_eq(a, b) for a, b in zip(t_args, s_args))

    def is_def_eq_proof_irrel(self, t: Expr, s: Expr) -> bool:
        """Any two proofs of the same proposition are equal."""

        try:
            t_type = self.infer(t)
            if not self.is_prop(t_type):
                return False
            return self.is_def_eq(t_type, self.infer(s))
        except KernelError:
            return False

    def try_eta(self, t: Expr, s: Expr) -> bool:
        """`fun x => f x` equals `f`."""

        if not isinstance(t, Lam) or isinstance(s, Lam):
            return False
        try:
            s_type = self.whnf(self.infer(s))
        except KernelError:
            return False
        if not isinstance(s_type, Pi):
            return False
        return self.is_def_eq(t, Lam(s_type.name, s_type.info, s_type.domain, App(s, BVar(0))))

    def delta_info(self, expr: Expr) -> ConstantInfo | None:
        """The definition at the head of `expr`, if it can be unfolded."""

        head, _ = spine(expr)
        if not isinstance(head, Const):
            return None
        info = self.env.find(head.name)
        if info is None or info.kind not in ("definition", "theorem") or info.value is None:
            return None
        return info

    def height(self, info: ConstantInfo) -> int:
        """How many layers of definitions `info` is built on.

        Used only to pick which side to unfold first: the taller one, since it
        is more likely to be defined in terms of the other.
        """

        cached = getattr(info, "_height", None)
        if cached is not None:
            return cached
        info._height = 0  # guard against cycles in unchecked imports
        deepest = 0
        stack = [info.value]
        while stack:
            node = stack.pop()
            match node:
                case Const(name, _):
                    other = self.env.find(name)
                    if other is not None and other.kind == "definition" and other.value is not None:
                        deepest = max(deepest, self.height(other))
                case App(fn, arg):
                    stack += [fn, arg]
                case Lam(_, _, domain, body) | Pi(_, _, domain, body):
                    stack += [domain, body]
                case Let(_, ty, value, body):
                    stack += [ty, value, body]
                case Proj(_, _, inner):
                    stack.append(inner)
        info._height = deepest + 1
        return info._height

    # END SOLUTION


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

    # BEGIN SOLUTION
    check_constant_type(env, name, universe_params, ty)
    env.add(ConstantInfo(name, "axiom", universe_params, ty))
    # END SOLUTION


def add_definition(
    env: Environment, name: str, universe_params: tuple[str, ...], ty: Expr, value: Expr, kind: str = "definition"
) -> None:
    """Accept `name : ty := value` if `value` really has type `ty`.

    `kind` is "definition" or "theorem". A theorem's type must be a proposition.
    """

    # BEGIN SOLUTION
    checker = check_constant_type(env, name, universe_params, ty)
    if kind == "theorem" and not checker.is_prop(ty):
        raise KernelError(f"{name}: the type of a theorem must be a proposition")
    value_type = checker.infer(value)
    if not checker.is_def_eq(value_type, ty):
        raise KernelError(f"{name}: value has type\n  {value_type}\nbut is expected to have type\n  {ty}")
    env.add(ConstantInfo(name, kind, universe_params, ty, value))
    # END SOLUTION
