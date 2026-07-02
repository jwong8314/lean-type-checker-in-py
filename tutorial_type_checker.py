"""A tiny, tutorial-style dependent type checker inspired by Lean.

This file is not a Lean implementation.  Lean's kernel has many more
expression forms, universe features, safety checks, projections, inductive
reducers, and caches.  The goal here is the small core that matters for a
first proof:

    forall a b : Nat, succ a + b = succ (a + b)

The proof is `rfl`, just as it is in Lean when addition reduces by recursion on
its first argument.  Our checker therefore needs a little computation inside
definitional equality, but it does not expose a user-facing evaluator.

The shape follows Lean's kernel type checker:

* infer the type of each expression;
* when a Sort or Pi is expected, reduce to weak-head normal form first;
* compare types with definitional equality, which performs beta reduction and
  the primitive Nat.add reduction needed by the theorem.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Callable


# ---------------------------------------------------------------------------
# 1. Syntax
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class Expr:
    """Base class for all expressions."""


@dataclass(frozen=True)
class Sort(Expr):
    """Sort(0) is Prop, Sort(1) is Type, Sort(2) is Type 1, and so on."""

    level: int


@dataclass(frozen=True)
class Var(Expr):
    """A local variable, represented by name for readability."""

    name: str


@dataclass(frozen=True)
class Const(Expr):
    """A globally declared constant."""

    name: str


@dataclass(frozen=True)
class App(Expr):
    """Function application."""

    fn: Expr
    arg: Expr


@dataclass(frozen=True)
class Lam(Expr):
    """Lambda abstraction: fun (x : domain) => body."""

    var: str
    domain: Expr
    body: Expr


@dataclass(frozen=True)
class Pi(Expr):
    """Dependent function type: forall (x : domain), body."""

    var: str
    domain: Expr
    body: Expr


@dataclass(frozen=True)
class Eq(Expr):
    """The proposition that lhs and rhs are equal at type ty."""

    ty: Expr
    lhs: Expr
    rhs: Expr


@dataclass(frozen=True)
class Refl(Expr):
    """Reflexivity proof for equality.

    In Lean this is the constructor `Eq.refl`.  We store the type and value
    explicitly to keep inference direct and readable:

        Refl(A, t) : Eq(A, t, t)

    During checking, this can also prove Eq(A, lhs, rhs) whenever lhs and rhs
    are definitionally equal.
    """

    ty: Expr
    value: Expr


def apps(fn: Expr, *args: Expr) -> Expr:
    """Build nested applications: apps(f, a, b) means ((f a) b)."""

    result = fn
    for arg in args:
        result = App(result, arg)
    return result


def arrow(domain: Expr, body: Expr) -> Pi:
    """Non-dependent function type A -> B."""

    return Pi("_", domain, body)


# ---------------------------------------------------------------------------
# 2. Contexts, declarations, and substitution
# ---------------------------------------------------------------------------


Context = dict[str, Expr]
Reducer = Callable[["TypeChecker", Expr], Expr | None]


@dataclass(frozen=True)
class Declaration:
    ty: Expr
    value: Expr | None = None
    reducer: Reducer | None = None


class TypeError(Exception):
    pass


def free_vars(expr: Expr) -> set[str]:
    match expr:
        case Sort() | Const():
            return set()
        case Var(name):
            return {name}
        case App(fn, arg):
            return free_vars(fn) | free_vars(arg)
        case Lam(var, domain, body) | Pi(var, domain, body):
            return free_vars(domain) | (free_vars(body) - {var})
        case Eq(ty, lhs, rhs):
            return free_vars(ty) | free_vars(lhs) | free_vars(rhs)
        case Refl(ty, value):
            return free_vars(ty) | free_vars(value)
        case _:
            raise TypeError(f"unknown expression: {expr!r}")


def fresh_name(base: str, avoid: set[str]) -> str:
    if base not in avoid:
        return base
    i = 1
    while f"{base}_{i}" in avoid:
        i += 1
    return f"{base}_{i}"


def rename(expr: Expr, old: str, new: str) -> Expr:
    """Rename free occurrences of old to new."""

    match expr:
        case Sort() | Const():
            return expr
        case Var(name):
            return Var(new) if name == old else expr
        case App(fn, arg):
            return App(rename(fn, old, new), rename(arg, old, new))
        case Lam(var, domain, body):
            domain2 = rename(domain, old, new)
            if var == old:
                return Lam(var, domain2, body)
            return Lam(var, domain2, rename(body, old, new))
        case Pi(var, domain, body):
            domain2 = rename(domain, old, new)
            if var == old:
                return Pi(var, domain2, body)
            return Pi(var, domain2, rename(body, old, new))
        case Eq(ty, lhs, rhs):
            return Eq(rename(ty, old, new), rename(lhs, old, new), rename(rhs, old, new))
        case Refl(ty, value):
            return Refl(rename(ty, old, new), rename(value, old, new))
        case _:
            raise TypeError(f"unknown expression: {expr!r}")


def subst(expr: Expr, var: str, replacement: Expr) -> Expr:
    """Capture-avoiding substitution [replacement / var] expr."""

    match expr:
        case Sort() | Const():
            return expr
        case Var(name):
            return replacement if name == var else expr
        case App(fn, arg):
            return App(subst(fn, var, replacement), subst(arg, var, replacement))
        case Lam(bound, domain, body):
            domain2 = subst(domain, var, replacement)
            if bound == var:
                return Lam(bound, domain2, body)
            if bound in free_vars(replacement):
                fresh = fresh_name(bound, free_vars(body) | free_vars(replacement) | {var})
                body = rename(body, bound, fresh)
                bound = fresh
            return Lam(bound, domain2, subst(body, var, replacement))
        case Pi(bound, domain, body):
            domain2 = subst(domain, var, replacement)
            if bound == var:
                return Pi(bound, domain2, body)
            if bound in free_vars(replacement):
                fresh = fresh_name(bound, free_vars(body) | free_vars(replacement) | {var})
                body = rename(body, bound, fresh)
                bound = fresh
            return Pi(bound, domain2, subst(body, var, replacement))
        case Eq(ty, lhs, rhs):
            return Eq(subst(ty, var, replacement), subst(lhs, var, replacement), subst(rhs, var, replacement))
        case Refl(ty, value):
            return Refl(subst(ty, var, replacement), subst(value, var, replacement))
        case _:
            raise TypeError(f"unknown expression: {expr!r}")


# ---------------------------------------------------------------------------
# 3. Type checking and conversion
# ---------------------------------------------------------------------------


class TypeChecker:
    def __init__(self) -> None:
        self.env: dict[str, Declaration] = {}

    def add(self, name: str, ty: Expr, value: Expr | None = None, reducer: Reducer | None = None) -> None:
        self.env[name] = Declaration(ty, value, reducer)

    def infer(self, expr: Expr, ctx: Context | None = None) -> Expr:
        """Infer the type of an expression.

        This mirrors the case split in Lean's `infer_type_core`, but with only
        the expression forms used by this miniature calculus.
        """

        ctx = {} if ctx is None else ctx
        match expr:
            case Sort(level):
                return Sort(level + 1)
            case Var(name):
                if name not in ctx:
                    raise TypeError(f"unknown variable {name!r}")
                return ctx[name]
            case Const(name):
                if name not in self.env:
                    raise TypeError(f"unknown constant {name!r}")
                return self.env[name].ty
            case App(fn, arg):
                fn_ty = self.ensure_pi(self.infer(fn, ctx))
                arg_ty = self.infer(arg, ctx)
                if not self.defeq(arg_ty, fn_ty.domain, ctx):
                    raise TypeError(
                        f"application type mismatch:\n"
                        f"  argument has type {pretty(arg_ty)}\n"
                        f"  expected          {pretty(fn_ty.domain)}"
                    )
                return subst(fn_ty.body, fn_ty.var, arg)
            case Lam(var, domain, body):
                self.ensure_sort(self.infer(domain, ctx))
                body_ty = self.infer(body, ctx | {var: domain})
                return Pi(var, domain, body_ty)
            case Pi(var, domain, body):
                domain_sort = self.ensure_sort(self.infer(domain, ctx))
                body_sort = self.ensure_sort(self.infer(body, ctx | {var: domain}))
                return Sort(max(domain_sort.level, body_sort.level))
            case Eq(ty, lhs, rhs):
                self.ensure_sort(self.infer(ty, ctx))
                lhs_ty = self.infer(lhs, ctx)
                rhs_ty = self.infer(rhs, ctx)
                if not self.defeq(lhs_ty, ty, ctx):
                    raise TypeError(f"left side has type {pretty(lhs_ty)}, expected {pretty(ty)}")
                if not self.defeq(rhs_ty, ty, ctx):
                    raise TypeError(f"right side has type {pretty(rhs_ty)}, expected {pretty(ty)}")
                return Sort(0)
            case Refl(ty, value):
                self.ensure_sort(self.infer(ty, ctx))
                value_ty = self.infer(value, ctx)
                if not self.defeq(value_ty, ty, ctx):
                    raise TypeError(f"refl value has type {pretty(value_ty)}, expected {pretty(ty)}")
                return Eq(ty, value, value)
            case _:
                raise TypeError(f"unknown expression: {expr!r}")

    def check(self, expr: Expr, expected: Expr, ctx: Context | None = None) -> Expr:
        """Check that expr has expected type, returning the inferred type."""

        ctx = {} if ctx is None else ctx
        actual = self.infer(expr, ctx)
        if not self.defeq(actual, expected, ctx):
            raise TypeError(
                f"type mismatch:\n"
                f"  actual   {pretty(actual)}\n"
                f"  expected {pretty(expected)}"
            )
        return actual

    def ensure_sort(self, expr: Expr) -> Sort:
        expr = self.whnf(expr)
        if not isinstance(expr, Sort):
            raise TypeError(f"expected a sort, got {pretty(expr)}")
        return expr

    def ensure_pi(self, expr: Expr) -> Pi:
        expr = self.whnf(expr)
        if not isinstance(expr, Pi):
            raise TypeError(f"expected a function type, got {pretty(expr)}")
        return expr

    def whnf(self, expr: Expr) -> Expr:
        """Weak-head normal form.

        This is the checker-facing computation step.  It reduces only enough to
        expose the outer constructor: a lambda for beta reduction, a Pi for
        applications, or one Nat.add equation for the example theorem.
        """

        while True:
            match expr:
                case Const(name):
                    decl = self.env.get(name)
                    if decl is not None and decl.value is not None:
                        expr = decl.value
                        continue
                    return expr
                case App(fn, arg):
                    fn_whnf = self.whnf(fn)
                    if isinstance(fn_whnf, Lam):
                        expr = subst(fn_whnf.body, fn_whnf.var, arg)
                        continue
                    rebuilt = App(fn_whnf, arg)
                    reduced = self.try_primitive_reduce(rebuilt)
                    if reduced is not None:
                        expr = reduced
                        continue
                    return rebuilt
                case _:
                    return expr

    def normalize(self, expr: Expr) -> Expr:
        """Normalize an expression for definitional equality.

        Lean's kernel uses a more careful algorithm than full normalization.
        Here, full recursive normalization keeps the tutorial simple.
        """

        expr = self.whnf(expr)
        match expr:
            case App(fn, arg):
                return self.whnf(App(self.normalize(fn), self.normalize(arg)))
            case Lam(var, domain, body):
                return Lam(var, self.normalize(domain), self.normalize(body))
            case Pi(var, domain, body):
                return Pi(var, self.normalize(domain), self.normalize(body))
            case Eq(ty, lhs, rhs):
                return Eq(self.normalize(ty), self.normalize(lhs), self.normalize(rhs))
            case Refl(ty, value):
                return Refl(self.normalize(ty), self.normalize(value))
            case _:
                return expr

    def defeq(self, left: Expr, right: Expr, ctx: Context | None = None) -> bool:
        """Definitional equality: compare normal forms up to binder names."""

        del ctx
        return alpha_equal(self.normalize(left), self.normalize(right))

    def try_primitive_reduce(self, expr: Expr) -> Expr | None:
        head, args = spine(expr)
        if isinstance(head, Const):
            decl = self.env.get(head.name)
            if decl is not None and decl.reducer is not None:
                return decl.reducer(self, expr)
        return None


def alpha_equal(left: Expr, right: Expr, env: dict[str, str] | None = None) -> bool:
    """Compare expressions up to renaming of bound variables."""

    env = {} if env is None else env
    match left, right:
        case Sort(l1), Sort(l2):
            return l1 == l2
        case Const(n1), Const(n2):
            return n1 == n2
        case Var(n1), Var(n2):
            return env.get(n1, n1) == n2
        case App(f1, a1), App(f2, a2):
            return alpha_equal(f1, f2, env) and alpha_equal(a1, a2, env)
        case Lam(v1, d1, b1), Lam(v2, d2, b2):
            return alpha_equal(d1, d2, env) and alpha_equal(b1, b2, env | {v1: v2})
        case Pi(v1, d1, b1), Pi(v2, d2, b2):
            return alpha_equal(d1, d2, env) and alpha_equal(b1, b2, env | {v1: v2})
        case Eq(t1, l1, r1), Eq(t2, l2, r2):
            return alpha_equal(t1, t2, env) and alpha_equal(l1, l2, env) and alpha_equal(r1, r2, env)
        case Refl(t1, v1), Refl(t2, v2):
            return alpha_equal(t1, t2, env) and alpha_equal(v1, v2, env)
        case _:
            return False


def spine(expr: Expr) -> tuple[Expr, list[Expr]]:
    args: list[Expr] = []
    while isinstance(expr, App):
        args.append(expr.arg)
        expr = expr.fn
    args.reverse()
    return expr, args


def rebuild(head: Expr, args: list[Expr]) -> Expr:
    return apps(head, *args)


# ---------------------------------------------------------------------------
# 4. Natural numbers
# ---------------------------------------------------------------------------


Prop = Sort(0)
Type = Sort(1)
Nat = Const("Nat")
zero = Const("zero")
succ = Const("succ")
add = Const("add")


def nat_add_reducer(tc: TypeChecker, expr: Expr) -> Expr | None:
    """The two definitional equations for Nat.add.

    add zero     b --> b
    add (succ a) b --> succ (add a b)

    This is the iota-style computation rule that makes the target theorem true
    by reflexivity.  It is intentionally tiny: no evaluator, just the one
    primitive reduction our checker needs when comparing types.
    """

    head, args = spine(expr)
    if not (isinstance(head, Const) and head.name == "add" and len(args) == 2):
        return None
    first, second = args
    first = tc.whnf(first)
    if alpha_equal(first, zero):
        return second
    first_head, first_args = spine(first)
    if isinstance(first_head, Const) and first_head.name == "succ" and len(first_args) == 1:
        return apps(succ, apps(add, first_args[0], second))
    return None


def base_checker() -> TypeChecker:
    tc = TypeChecker()
    tc.add("Nat", Type)
    tc.add("zero", Nat)
    tc.add("succ", arrow(Nat, Nat))
    tc.add("add", arrow(Nat, arrow(Nat, Nat)), reducer=nat_add_reducer)
    return tc


# ---------------------------------------------------------------------------
# 5. The proof: forall a b, succ a + b = succ (a + b)
# ---------------------------------------------------------------------------


def theorem_type() -> Expr:
    a = Var("a")
    b = Var("b")
    lhs = apps(add, apps(succ, a), b)
    rhs = apps(succ, apps(add, a, b))
    return Pi("a", Nat, Pi("b", Nat, Eq(Nat, lhs, rhs)))


def theorem_proof() -> Expr:
    """fun a b => rfl

    The body uses Refl at the right-hand side.  Its inferred type is
    Eq Nat (succ (add a b)) (succ (add a b)), and the checker accepts it at the
    desired type because the left side `add (succ a) b` unfolds to the same
    expression.
    """

    a = Var("a")
    b = Var("b")
    rhs = apps(succ, apps(add, a, b))
    return Lam("a", Nat, Lam("b", Nat, Refl(Nat, rhs)))


# ---------------------------------------------------------------------------
# 6. Pretty printing and demo
# ---------------------------------------------------------------------------


def pretty(expr: Expr) -> str:
    match expr:
        case Sort(0):
            return "Prop"
        case Sort(1):
            return "Type"
        case Sort(level):
            return f"Type {level - 1}"
        case Var(name) | Const(name):
            return name
        case App(_, _):
            head, args = spine(expr)
            if isinstance(head, Const) and head.name == "succ" and len(args) == 1:
                return f"succ {atom(args[0])}"
            if isinstance(head, Const) and head.name == "add" and len(args) == 2:
                return f"{atom(args[0])} + {atom(args[1])}"
            return f"{pretty(head)} " + " ".join(atom(arg) for arg in args)
        case Lam(var, domain, body):
            return f"fun ({var} : {pretty(domain)}) => {pretty(body)}"
        case Pi(var, domain, body):
            if var == "_":
                return f"{atom(domain)} -> {pretty(body)}"
            return f"forall ({var} : {pretty(domain)}), {pretty(body)}"
        case Eq(ty, lhs, rhs):
            del ty
            return f"{pretty(lhs)} = {pretty(rhs)}"
        case Refl(ty, value):
            return f"rfl@{pretty(ty)} {atom(value)}"
        case _:
            return repr(expr)


def atom(expr: Expr) -> str:
    if isinstance(expr, (Sort, Var, Const)):
        return pretty(expr)
    return f"({pretty(expr)})"


def demo() -> None:
    tc = base_checker()
    target = theorem_type()
    proof = theorem_proof()
    inferred = tc.check(proof, target)

    print("Target theorem:")
    print(" ", pretty(target))
    print()
    print("Proof term:")
    print(" ", pretty(proof))
    print()
    print("The checker accepts the proof with type:")
    print(" ", pretty(inferred))


if __name__ == "__main__":
    demo()
