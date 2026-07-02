"""A tiny, tutorial-style dependent type checker inspired by Lean.

This file is not a Lean implementation.  Lean's kernel has many more
expression forms, universe features, safety checks, projections, inductive
reducers, and caches.  This tutorial grows in four phases:

1. Propositions: `True`, `False`, and simple proof checking.
2. Objects: declarations such as `Nat`, `zero`, and `succ`.
3. Computation and rewrites: equality, `rfl`, `Nat.add` reductions, and a
   small successor-congruence rewrite.
4. Induction: a tiny `Nat.ind` eliminator that proves:

    forall a b : Nat, succ a + b = succ (a + b)

The final theorem is not a proof by `rfl`: Lean's natural-number addition
computes by recursing on the second argument.  We therefore prove it by
induction on `b`, using `rfl` for the base case and a rewrite under `succ` for
the step.

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


@dataclass(frozen=True)
class CongSucc(Expr):
    """If proof shows x = y, then CongSucc(proof) shows succ x = succ y."""

    proof: Expr


@dataclass(frozen=True)
class NatInd(Expr):
    """Natural-number induction.

    NatInd(motive, zero_case, succ_case, target) means:

        Nat.rec motive zero_case succ_case target

    where:

        motive    : Nat -> Sort u
        zero_case : motive zero
        succ_case : forall n, motive n -> motive (succ n)
        target    : Nat
    """

    motive: Expr
    zero_case: Expr
    succ_case: Expr
    target: Expr


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
        case CongSucc(proof):
            return free_vars(proof)
        case NatInd(motive, zero_case, succ_case, target):
            return free_vars(motive) | free_vars(zero_case) | free_vars(succ_case) | free_vars(target)
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
        case CongSucc(proof):
            return CongSucc(rename(proof, old, new))
        case NatInd(motive, zero_case, succ_case, target):
            return NatInd(
                rename(motive, old, new),
                rename(zero_case, old, new),
                rename(succ_case, old, new),
                rename(target, old, new),
            )
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
        case CongSucc(proof):
            return CongSucc(subst(proof, var, replacement))
        case NatInd(motive, zero_case, succ_case, target):
            return NatInd(
                subst(motive, var, replacement),
                subst(zero_case, var, replacement),
                subst(succ_case, var, replacement),
                subst(target, var, replacement),
            )
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
                body_ty = self.whnf(self.infer(body, ctx | {var: domain}))
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
            case CongSucc(proof):
                proof_ty = self.whnf(self.infer(proof, ctx))
                if not isinstance(proof_ty, Eq):
                    raise TypeError(f"congr_succ expected an equality proof, got {pretty(proof_ty)}")
                if not self.defeq(proof_ty.ty, Nat, ctx):
                    raise TypeError(f"congr_succ expected equality over Nat, got {pretty(proof_ty.ty)}")
                return Eq(Nat, apps(succ, proof_ty.lhs), apps(succ, proof_ty.rhs))
            case NatInd(motive, zero_case, succ_case, target):
                motive_ty = self.ensure_pi(self.infer(motive, ctx))
                if not self.defeq(motive_ty.domain, Nat, ctx):
                    raise TypeError(f"Nat induction motive must take Nat, got {pretty(motive_ty.domain)}")
                self.ensure_sort(motive_ty.body)

                motive_at_zero = apps(motive, zero)
                self.check(zero_case, motive_at_zero, ctx)

                n = Var("n")
                ih = Var("ih")
                motive_at_n = apps(motive, n)
                motive_at_succ_n = apps(motive, apps(succ, n))
                succ_case_ty = Pi("n", Nat, Pi("ih", motive_at_n, motive_at_succ_n))
                self.check(succ_case, succ_case_ty, ctx)

                target_ty = self.infer(target, ctx)
                if not self.defeq(target_ty, Nat, ctx):
                    raise TypeError(f"Nat induction target has type {pretty(target_ty)}, expected Nat")
                return apps(motive, target)
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
            case CongSucc(proof):
                return CongSucc(self.normalize(proof))
            case NatInd(motive, zero_case, succ_case, target):
                return NatInd(
                    self.normalize(motive),
                    self.normalize(zero_case),
                    self.normalize(succ_case),
                    self.normalize(target),
                )
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
        case CongSucc(p1), CongSucc(p2):
            return alpha_equal(p1, p2, env)
        case NatInd(m1, z1, s1, t1), NatInd(m2, z2, s2, t2):
            return (
                alpha_equal(m1, m2, env)
                and alpha_equal(z1, z2, env)
                and alpha_equal(s1, s2, env)
                and alpha_equal(t1, t2, env)
            )
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
TrueProp = Const("True")
true_intro = Const("true_intro")
FalseProp = Const("False")
Nat = Const("Nat")
zero = Const("zero")
succ = Const("succ")
add = Const("add")


def nat_add_reducer(tc: TypeChecker, expr: Expr) -> Expr | None:
    """The two definitional equations for Nat.add.

    add a zero     --> a
    add a (succ b) --> succ (add a b)

    Lean's theorem now needs induction on the second argument.  The base and
    step cases still close by definitional equality after these reductions.
    """

    head, args = spine(expr)
    if not (isinstance(head, Const) and head.name == "add" and len(args) == 2):
        return None
    first, second = args
    second = tc.whnf(second)
    if alpha_equal(second, zero):
        return first
    second_head, second_args = spine(second)
    if isinstance(second_head, Const) and second_head.name == "succ" and len(second_args) == 1:
        return apps(succ, apps(add, first, second_args[0]))
    return None


def base_checker() -> TypeChecker:
    tc = TypeChecker()
    tc.add("True", Prop)
    tc.add("true_intro", TrueProp)
    tc.add("False", Prop)
    tc.add("Nat", Type)
    tc.add("zero", Nat)
    tc.add("succ", arrow(Nat, Nat))
    tc.add("add", arrow(Nat, arrow(Nat, Nat)), reducer=nat_add_reducer)
    return tc


def phase1_checker() -> TypeChecker:
    """Phase 1: a checker with only propositions and proofs-as-terms."""

    tc = TypeChecker()
    tc.add("True", Prop)
    tc.add("true_intro", TrueProp)
    tc.add("False", Prop)
    return tc


def phase2_checker() -> TypeChecker:
    """Phase 2: add ordinary mathematical objects, here natural numbers."""

    tc = phase1_checker()
    tc.add("Nat", Type)
    tc.add("zero", Nat)
    tc.add("succ", arrow(Nat, Nat))
    return tc


def phase3_checker() -> TypeChecker:
    """Phase 3: add definitional equations for Nat.add and equality proofs."""

    tc = phase2_checker()
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
    """fun a b => Nat.ind motive base step b

    This corresponds to the Lean proof sketch:

        induction b with
        | zero =>
            rw [Nat.add_zero]
            rw [Nat.add_zero]
            rfl
        | succ n ih =>
            rw [Nat.add_succ]
            rw [ih]
            rw [Nat.add_succ]
            rfl

    The two rewrites by `Nat.add_zero` and `Nat.add_succ` are definitional
    reductions in this checker.  The rewrite by `ih` is represented by
    CongSucc(ih).
    """

    a = Var("a")
    n = Var("n")
    ih = Var("ih")

    def motive_at(x: Expr) -> Expr:
        return Eq(Nat, apps(add, apps(succ, a), x), apps(succ, apps(add, a, x)))

    motive = Lam("b", Nat, motive_at(Var("b")))
    base = Refl(Nat, apps(succ, a))
    step = Lam("n", Nat, Lam("ih", motive_at(n), CongSucc(ih)))
    body = NatInd(motive, base, step, Var("b"))
    return Lam("a", Nat, Lam("b", Nat, body))


def rfl_only_proof() -> Expr:
    """The tempting but invalid proof: fun a b => rfl."""

    a = Var("a")
    b = Var("b")
    rhs = apps(succ, apps(add, a, b))
    return Lam("a", Nat, Lam("b", Nat, Refl(Nat, rhs)))


# ---------------------------------------------------------------------------
# 6. Phase demos
# ---------------------------------------------------------------------------


def phase1_demo() -> list[str]:
    """Phase 1: propositions are types, proofs are terms."""

    tc = phase1_checker()
    tc.check(true_intro, TrueProp)
    false_rejected = rejected(lambda: tc.check(true_intro, FalseProp))
    return [
        f"True : {pretty(tc.infer(TrueProp))}",
        f"False : {pretty(tc.infer(FalseProp))}",
        f"true_intro : {pretty(tc.infer(true_intro))}",
        f"true_intro checked against False? {'no' if false_rejected else 'yes'}",
    ]


def phase2_demo() -> list[str]:
    """Phase 2: add an object language with natural numbers."""

    tc = phase2_checker()
    one = apps(succ, zero)
    two = apps(succ, one)
    tc.check(zero, Nat)
    tc.check(one, Nat)
    tc.check(two, Nat)
    return [
        f"zero : {pretty(tc.infer(zero))}",
        f"succ : {pretty(tc.infer(succ))}",
        f"succ (succ zero) : {pretty(tc.infer(two))}",
    ]


def phase3_demo() -> list[str]:
    """Phase 3: equality, computation, and a small rewrite."""

    tc = phase3_checker()
    a = Var("a")
    n = Var("n")
    ih = Var("ih")

    add_zero_type = Pi("a", Nat, Eq(Nat, apps(add, a, zero), a))
    add_zero_proof = Lam("a", Nat, Refl(Nat, a))
    tc.check(add_zero_proof, add_zero_type)

    add_succ_type = Pi("a", Nat, Pi("n", Nat, Eq(Nat, apps(add, a, apps(succ, n)), apps(succ, apps(add, a, n)))))
    add_succ_proof = Lam("a", Nat, Lam("n", Nat, Refl(Nat, apps(succ, apps(add, a, n)))))
    tc.check(add_succ_proof, add_succ_type)

    rewrite_ctx = {
        "a": Nat,
        "n": Nat,
        "ih": Eq(Nat, apps(add, apps(succ, a), n), apps(succ, apps(add, a, n))),
    }
    rewrite_goal = Eq(
        Nat,
        apps(add, apps(succ, a), apps(succ, n)),
        apps(succ, apps(succ, apps(add, a, n))),
    )
    rewrite_proof = CongSucc(ih)
    tc.check(rewrite_proof, rewrite_goal, rewrite_ctx)

    return [
        f"add_zero proof: {pretty(add_zero_proof)}",
        f"add_succ proof: {pretty(add_succ_proof)}",
        f"rewrite step from ih: {pretty(rewrite_proof)}",
        f"rewrite goal: {pretty(rewrite_goal)}",
    ]


def phase4_demo() -> list[str]:
    """Phase 4: induction proves the target theorem."""

    tc = base_checker()
    target = theorem_type()
    proof = theorem_proof()
    inferred = tc.check(proof, target)
    rfl_rejected = rejected(lambda: tc.check(rfl_only_proof(), target))
    return [
        f"Target theorem: {pretty(target)}",
        f"Proof term: {pretty(proof)}",
        f"Accepted with type: {pretty(inferred)}",
        f"Bare rfl proof accepted? {'no, rejected as expected' if rfl_rejected else 'yes, something is wrong'}",
    ]


def rejected(action: Callable[[], object]) -> bool:
    try:
        action()
    except TypeError:
        return True
    return False


# ---------------------------------------------------------------------------
# 7. Pretty printing and command-line tutorial
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
        case CongSucc(proof):
            return f"congr_succ {atom(proof)}"
        case NatInd(motive, zero_case, succ_case, target):
            return (
                f"Nat.ind {atom(motive)} {atom(zero_case)} "
                f"{atom(succ_case)} {atom(target)}"
            )
        case _:
            return repr(expr)


def atom(expr: Expr) -> str:
    if isinstance(expr, (Sort, Var, Const)):
        return pretty(expr)
    return f"({pretty(expr)})"


def print_phase(title: str, lines: list[str]) -> None:
    print(title)
    for line in lines:
        print(" ", line)
    print()


def demo() -> None:
    print_phase("Phase 1: True and False", phase1_demo())
    print_phase("Phase 2: Natural-number objects", phase2_demo())
    print_phase("Phase 3: Equality and rewrites", phase3_demo())
    print_phase("Phase 4: Induction completes the proof", phase4_demo())


if __name__ == "__main__":
    demo()
