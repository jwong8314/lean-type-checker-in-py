"""Chapter 2: functions, application, bound variables, beta reduction."""

import pytest
from common import assert_all_checked, declarations, replay

from kernel.environment import KernelError
from kernel.expr import App, BVar, Const, FVar, Lam, Pi, Prop, Sort, Succ, Zero
from kernel.level import is_equiv
from kernel.subst import abstract, instantiate
from kernel.typechecker import TypeChecker, add_definition

MINE = {
    "id_proof", "modus_ponens", "compose", "Implies", "Not",
    "implies_refl", "not_not_intro", "beta_in_type",
}  # fmt: skip


def test_instantiate_replaces_the_bound_variable():
    x = Const("x")
    assert instantiate(BVar(0), x) == x
    assert instantiate(App(Const("f"), BVar(0)), x) == App(Const("f"), x)
    # Under one more binder, the variable we want is BVar(1).
    body = Lam("y", "default", Prop, App(BVar(1), BVar(0)))
    assert instantiate(body, x) == Lam("y", "default", Prop, App(x, BVar(0)))


def test_abstract_undoes_instantiate():
    fvar = FVar("x", Prop)
    body = Lam("y", "default", Prop, App(BVar(1), BVar(0)))
    assert abstract(instantiate(body, fvar), fvar) == body


def test_free_variables_are_distinct():
    assert FVar("x", Prop) != FVar("x", Prop)


def test_real_trace_is_accepted():
    _, results = replay("02", only=MINE)
    assert_all_checked(results, MINE)


def test_infer_lambda_and_pi():
    env, _ = replay("02", only=MINE)
    checker = TypeChecker(env)
    identity = Lam("p", "default", Prop, Lam("h", "default", BVar(0), BVar(0)))
    identity_type = Pi("p", "default", Prop, Pi("h", "default", BVar(0), BVar(1)))
    assert checker.is_def_eq(checker.infer(identity), identity_type)
    # (p : Prop) → p → p is itself a proposition; Prop → Prop lives in Type.
    assert is_equiv(checker.ensure_sort(checker.infer(identity_type)).level, Zero())
    assert is_equiv(checker.ensure_sort(checker.infer(Pi("p", "default", Prop, Prop))).level, Succ(Zero()))


def test_beta_reduction():
    env, _ = replay("02", only=MINE)
    checker = TypeChecker(env)
    redex = App(Lam("q", "default", Sort(Succ(Zero())), BVar(0)), Prop)
    assert checker.whnf(redex) == Prop


def test_application_checks_the_argument():
    env, _ = replay("02", only=MINE)
    checker = TypeChecker(env)
    with pytest.raises(KernelError):
        # `Not` expects a proposition, and `Not` itself is a function.
        checker.infer(App(Const("Not"), Const("Not")))
    with pytest.raises(KernelError):
        # `False` is not a function at all.
        checker.infer(App(Const("False"), Const("False")))


def test_wrong_proofs_are_rejected():
    env, _ = replay("02", only=MINE)
    decls = declarations("02")
    # A proof of `p → p` does not prove modus ponens.
    with pytest.raises(KernelError):
        add_definition(env, "bad1", (), decls["modus_ponens"].type, decls["id_proof"].value, "theorem")
    # `∀ p q, p → q` is false; `fun p q h => h` must not be accepted for it.
    false_claim = Pi("p", "default", Prop, Pi("q", "default", Prop, Pi("h", "default", BVar(1), BVar(1))))
    bogus = Lam("p", "default", Prop, Lam("q", "default", Prop, Lam("h", "default", BVar(1), BVar(0))))
    with pytest.raises(KernelError):
        add_definition(env, "bad2", (), false_claim, bogus, "theorem")
