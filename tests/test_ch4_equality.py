"""Chapter 4: equality, proofs by computation, proofs by induction."""

import pytest
from common import assert_all_checked, declarations, replay, trace_path

from kernel.environment import KernelError
from kernel.expr import App, BVar, Const, Lam, Succ, Zero, erase_binder_names, mk_app
from kernel.trace import load_trace
from kernel.typechecker import TypeChecker, add_definition

one = Succ(Zero())
THEOREMS = {
    "Eq.symm", "Eq.trans", "Eq.congrArg", "MyNat.two_add_two", "MyNat.add_zero",
    "MyNat.add_succ", "MyNat.zero_add", "MyNat.succ_add", "MyNat.add_comm",
}  # fmt: skip


def eq(a, b):
    return mk_app(Const("Eq", (one,)), [Const("MyNat"), a, b])


def refl(a):
    return mk_app(Const("Eq.refl", (one,)), [Const("MyNat"), a])


def add(a, b):
    return mk_app(Const("MyNat.add"), [a, b])


zero = Const("MyNat.zero")


def test_real_trace_is_accepted():
    _, results = replay("04")
    assert_all_checked(results, THEOREMS)


def test_eq_recursor_matches_lean():
    # `Eq` has parameters *and* an index, the hardest shape in this tutorial.
    env, _ = replay("04")
    lean = {d.name: d for d in load_trace(trace_path("04")) if d.kind == "recursor"}["Eq.rec"]
    ours = env.get("Eq.rec")
    assert ours.universe_params == lean.universe_params == ("u_1", "u")
    assert erase_binder_names(ours.type) == erase_binder_names(lean.type)
    assert (ours.num_params, ours.num_indices, ours.num_minors) == (2, 1, 1)


def test_refl_proves_what_computes():
    env, _ = replay("04")
    checker = TypeChecker(env)
    two, four = Const("MyNat.two"), Const("MyNat.four")
    # Eq.refl four : four = four, and that *is* `two + two = four` after computing.
    assert checker.is_def_eq(checker.infer(refl(four)), eq(add(two, two), four))
    assert not checker.is_def_eq(checker.infer(refl(four)), eq(add(two, two), two))


def test_refl_cannot_prove_zero_add():
    # `add zero a` is stuck: `add` recurses on its second argument, and `a` is
    # a variable. So `Eq.refl a` must NOT be accepted as a proof of
    # `add zero a = a`, even though `Eq.refl a` does prove `add a zero = a`.
    env, _ = replay("04")
    decls = declarations("04")
    by_refl = Lam("a", "default", Const("MyNat"), refl(BVar(0)))
    add_definition(env, "add_zero_again", (), decls["MyNat.add_zero"].type, by_refl, "theorem")
    with pytest.raises(KernelError):
        add_definition(env, "zero_add_by_refl", (), decls["MyNat.zero_add"].type, by_refl, "theorem")


def test_wrong_proofs_are_rejected():
    env, _ = replay("04")
    decls = declarations("04")
    with pytest.raises(KernelError):
        add_definition(env, "bad1", (), decls["MyNat.succ_add"].type, decls["MyNat.zero_add"].value, "theorem")
    with pytest.raises(KernelError):
        add_definition(env, "bad2", (), decls["Eq.symm"].type, decls["Eq.trans"].value, "theorem")
    # one = two is false.
    with pytest.raises(KernelError):
        claim = eq(Const("MyNat.one"), Const("MyNat.two"))
        add_definition(env, "bad3", (), claim, refl(Const("MyNat.one")), "theorem")


def test_a_theorem_must_state_a_proposition():
    env, _ = replay("04")
    with pytest.raises(KernelError):
        add_definition(env, "bad", (), Const("MyNat"), zero, "theorem")


def test_proof_irrelevance():
    # Two different-looking proofs of the same proposition are definitionally equal.
    env, _ = replay("04")
    checker = TypeChecker(env)
    a = Const("MyNat.one")
    direct = mk_app(Const("MyNat.add_zero"), [a])  # : add one zero = one
    assert checker.is_def_eq(direct, refl(a))


def test_eta():
    env, _ = replay("04")
    checker = TypeChecker(env)
    succ = Const("MyNat.succ")
    expanded = Lam("n", "default", Const("MyNat"), App(succ, BVar(0)))
    assert checker.is_def_eq(expanded, succ)
