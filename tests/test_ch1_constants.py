"""Chapter 1: constants, sorts, and unfolding a definition."""

import pytest
from common import assert_all_checked, replay

from kernel.environment import KernelError
from kernel.expr import Const, Prop, Sort, Succ, Zero
from kernel.typechecker import TypeChecker, add_axiom, add_definition

MINE = {"TrueProp", "true_intro", "true_is_true"}


def test_real_trace_is_accepted():
    _, results = replay("01", only=MINE)
    assert_all_checked(results, MINE)


def test_infer_constant_and_sort():
    env, _ = replay("01", only=MINE)
    checker = TypeChecker(env)
    assert checker.infer(Const("True.intro")) == Const("True")
    assert checker.infer(Const("True")) == Prop
    assert checker.infer(Prop) == Sort(Succ(Zero()))  # Prop : Type


def test_definitions_unfold():
    env, _ = replay("01", only=MINE)
    checker = TypeChecker(env)
    assert checker.whnf(Const("TrueProp")) == Const("True")
    assert checker.is_def_eq(Const("TrueProp"), Const("True"))
    assert not checker.is_def_eq(Const("True"), Const("False"))


def test_unknown_constant_is_rejected():
    env, _ = replay("01", only=MINE)
    with pytest.raises(KernelError):
        TypeChecker(env).infer(Const("made_up_proof"))


def test_proposition_is_not_a_proof():
    # `False : Prop`, so `False` is not a proof of `TrueProp`.
    env, _ = replay("01", only=MINE)
    with pytest.raises(KernelError):
        add_definition(env, "bad", (), Const("TrueProp"), Const("False"), "theorem")


def test_no_proof_of_false():
    env, _ = replay("01", only=MINE)
    with pytest.raises(KernelError):
        add_definition(env, "bad", (), Const("False"), Const("True.intro"), "theorem")


def test_type_must_be_a_type():
    # `True.intro` is a proof, not a type, so nothing can have "type True.intro".
    env, _ = replay("01", only=MINE)
    with pytest.raises(KernelError):
        add_axiom(env, "bad", (), Const("True.intro"))


def test_redeclaration_is_rejected():
    env, _ = replay("01", only=MINE)
    with pytest.raises(KernelError):
        add_definition(env, "TrueProp", (), Prop, Const("False"))
