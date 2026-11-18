"""Chapter 3: universe levels, inductive types, recursors, and their computation."""

import pytest
from common import assert_all_checked, replay, trace_path

from kernel.environment import Environment, KernelError
from kernel.expr import App, Const, IMax, Lam, Max, Param, Pi, Succ, Type, Zero, erase_binder_names, mk_app
from kernel.inductive import add_inductive
from kernel.level import is_equiv, leq, simplify
from kernel.trace import Declaration, load_trace
from kernel.typechecker import TypeChecker

u, v = Param("u"), Param("v")
one = Succ(Zero())


def test_level_order():
    assert leq(Zero(), u)
    assert leq(u, Succ(u))
    assert not leq(Succ(u), u)
    assert leq(u, Max(u, v)) and leq(v, Max(u, v))
    assert not leq(Max(u, v), u)
    assert not leq(u, v)


def test_imax():
    # imax u 0 = 0: a function into a proposition is a proposition.
    assert is_equiv(IMax(u, Zero()), Zero())
    assert is_equiv(IMax(u, one), Max(u, one))
    assert is_equiv(IMax(Zero(), u), u)
    assert leq(IMax(u, v), Max(u, v))
    assert not is_equiv(IMax(u, v), Max(u, v))  # they differ when v = 0
    assert is_equiv(Max(u, v), Max(v, u))
    assert simplify(Max(Zero(), u)) == u


def test_real_trace_is_accepted():
    _, results = replay("03")
    assert_all_checked(results, {"MyNat", "And", "Prod", "MyNat.add", "And.swap", "Or.swap", "Prod.fst", "id"})


@pytest.mark.parametrize("name", ["False", "True", "And", "Or", "MyNat", "Prod"])
def test_generated_recursor_matches_lean(name):
    env, _ = replay("03")
    lean = {d.name: d for d in load_trace(trace_path("03")) if d.kind == "recursor"}[f"{name}.rec"]
    ours = env.get(f"{name}.rec")
    assert ours.kind == "recursor" and ours.rules is not None
    assert ours.universe_params == lean.universe_params
    assert erase_binder_names(ours.type) == erase_binder_names(lean.type)


def test_elimination_universe():
    env, _ = replay("03")
    # Data, and propositions with at most one "uninformative" constructor,
    # can be eliminated into any universe.
    for name in ("MyNat", "False", "True"):
        assert env.get(f"{name}.rec").universe_params == ("u",), name
    # `Prod` already uses the names u and v, so the new parameter is u_1, and it comes first.
    assert env.get("Prod.rec").universe_params == ("u_1", "u", "v")
    # `Or` has two constructors: a proof of `Or a b` must not reveal which.
    assert env.get("Or.rec").universe_params == ()
    # `And.intro` carries two proofs, which are themselves propositions: fine.
    assert env.get("And.rec").universe_params == ("u",)


def test_recursor_computes():
    env, _ = replay("03")
    checker = TypeChecker(env)
    succ = lambda n: App(Const("MyNat.succ"), n)  # noqa: E731
    three = succ(succ(succ(Const("MyNat.zero"))))
    assert checker.is_def_eq(Const("MyNat.one_plus_two"), Const("MyNat.three"))
    assert checker.is_def_eq(Const("MyNat.one_plus_two"), three)
    assert not checker.is_def_eq(Const("MyNat.one_plus_two"), Const("MyNat.two"))
    # whnf exposes exactly one constructor.
    head = checker.whnf(Const("MyNat.one_plus_two"))
    assert isinstance(head, App) and head.fn == Const("MyNat.succ")


def test_universe_polymorphic_constant():
    env, _ = replay("03")
    checker = TypeChecker(env)
    # id.{1} MyNat MyNat.zero : MyNat
    term = mk_app(Const("id", (one,)), [Const("MyNat"), Const("MyNat.zero")])
    assert checker.is_def_eq(checker.infer(term), Const("MyNat"))
    assert checker.is_def_eq(term, Const("MyNat.zero"))
    with pytest.raises(KernelError):
        checker.infer(Const("id"))  # missing its universe level
    with pytest.raises(KernelError):
        checker.infer(mk_app(Const("id", (Zero(),)), [Const("MyNat"), Const("MyNat.zero")]))  # MyNat is not a Prop


def bad_inductive(ctor_type) -> tuple[Declaration, list[Declaration]]:
    return (
        Declaration("inductive", "Bad", (), Type, num_params=0),
        [Declaration("constructor", "Bad.mk", (), ctor_type)],
    )


def test_non_positive_inductive_is_rejected():
    # inductive Bad | mk : (Bad → False) → Bad      -- would make `False` provable
    env, _ = replay("03")
    decl, ctors = bad_inductive(Pi("f", "default", Pi("x", "default", Const("Bad"), Const("False")), Const("Bad")))
    with pytest.raises(KernelError):
        add_inductive(env, decl, ctors)


def test_constructor_must_return_its_type():
    env, _ = replay("03")
    decl, ctors = bad_inductive(Const("MyNat"))
    with pytest.raises(KernelError):
        add_inductive(env, decl, ctors)


def test_field_universe_too_big():
    # inductive Bad : Type | mk : Type → Bad         -- a Type cannot hold all Types
    env = Environment()
    decl, ctors = bad_inductive(Pi("a", "default", Type, Const("Bad")))
    with pytest.raises(KernelError):
        add_inductive(env, decl, ctors)


def test_small_elimination_is_enforced():
    # Using `Or.rec` to compute a MyNat from a proof must fail: its motive is
    # fixed to return a `Prop`.
    env, _ = replay("03")
    checker = TypeChecker(env)
    a, b = Const("True"), Const("True")
    motive = Lam("_", "default", mk_app(Const("Or"), [a, b]), Const("MyNat"))
    with pytest.raises(KernelError):
        checker.infer(mk_app(Const("Or.rec"), [a, b, motive]))
