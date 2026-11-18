"""Chapter 5: the real `MyNatSuccAdd.lean`, tactics and all, and `rw` by hand."""

import pytest
from common import assert_all_checked, replay, trace_path

from kernel.environment import KernelError
from kernel.expr import App, BVar, Const, Expr, FVar, Lam, Pi, Succ, Zero, mk_app, spine
from kernel.rewrite import kabstract, mk_eq_mpr, rewrite
from kernel.subst import instantiate
from kernel.trace import load_trace
from kernel.typechecker import TypeChecker

USER_THEOREMS = {
    "MyNat.my_add_zero", "MyNat.my_add_succ", "MyNat.succ_add_succ", "MyNat.succ_add",
    "MyNat.zero_add", "MyNat.add_comm", "MyNat.add_assoc", "MyNat.add_right_comm",
}  # fmt: skip


@pytest.fixture(scope="module")
def chapter():
    return replay("05")


def test_real_trace_is_accepted(chapter):
    # Nothing here is simplified: pattern matching, `+` through type classes,
    # `rfl`, `rw`, and `induction`, exactly as Lean elaborated them.
    _, results = chapter
    assert_all_checked(results, USER_THEOREMS | {"MyNat", "MyNat.add", "MyNat.instAdd", "MyNat.brecOn"})


def test_imported_recursors_match_lean(chapter):
    # For every library inductive type the trace mentions, the recursor this
    # kernel generates must equal the one Lean ships.
    _, results = chapter
    compared = [r for r in results.values() if r.kind == "recursor" and r.status == "checked"]
    assert len(compared) >= 5
    assert {"Eq.rec", "MyNat.rec", "Nat.rec", "Bool.rec", "List.rec"} <= {r.name for r in compared}


def test_kabstract():
    a, b, f = Const("a"), Const("b"), Const("f")
    assert kabstract(App(f, a), a) == App(f, BVar(0))
    assert kabstract(mk_app(f, [a, b, a]), a) == mk_app(f, [BVar(0), b, BVar(0)])
    assert kabstract(App(f, b), a) == App(f, b)
    # Under a binder the new variable is one further out.
    under = Lam("x", "default", Const("T"), mk_app(f, [BVar(0), a]))
    assert kabstract(under, a) == Lam("x", "default", Const("T"), mk_app(f, [BVar(0), BVar(1)]))


def find_rewrites(expr: Expr, found: list) -> None:
    """Collect every `Eq.mpr goal new (id _ (congrArg ... h)) rest` in a proof.

    Binders are opened with free variables on the way down, so the pieces
    handed to `rewrite` contain no dangling bound variables.
    """

    head, args = spine(expr)
    if head == Const("Eq.mpr", (Zero(),)) and len(args) == 4:
        id_head, id_args = spine(args[2])
        if isinstance(id_head, Const) and id_head.name == "id":
            congr_head, congr_args = spine(id_args[1])
            if isinstance(congr_head, Const) and congr_head.name == "congrArg":
                found.append(
                    {"goal": args[0], "new_goal": args[1], "h": congr_args[5], "eq_proof": id_args[1],
                     "rest": args[3], "whole": expr}
                )  # fmt: skip
    match expr:
        case App(fn, arg):
            find_rewrites(fn, found)
            find_rewrites(arg, found)
        case Lam(name, info, domain, body) | Pi(name, info, domain, body):
            find_rewrites(domain, found)
            find_rewrites(instantiate(body, FVar(name, domain, info)), found)


def all_rewrites() -> list:
    found: list = []
    for decl in load_trace(trace_path("05")):
        if decl.name in USER_THEOREMS and decl.kind == "theorem":
            before = len(found)
            find_rewrites(decl.value, found)
            for i, rw in enumerate(found[before:]):
                rw["id"] = f"{decl.name}#{i}"
    return found


try:
    REWRITES = all_rewrites()
except NotImplementedError:  # `instantiate` (Chapter 2) is not written yet
    REWRITES = []


def test_trace_contains_rewrites():
    assert len(REWRITES) == 20


@pytest.mark.parametrize("rw", REWRITES, ids=[rw["id"] for rw in REWRITES])
def test_rewrite_matches_lean(chapter, rw):
    """Your `rw` must build, node for node, the term Lean's `rw` built."""

    env, _ = chapter
    checker = TypeChecker(env)
    new_goal, eq_proof = rewrite(checker, rw["goal"], rw["h"])
    assert new_goal == rw["new_goal"]
    assert eq_proof == rw["eq_proof"]
    assert mk_eq_mpr(checker, rw["goal"], new_goal, eq_proof, rw["rest"]) == rw["whole"]


def test_rewrite_result_type_checks(chapter):
    env, _ = chapter
    checker = TypeChecker(env)
    rw = REWRITES[0]
    new_goal, eq_proof = rewrite(checker, rw["goal"], rw["h"])
    expected = mk_app(Const("Eq", (Succ(Zero()),)), [checker.infer(rw["goal"]), rw["goal"], new_goal])
    assert checker.is_def_eq(checker.infer(eq_proof), expected)


def test_rewrite_fails_when_pattern_is_missing(chapter):
    env, _ = chapter
    checker = TypeChecker(env)
    rw = REWRITES[0]
    new_goal, _ = rewrite(checker, rw["goal"], rw["h"])
    with pytest.raises(KernelError):
        rewrite(checker, new_goal, rw["h"])  # the left-hand side is gone now


def test_rewrite_needs_an_equation(chapter):
    env, _ = chapter
    with pytest.raises(KernelError):
        rewrite(TypeChecker(env), REWRITES[0]["goal"], Const("MyNat.zero"))
