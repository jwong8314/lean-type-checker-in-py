# Chapter 3: Equality and Rewrites

Goal: build computation and rewriting one declaration at a time.

Nothing in this chapter should feel like a hidden compiler default. Chapter 2
introduced equality and `rfl`; this script introduces each new computation and
rewrite ingredient before using it:

1. `add`, a `MyNat` function.
2. `add_zero a : a + zero = a`, the first computation rule.
3. `add_succ a b : a + succ b = succ (a + b)`, the second computation rule.
4. `rw`, a tiny rewrite tactic/principle under `succ`.
5. Theorems that use those pieces.

The computation rules are:

```text
add a zero     --> a
add a (succ b) --> succ (add a b)
```

So `add : MyNat -> MyNat -> MyNat` is just the shape of the function. Its behavior is
introduced by `add_zero` and `add_succ`: those are the only equations the
checker uses to reduce an addition expression.

Tactics are not extra kernel rules. They are a small elaboration layer that
massages a proof script into an ordinary proof object before the type checker
sees it. In this chapter, `rfl` elaborates to a `Refl(...)` proof object, and
`rw h` elaborates to an `Rw(h)` proof object. After that point, the checker is
only checking expression trees, not tactic syntax.

That mirrors the important Lean idea: tactics help build proof terms, but the
kernel still only accepts or rejects the proof term that tactics produce.

The runner processes [script.lean](script.lean) in declaration order.
[solution_runner.py](../../solution_runner.py) updates the checker as each
declaration is reached, so later theorems only type-check because earlier
declarations have already been added.

Try it:

```bash
python3 -B -m pylean.tutorial_type_checker 03
```
