# Phase 3: Equality and Rewrites

Goal: build equality, computation, and rewriting one declaration at a time.

Nothing in this phase should feel like a hidden compiler default. The script
introduces each ingredient before using it:

1. `Eq`, the equality proposition former.
2. `rfl_nat`, reflexivity for natural-number equality.
3. `add`, a natural-number function.
4. `add_zero a : a + zero = a`, the first computation rule.
5. `add_succ a b : a + succ b = succ (a + b)`, the second computation rule.
6. `rw`, a tiny rewrite tactic/principle under `succ`.
7. Theorems that use those pieces.

The computation rules are:

```text
add a zero     --> a
add a (succ b) --> succ (add a b)
```

So `add : Nat -> Nat -> Nat` is just the shape of the function. Its behavior is
introduced by `add_zero` and `add_succ`: those are the only equations the
checker uses to reduce an addition expression.

The runner processes [script.lean](script.lean) in declaration order. In
`solution.py`, `register_declaration` updates the checker as each declaration
is reached, so later theorems only type-check because earlier declarations have
already been added.

Try it:

```bash
python3 -B tutorial_type_checker.py 03
```
