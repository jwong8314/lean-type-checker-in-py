# Chapter 3: Explicit Rewrites

Goal: build computation and rewriting one explicit proof term at a time.

Nothing in this chapter should feel like a hidden compiler default. Chapter 2
introduced equality proof objects; this script introduces each new computation
and rewrite ingredient before using it:

1. `add`, a `MyNat` function.
2. `add_zero a : a + zero = a`, the first named equation for addition.
3. `add_succ a b : a + succ b = succ (a + b)`, the second named equation.
4. `succ_congr`, the explicit proof constructor for rewriting under `succ`.
5. Theorems that use those pieces.

The addition equations are:

```text
add a zero     --> a
add a (succ b) --> succ (add a b)
```

So `add : MyNat -> MyNat -> MyNat` is just the shape of the function. Its
behavior is introduced by `add_zero` and `add_succ`: those are the only
equations we are allowed to cite when we want to change an addition expression.

The important strictness point is that the checker does not silently identify
`a + zero` with `a`. Equality checking in this chapter is exact structural
equality. If the goal contains `a + zero`, the proof must explicitly use
`add_zero a`.

This chapter intentionally avoids tactic elaboration. Its script is already in
the proof-term form the kernel checks. For example, instead of writing `rw h`,
it writes `succ_congr h`, which parses directly to `SuccCongr(h)`.

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
