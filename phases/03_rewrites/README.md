# Phase 3: Equality and Rewrites

Goal: add just enough computation and equality to prove small rewrite lemmas.

New concepts:

1. `Lam` for proof terms like `fun a => ...`.
2. `Eq(A, lhs, rhs)` as a proposition.
3. `Refl(A, value)` as an equality proof.
4. Weak-head reduction for beta reduction and `Nat.add`.
5. Definitional equality: compare normalized expressions.
6. `CongSucc(ih)`, a tiny rewrite principle turning `ih : x = y` into
   `succ x = succ y`.

The important computation rules are:

```text
add a zero     --> a
add a (succ b) --> succ (add a b)
```

Try it:

```bash
python3 -B phases/03_rewrites/solution.py
```
