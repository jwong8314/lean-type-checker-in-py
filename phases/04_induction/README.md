# Phase 4: Induction

Goal: use the recursive `Nat` declaration to derive an induction rule.

The theorem is:

```text
forall a b : Nat, succ a + b = succ (a + b)
```

This is not true by bare `rfl`, because `add` computes by recursion on the
second argument. The proof is by induction on `b`:

```text
base: rfl
step: fun n ih => rw ih
```

New implementation pieces:

1. `Induction(type_name, motive, cases, target)`.
2. A function that derives case types from recursive constructors.
3. A final proof term for `succ_add`.

Try it:

```bash
python3 -B tutorial_type_checker.py 04
```
