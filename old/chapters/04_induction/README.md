# Chapter 4: Induction

Goal: use the recursive `MyNat` declaration to derive an induction rule.

The theorem is:

```text
forall a b : MyNat, succ a + b = succ (a + b)
```

This is not true by bare `rfl`, because `add` computes by recursion on the
second argument. The proof is by induction on `b`:

```text
base: rewrite with add_zero on both sides
step: rewrite with add_succ, use ih, then rewrite with add_succ on the right
```

New implementation pieces:

1. `Induction(type_name, motive, cases, target)`.
2. A function that derives case types from recursive constructors.
3. Equality symmetry/transitivity proof objects, which model the chain that
   `rw` builds before the type checker sees the proof.
4. A final proof term for `succ_add`.

Try it:

```bash
python3 -B -m pylean.tutorial_type_checker 04
```
