# Phase 5: Commutativity

Goal: keep Phase 4 focused on the first interesting induction theorem,
`succ_add`, then use it here to build the familiar arithmetic layer.

This phase proves the same shape as `MyNatSuccAdd.lean`:

```text
zero_add      : forall a : Nat, zero + a = a
succ_add_succ : forall a b : Nat, succ a + succ b = succ (succ (a + b))
add_assoc     : forall a b c : Nat, (a + b) + c = a + (b + c)
add_comm      : forall a b : Nat, a + b = b + a
```

New implementation pieces:

1. `EqSymm(proof)` flips an equality proof.
2. `EqTrans(left, right)` chains two equality proofs.
3. The checker starts with Phase 4's `succ_add` in the environment, because
   this phase is about using that theorem rather than reproving it.

The key `add_comm` proof follows the Lean proof:

```text
base: symm (zero_add a)
step: trans (rw ih) (symm (succ_add n a))
```

Try it:

```bash
python3 -B tutorial_type_checker.py 05
```
