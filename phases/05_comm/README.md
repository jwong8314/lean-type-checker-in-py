# Phase 5: Commutativity

Goal: accept the raw Lean script from `MyNatSuccAdd.lean` and check the same
declarations against our Python kernel.

This phase proves the same shape as `MyNatSuccAdd.lean`:

```text
MyNat          : Type
my_add_zero    : forall a : MyNat, a + zero = a
my_add_succ    : forall a b : MyNat, a + succ b = succ (a + b)
succ_add       : forall a b : MyNat, succ a + b = succ (a + b)
succ_add_succ  : forall a b : MyNat,
                 succ a + b = succ (a + b) ->
                 succ a + succ b = succ (succ (a + b))
zero_add       : forall a : MyNat, zero + a = a
add_comm       : forall a b : MyNat, a + b = b + a
add_assoc      : forall a b c : MyNat, (a + b) + c = a + (b + c)
add_right_comm : forall a b c : MyNat, a + b + c = a + c + b
```

New implementation pieces:

1. `EqSymm(proof)` flips an equality proof.
2. `EqTrans(left, right)` chains two equality proofs.
3. `EqCongrAddLeft(a, proof)` is the small congruence step needed by
   `add_right_comm`.
4. The checker declares a recursive type named `MyNat`, rather than reusing
   the earlier tutorial's `Nat` name.

The key `add_comm` proof follows the Lean proof:

```text
base: symm (zero_add a)
step: trans (rw ih) (symm (succ_add n a))
```

Try it:

```bash
python3 -B tutorial_type_checker.py 05
```
