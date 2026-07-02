/-
Phase 4: induction over the recursive Nat declaration.

The target theorem is not closed by rfl, because Nat.add recurses on the second
argument.  The kernel checks an explicit induction proof over b:

  base: rfl
  step: fun n ih => congr_succ ih
-/

#kernel phase 4

#kernel reject by_rfl : forall a b : Nat, succ a + b = succ (a + b)
#kernel check succ_add : forall a b : Nat, succ a + b = succ (a + b)
