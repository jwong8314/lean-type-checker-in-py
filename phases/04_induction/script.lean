/-
Phase 4 script: induction over Nat proves succ_add.
-/

theorem succ_add : forall a b : Nat, succ a + b = succ (a + b) :=
  fun a b =>
    Nat.ind
      (fun b => succ a + b = succ (a + b))
      rfl
      (fun n ih => rw ih)
      b
