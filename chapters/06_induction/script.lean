/-
Chapter 6 script: induction over MyNat proves succ_add.
-/

theorem succ_add : forall a b : MyNat, succ a + b = succ (a + b) :=
  fun a b =>
    MyNat.ind
      (fun b => succ a + b = succ (a + b))
      rfl
      (fun n ih => rw ih)
      b
