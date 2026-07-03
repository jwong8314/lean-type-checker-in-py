/-
Phase 5 script: reuse Phase 4's succ_add theorem to build the usual
commutativity layer for our recursive Nat.
-/

theorem zero_add : forall a : Nat, zero + a = a :=
  fun a =>
    Nat.ind
      (fun a => zero + a = a)
      rfl
      (fun n ih => rw ih)
      a

theorem succ_add_succ : forall a b : Nat, succ a + succ b = succ (succ (a + b)) :=
  fun a b =>
    rw (succ_add a b)

theorem add_assoc : forall a b c : Nat, (a + b) + c = a + (b + c) :=
  fun a b c =>
    Nat.ind
      (fun c => (a + b) + c = a + (b + c))
      rfl
      (fun n ih => rw ih)
      c

theorem add_comm : forall a b : Nat, a + b = b + a :=
  fun a b =>
    Nat.ind
      (fun b => a + b = b + a)
      (symm (zero_add a))
      (fun n ih => trans (rw ih) (symm (succ_add n a)))
      b
