/-
Phase 3 script: equality, computation, and rewrites.
-/

theorem add_zero : forall a : Nat, a + zero = a :=
  fun a => rfl

theorem add_succ : forall a n : Nat, a + succ n = succ (a + n) :=
  fun a n => rfl

theorem rewrite_step :
    forall a n : Nat,
      (succ a + n = succ (a + n)) ->
      succ a + succ n = succ (succ (a + n)) :=
  fun a n ih => congr_succ ih
