/-
Chapter 4 script: introduce `rfl` as syntax elaborated into a reflexivity proof.
-/

theorem rfl_nat : forall x : MyNat, x = x :=
  fun x => rfl

theorem rfl_zero : zero = zero := by
  rfl

theorem rfl_one_unfolds : succ zero = one := by
  rfl

theorem explicit_refl_one_unfolds : succ zero = one :=
  refl MyNat one
