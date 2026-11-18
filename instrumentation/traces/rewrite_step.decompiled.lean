theorem rewrite_step : ∀ (a n : MyNat), succ a + n = succ (a + n) → succ (succ a + n) = succ (succ (a + n)) :=
  fun a n ih =>
    Eq.mpr (id (congrArg (fun _a => succ _a = succ (succ (a + n))) ih)) (Eq.refl (succ (succ (a + n))))

