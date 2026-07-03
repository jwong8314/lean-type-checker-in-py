theorem my_add_zero : forall a : MyNat, a + zero = a :=
  add_zero

theorem my_add_succ : forall a b : MyNat, a + succ b = succ (a + b) :=
  add_succ

theorem succ_add_succ
    (a b : MyNat)
    (ih : succ a + b = succ (a + b)) :
    succ a + succ b = succ (succ (a + b)) := by
  rw [my_add_succ]
  rw [ih]

theorem succ_add (a b : MyNat) : succ a + b = succ (a + b) := by
  induction b with
  | zero =>
      rw [my_add_zero, my_add_zero]
  | succ n ih =>
      exact succ_add_succ a n ih

theorem zero_add (a : MyNat) : zero + a = a := by
  induction a with
  | zero =>
      rfl
  | succ n ih =>
      rw [my_add_succ, ih]

theorem add_comm (a b : MyNat) : a + b = b + a := by
  induction b with
  | zero =>
      rw [my_add_zero, zero_add]
  | succ n ih =>
      rw [my_add_succ, succ_add, ih]

theorem add_assoc (a b c : MyNat) : a + b + c = a + (b + c) := by
  induction c with
  | zero =>
      rw [my_add_zero, my_add_zero]
  | succ n ih =>
      rw [my_add_succ, my_add_succ, ih, my_add_succ]

theorem add_right_comm (a b c : MyNat) : a + b + c = a + c + b := by
  rw [add_assoc, add_comm b c, ← add_assoc]
