inductive MyNat where
  | zero : MyNat
  | succ : MyNat -> MyNat

open MyNat

axiom add : MyNat -> MyNat -> MyNat
infixl:65 " + " => add

axiom add_zero : forall a : MyNat, a + zero = a
axiom add_succ : forall a b : MyNat, a + succ b = succ (a + b)

theorem rw :
    forall x y : MyNat,
      forall h : x = y,
      succ x = succ y :=
  fun x y h => congrArg succ h

theorem add_zero_from_rule : forall a : MyNat, a + zero = a :=
  fun a => add_zero a

theorem add_succ_from_rule : forall a n : MyNat, a + succ n = succ (a + n) :=
  fun a n => add_succ a n

theorem rewrite_step :
    forall a n : MyNat,
      forall ih : succ a + n = succ (a + n),
      succ (succ a + n) = succ (succ (a + n)) :=
  fun a n ih => congrArg succ ih

