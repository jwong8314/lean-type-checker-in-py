/-
Chapter 3 script: build addition, computation, and rewrites piece by piece.
Equality and rfl were introduced in Chapter 2.
-/

/-
At this point `add` is only given its type.  That is sensible because the next
two declarations are the only introduction/computation rules for it: they say
what `add a zero` and `add a (succ b)` reduce to.
-/
def add : MyNat -> MyNat -> MyNat

def add_zero : forall a : MyNat, a + zero = a

def add_succ : forall a b : MyNat, a + succ b = succ (a + b)

theorem rw :
    forall x y : MyNat,
      forall h : x = y,
      succ x = succ y :=
  fun x y h => rw h

theorem add_zero_from_rule : forall a : MyNat, a + zero = a :=
  fun a => add_zero a

theorem add_succ_from_rule : forall a n : MyNat, a + succ n = succ (a + n) :=
  fun a n => add_succ a n

theorem rewrite_step :
    forall a n : MyNat,
      forall ih : succ a + n = succ (a + n),
      succ (succ a + n) = succ (succ (a + n)) :=
  fun a n ih => rw ih
