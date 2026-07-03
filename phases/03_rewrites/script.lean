/-
Phase 3 script: build equality, addition, computation, and rewrites piece by
piece. Nothing here is a compiler default.
-/

constant Eq : Type -> MyNat -> MyNat -> Prop

theorem rfl_nat : forall x : MyNat, Eq MyNat x x :=
  fun x => rfl

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
      x = y ->
      succ x = succ y :=
  fun x y h => rw h

theorem add_zero_by_rfl : forall a : MyNat, a + zero = a :=
  fun a => rfl

theorem add_succ_by_rfl : forall a n : MyNat, a + succ n = succ (a + n) :=
  fun a n => rfl

theorem rewrite_step :
    forall a n : MyNat,
      (succ a + n = succ (a + n)) ->
      succ a + succ n = succ (succ (a + n)) :=
  fun a n ih => rw ih
