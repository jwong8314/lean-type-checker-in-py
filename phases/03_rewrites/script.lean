/-
Phase 3 script: build equality, addition, computation, and rewrites piece by
piece. Nothing here is a compiler default.
-/

constant Eq : Type -> Nat -> Nat -> Prop

theorem rfl_nat : forall x : Nat, Eq Nat x x :=
  fun x => rfl

/-
At this point `add` is only given its type.  That is sensible because the next
two declarations are the only introduction/computation rules for it: they say
what `add a zero` and `add a (succ b)` reduce to.
-/
def add : Nat -> Nat -> Nat

def add_zero : forall a : Nat, a + zero = a

def add_succ : forall a b : Nat, a + succ b = succ (a + b)

theorem congr_succ :
    forall x y : Nat,
      x = y ->
      succ x = succ y :=
  fun x y h => congr_succ h

theorem add_zero_by_rfl : forall a : Nat, a + zero = a :=
  fun a => rfl

theorem add_succ_by_rfl : forall a n : Nat, a + succ n = succ (a + n) :=
  fun a n => rfl

theorem rewrite_step :
    forall a n : Nat,
      (succ a + n = succ (a + n)) ->
      succ a + succ n = succ (succ (a + n)) :=
  fun a n ih => congr_succ ih
