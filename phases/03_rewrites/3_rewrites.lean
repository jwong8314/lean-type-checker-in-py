/-
Phase 3: equality, definitional computation, and a tiny rewrite principle.

Addition is declared over the recursive Nat type and gets the same direction
of computation as Lean's Nat.add:

  add a zero     --> a
  add a (succ b) --> succ (add a b)

The first two theorems below are checked by rfl because both sides become
definitionally equal.  The final line checks the step-shape rewrite used later:
from ih, congr_succ ih rewrites under succ.
-/

#kernel phase 3

#kernel check add_zero : forall a : Nat, a + zero = a
#kernel check add_succ : forall a n : Nat, a + succ n = succ (a + n)
#kernel check rewrite_step : forall a n : Nat, (succ a + n = succ (a + n)) -> succ a + succ n = succ (succ (a + n))
