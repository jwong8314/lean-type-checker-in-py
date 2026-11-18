inductive MyNat : Type where
  | zero : MyNat
  | succ : MyNat -> MyNat
namespace MyNat
def add : MyNat -> MyNat -> MyNat
  | a, zero => a
  | a, succ b => succ (add a b)
instance : Add MyNat where
  add := add

theorem rewrite_step (a n : MyNat) (ih : succ a + n = succ (a + n)) :
    succ (succ a + n) = succ (succ (a + n)) := by
  rw [ih]

#print rewrite_step
set_option pp.explicit true in
#print rewrite_step
#check @Eq.mpr
#check @congrArg
#print Eq.mpr
#print axioms rewrite_step
end MyNat
