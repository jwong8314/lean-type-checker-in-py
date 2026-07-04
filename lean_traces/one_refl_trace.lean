inductive MyNat where
  | zero : MyNat
  | succ : MyNat -> MyNat

open MyNat

def one : MyNat := succ zero

set_option pp.all true
set_option pp.universes true
set_option pp.explicit true
set_option pp.notation false

#check (show @Eq MyNat (succ zero) one from rfl)
#check (show @Eq MyNat (succ zero) one from @Eq.refl MyNat one)

