/-
Phase 2 script: MyNat is declared as a recursive type, not a built-in.
-/

inductive MyNat : Type where
| zero : MyNat
| succ : MyNat -> MyNat

def one : MyNat := succ zero
def two : MyNat := succ one
