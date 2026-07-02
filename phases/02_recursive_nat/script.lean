/-
Phase 2 script: Nat is declared as a recursive type, not a built-in.
-/

inductive Nat : Type where
| zero : Nat
| succ : Nat -> Nat

def one : Nat := succ zero
def two : Nat := succ one
