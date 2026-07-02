/-
Phase 2: natural numbers are introduced as a recursive type declaration.

This is not a built-in Nat.  The Python kernel registers exactly this
declaration:

  inductive Nat : Type where
  | zero : Nat
  | succ : Nat -> Nat

The constructor types are derived from the recursive declaration.
-/

#kernel phase 2

#kernel inductive Nat : Type where
#kernel | zero : Nat
#kernel | succ : Nat -> Nat

#kernel check Nat : Type
#kernel check zero : Nat
#kernel check succ : Nat -> Nat
#kernel check succ zero : Nat
#kernel check succ (succ zero) : Nat
