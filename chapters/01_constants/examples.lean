/-
Chapter 1 examples. `prelude` means "import nothing": every constant this
file uses is declared in this file.
-/
prelude

inductive True : Prop where
  | intro : True

inductive False : Prop

def TrueProp : Prop := True

theorem true_intro : TrueProp := True.intro

theorem true_is_true : TrueProp := true_intro
