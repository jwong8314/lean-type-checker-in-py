/-
Chapter 1 script: propositions are types, proofs are terms.
-/

constant True : Prop
constant False : Prop
constant true_intro : True

theorem true_is_true : True := true_intro
