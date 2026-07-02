/-
Phase 1: propositions are types, proofs are terms.

Our tiny kernel begins with just:

  True : Prop
  true_intro : True
  False : Prop

There is no eliminator for False yet.  This phase only demonstrates that a
proof term must inhabit the proposition it claims to prove.
-/

#kernel phase 1

#kernel check True : Prop
#kernel check False : Prop
#kernel check true_intro : True
#kernel reject true_intro : False
