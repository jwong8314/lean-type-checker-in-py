/-
Chapter 5 script: disjunctions, cases, and contradiction before induction.
-/

constant False : Prop

theorem true_or_false : Or TrueProp False :=
  or_inl TrueProp False true_intro

theorem false_or_true : Or False TrueProp :=
  or_inr False TrueProp true_intro

theorem false_implies_true (h : False) : TrueProp := by
  contradiction

theorem or_swap (h : Or TrueProp False) : Or False TrueProp := by
  cases h with
  | inl x =>
      exact or_inr False TrueProp x
  | inr y =>
      exact or_inl False TrueProp y

theorem cases_with_contradiction (h : Or False TrueProp) : TrueProp := by
  cases h with
  | inl h =>
      contradiction
  | inr x =>
      exact x

