/-
Chapter 5 script: disjunctions, cases, and contradiction before induction.
-/

constant False : Prop
constant False.elim : forall p : Prop, False -> p
constant Or : Prop -> Prop -> Prop
constant Or.inl : forall p q : Prop, p -> Or p q
constant Or.inr : forall p q : Prop, q -> Or p q
constant Or.elim : forall p q r : Prop, Or p q -> forall left : p -> r, forall right : q -> r, r

theorem true_or_false : Or TrueProp False :=
  Or.inl TrueProp False true_intro

theorem false_or_true : Or False TrueProp :=
  Or.inr False TrueProp true_intro

theorem false_implies_true (h : False) : TrueProp := by
  contradiction

theorem or_swap (h : Or TrueProp False) : Or False TrueProp := by
  cases h with
  | inl x =>
      exact Or.inr False TrueProp x
  | inr y =>
      exact Or.inl False TrueProp y

theorem cases_with_contradiction (h : Or False TrueProp) : TrueProp := by
  cases h with
  | inl h =>
      contradiction
  | inr x =>
      exact x
