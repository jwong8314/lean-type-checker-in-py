set_option pp.all true
set_option pp.universes true
set_option pp.explicit true
set_option pp.notation false

theorem false_implies_true (h : False) : True := by
  contradiction

theorem or_swap (h : Or True False) : Or False True := by
  cases h with
  | inl x =>
      exact Or.inr x
  | inr y =>
      exact Or.inl y

theorem cases_with_contradiction (h : Or False True) : True := by
  cases h with
  | inl h =>
      contradiction
  | inr x =>
      exact x

#check false_implies_true
#check or_swap
#check cases_with_contradiction

