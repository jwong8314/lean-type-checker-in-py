/-
Chapter 2 examples: functions, application, and bound variables.
-/
prelude

inductive False : Prop

theorem id_proof : ∀ (p : Prop), p → p :=
  fun p h => h

theorem modus_ponens : ∀ (p q : Prop), (p → q) → p → q :=
  fun p q f h => f h

theorem compose : ∀ (p q r : Prop), (p → q) → (q → r) → p → r :=
  fun p q r f g h => g (f h)

def Implies (p q : Prop) : Prop := p → q

def Not (p : Prop) : Prop := p → False

-- Accepted only by unfolding `Implies` and then beta-reducing.
theorem implies_refl : ∀ (p : Prop), Implies p p :=
  fun p h => h

theorem not_not_intro : ∀ (p : Prop), p → Not (Not p) :=
  fun p h notp => notp h

-- A function applied in a type: the checker must beta-reduce to compare.
theorem beta_in_type : ∀ (p : Prop), (fun (q : Prop) => q → q) p :=
  fun p h => h
