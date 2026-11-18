inductive False : Prop where

def False.recOn.{u} : ∀ (motive : False → Sort u) (t : False), motive t :=
  fun motive t => False.rec motive t

theorem id_proof : ∀ (p : Prop), p → p :=
  fun p h => h

theorem modus_ponens : ∀ (p q : Prop), (p → q) → p → q :=
  fun p q f h => f h

theorem compose : ∀ (p q r : Prop), (p → q) → (q → r) → p → r :=
  fun p q r f g h => g (f h)

def Implies : Prop → Prop → Prop :=
  fun p q => p → q

def Not : Prop → Prop :=
  fun p => p → False

theorem implies_refl : ∀ (p : Prop), Implies p p :=
  fun p h => h

theorem not_not_intro : ∀ (p : Prop), p → Not (Not p) :=
  fun p h notp => notp h

theorem beta_in_type : ∀ (p : Prop), (fun q => q → q) p :=
  fun p h => h

