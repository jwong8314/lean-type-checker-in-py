inductive True : Prop where
  | intro : True

def True.recOn.{u} : ∀ {motive : True → Sort u} (t : True), motive intro → motive t :=
  fun motive t intro => True.rec intro t

inductive False : Prop where

def False.recOn.{u} : ∀ (motive : False → Sort u) (t : False), motive t :=
  fun motive t => False.rec motive t

def TrueProp : Prop :=
  True

theorem true_intro : TrueProp :=
  True.intro

theorem true_is_true : TrueProp :=
  true_intro

