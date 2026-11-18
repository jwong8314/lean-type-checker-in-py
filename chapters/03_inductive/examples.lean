/-
Chapter 3 examples: inductive types, recursors, and universe parameters.
-/
prelude

universe u v

-- Skip code generation everywhere: this file is only about type checking.
noncomputable section

-- Two names Lean's code generator expects to find. They play no part in
-- type checking; without them `inductive` reports an error under `prelude`.
unsafe axiom lcErased : Type
unsafe axiom lcAny : Type

def id {α : Sort u} (a : α) : α := a

def const {α : Sort u} {β : Sort v} (a : α) (b : β) : α := a

inductive False : Prop

inductive True : Prop where
  | intro : True

inductive And (a b : Prop) : Prop where
  | intro : a → b → And a b

inductive Or (a b : Prop) : Prop where
  | inl : a → Or a b
  | inr : b → Or a b

inductive MyNat : Type where
  | zero : MyNat
  | succ : MyNat → MyNat

inductive Prod (α : Type u) (β : Type v) : Type (max u v) where
  | mk : α → β → Prod α β

namespace MyNat

def add (a b : MyNat) : MyNat :=
  @MyNat.rec (fun _ => MyNat) a (fun _ ih => succ ih) b

def one : MyNat := succ zero
def two : MyNat := succ one
def three : MyNat := succ two

def one_plus_two : MyNat := add one two

end MyNat

theorem False.elim {p : Prop} (h : False) : p :=
  @False.rec (fun _ => p) h

theorem And.left {a b : Prop} (h : And a b) : a :=
  @And.rec a b (fun _ => a) (fun ha _ => ha) h

theorem And.swap {a b : Prop} (h : And a b) : And b a :=
  @And.rec a b (fun _ => And b a) (fun ha hb => And.intro hb ha) h

theorem Or.swap {a b : Prop} (h : Or a b) : Or b a :=
  @Or.rec a b (fun _ => Or b a) (fun ha => Or.inr ha) (fun hb => Or.inl hb) h

def Prod.fst {α : Type u} {β : Type v} (p : Prod α β) : α :=
  @Prod.rec α β (fun _ => α) (fun a _ => a) p
