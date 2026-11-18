axiom lcErased : Type

axiom lcAny : Type

def id.{u} : ∀ {α : Sort u}, α → α :=
  fun α a => a

def const.{u, v} : ∀ {α : Sort u} {β : Sort v}, α → β → α :=
  fun α β a b => a

inductive False : Prop where

def False.recOn.{u} : ∀ (motive : False → Sort u) (t : False), motive t :=
  fun motive t => False.rec motive t

inductive True : Prop where
  | intro : True

def True.recOn.{u} : ∀ {motive : True → Sort u} (t : True), motive intro → motive t :=
  fun motive t intro => True.rec intro t

inductive And : Prop → Prop → Prop where
  | intro : ∀ {a b : Prop}, a → b → a ∧ b

def And.recOn.{u} : ∀ {a b : Prop} {motive : a ∧ b → Sort u} (t : a ∧ b), (∀ (a_1 : a) (a_2 : b), motive (intro a_1 a_2)) → motive t :=
  fun a b motive t intro => And.rec intro t

inductive Or : Prop → Prop → Prop where
  | inl : ∀ {a b : Prop}, a → a ∨ b
  | inr : ∀ {a b : Prop}, b → a ∨ b

def Or.recOn : ∀ {a b : Prop} {motive : a ∨ b → Prop} (t : a ∨ b), (∀ (a_1 : a), motive (inl a_1)) → (∀ (a_1 : b), motive (inr a_1)) → motive t :=
  fun a b motive t inl inr => Or.rec inl inr t

inductive MyNat : Type where
  | zero : MyNat
  | succ : MyNat → MyNat

def MyNat.recOn.{u} : ∀ {motive : MyNat → Sort u} (t : MyNat), motive zero → (∀ (a : MyNat), motive a → motive (succ a)) → motive t :=
  fun motive t zero succ => MyNat.rec zero succ t

inductive Prod : Type u → Type v → Sort ((max u v)+1) where
  | mk : ∀ {α : Type u} {β : Type v}, α → β → Prod α β

def Prod.recOn.{u_1, u, v} : ∀ {α : Type u} {β : Type v} {motive : Prod α β → Sort u_1} (t : Prod α β), (∀ (a : α) (a_1 : β), motive (mk a a_1)) → motive t :=
  fun α β motive t mk => Prod.rec mk t

def add : MyNat → MyNat → MyNat :=
  fun a b => MyNat.rec (motive := fun x => MyNat) a (fun x ih => succ ih) b

def one : MyNat :=
  succ zero

def two : MyNat :=
  succ one

def three : MyNat :=
  succ two

def one_plus_two : MyNat :=
  add one two

theorem elim : ∀ {p : Prop}, False → p :=
  fun p h => False.rec (fun x => p) h

theorem left : ∀ {a b : Prop}, a ∧ b → a :=
  fun a b h => And.rec (motive := fun x => a) (fun ha x => ha) h

theorem swap : ∀ {a b : Prop}, a ∧ b → b ∧ a :=
  fun a b h => And.rec (motive := fun x => b ∧ a) (fun ha hb => intro hb ha) h

theorem swap : ∀ {a b : Prop}, a ∨ b → b ∨ a :=
  fun a b h => Or.rec (motive := fun x => b ∨ a) (fun ha => inr ha) (fun hb => inl hb) h

def fst.{u, v} : ∀ {α : Type u} {β : Type v}, Prod α β → α :=
  fun α β p => Prod.rec (motive := fun x => α) (fun a x => a) p

