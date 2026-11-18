inductive MyNat : Type where
  | zero : MyNat
  | succ : MyNat → MyNat

def MyNat.recOn.{u} : ∀ {motive : MyNat → Sort u} (t : MyNat), motive zero → (∀ (a : MyNat), motive a → motive (succ a)) → motive t :=
  fun motive t zero succ => MyNat.rec zero succ t

inductive Eq : ∀ {α : Sort u}, α → α → Prop where
  | refl : ∀ {α : Sort u} (a : α), a = a

def Eq.recOn.{u_1, u} : ∀ {α : Sort u} {a : α} {motive : ∀ (a_1 : α), a = a_1 → Sort u_1} {a_1 : α} (t : a = a_1), motive a (refl a) → motive a_1 t :=
  fun α a motive a_1 t refl => Eq.rec refl t

theorem symm.{u} : ∀ {α : Sort u} {a b : α}, a = b → b = a :=
  fun α a b h => Eq.rec (motive := fun x x_1 => x = a) (refl a) h

theorem trans.{u} : ∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c :=
  fun α a b c h₁ h₂ => Eq.rec (motive := fun x x_1 => a = x) h₁ h₂

theorem congrArg.{u, v} : ∀ {α : Sort u} {β : Sort v} {a b : α} (f : α → β), a = b → f a = f b :=
  fun α β a b f h => Eq.rec (motive := fun x x_1 => f a = f x) (refl (f a)) h

def add : MyNat → MyNat → MyNat :=
  fun a b => MyNat.rec (motive := fun x => MyNat) a (fun x ih => succ ih) b

def one : MyNat :=
  succ zero

def two : MyNat :=
  succ one

def four : MyNat :=
  succ (succ two)

theorem two_add_two : add two two = four :=
  Eq.refl four

theorem add_zero : ∀ (a : MyNat), add a zero = a :=
  fun a => Eq.refl a

theorem add_succ : ∀ (a b : MyNat), add a (succ b) = succ (add a b) :=
  fun a b => Eq.refl (succ (add a b))

theorem zero_add : ∀ (a : MyNat), add zero a = a :=
  fun a =>
    MyNat.rec (motive := fun n => add zero n = n) (Eq.refl zero) (fun n ih => Eq.congrArg succ ih) a

theorem succ_add : ∀ (a b : MyNat), add (succ a) b = succ (add a b) :=
  fun a b =>
    MyNat.rec
      (motive := fun n => add (succ a) n = succ (add a n))
      (Eq.refl (succ a))
      (fun n ih => Eq.congrArg succ ih)
      b

theorem add_comm : ∀ (a b : MyNat), add a b = add b a :=
  fun a b =>
    MyNat.rec
      (motive := fun n => add a n = add n a)
      (Eq.symm (zero_add a))
      (fun n ih => Eq.trans (Eq.congrArg succ ih) (Eq.symm (succ_add n a)))
      b

