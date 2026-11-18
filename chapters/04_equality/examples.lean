/-
Chapter 4 examples: equality, proofs by computation, and proofs by induction.
Everything is written as an explicit term. There are no tactics here.
-/
prelude

universe u v

-- Skip code generation everywhere: this file is only about type checking.
noncomputable section

inductive MyNat : Type where
  | zero : MyNat
  | succ : MyNat → MyNat

inductive Eq {α : Sort u} : α → α → Prop where
  | refl (a : α) : Eq a a

namespace Eq

theorem symm {α : Sort u} {a b : α} (h : Eq a b) : Eq b a :=
  @Eq.rec α a (fun x _ => Eq x a) (Eq.refl a) b h

theorem trans {α : Sort u} {a b c : α} (h₁ : Eq a b) (h₂ : Eq b c) : Eq a c :=
  @Eq.rec α b (fun x _ => Eq a x) h₁ c h₂

theorem congrArg {α : Sort u} {β : Sort v} {a b : α} (f : α → β) (h : Eq a b) : Eq (f a) (f b) :=
  @Eq.rec α a (fun x _ => Eq (f a) (f x)) (Eq.refl (f a)) b h

end Eq

namespace MyNat

def add (a b : MyNat) : MyNat :=
  @MyNat.rec (fun _ => MyNat) a (fun _ ih => succ ih) b

def one : MyNat := succ zero
def two : MyNat := succ one
def four : MyNat := succ (succ two)

-- Proofs by computation: both sides reduce to the same term.
theorem two_add_two : Eq (add two two) four :=
  Eq.refl four

theorem add_zero (a : MyNat) : Eq (add a zero) a :=
  Eq.refl a

theorem add_succ (a b : MyNat) : Eq (add a (succ b)) (succ (add a b)) :=
  Eq.refl (succ (add a b))

-- Proofs by induction: `add zero a` is stuck, because `a` is a variable.
theorem zero_add (a : MyNat) : Eq (add zero a) a :=
  @MyNat.rec (fun n => Eq (add zero n) n)
    (Eq.refl zero)
    (fun n ih => Eq.congrArg succ ih)
    a

theorem succ_add (a b : MyNat) : Eq (add (succ a) b) (succ (add a b)) :=
  @MyNat.rec (fun n => Eq (add (succ a) n) (succ (add a n)))
    (Eq.refl (succ a))
    (fun n ih => Eq.congrArg succ ih)
    b

theorem add_comm (a b : MyNat) : Eq (add a b) (add b a) :=
  @MyNat.rec (fun n => Eq (add a n) (add n a))
    (Eq.symm (zero_add a))
    (fun n ih => Eq.trans (Eq.congrArg succ ih) (Eq.symm (succ_add n a)))
    b

end MyNat
