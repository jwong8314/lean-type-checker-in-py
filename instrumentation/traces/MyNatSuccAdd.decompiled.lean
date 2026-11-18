def TrueProp : Prop :=
  True

theorem true_intro : TrueProp :=
  True.intro

theorem true_is_true : TrueProp :=
  true_intro

inductive MyNat : Type where
  | zero : MyNat
  | succ : MyNat → MyNat

def MyNat.recOn.{u} : ∀ {motive : MyNat → Sort u} (t : MyNat), motive zero → (∀ (a : MyNat), motive a → motive (succ a)) → motive t :=
  fun motive t zero succ => MyNat.rec zero succ t

def MyNat.casesOn.{u} : ∀ {motive : MyNat → Sort u} (t : MyNat), motive zero → (∀ (a : MyNat), motive (succ a)) → motive t :=
  fun motive t zero succ => MyNat.rec zero (fun a a_ih => succ a) t

def MyNat.ctorIdx : MyNat → Nat :=
  fun x => MyNat.casesOn (motive := fun x_1 => Nat) x 0 (fun a => 1)

def MyNat.ctorElimType.{u} : ∀ {motive : MyNat → Sort u}, Nat → Sort (max 1 u) :=
  fun motive ctorIdx =>
    cond (Nat.ble ctorIdx 0) (PULift (motive zero)) (PULift (∀ (a : MyNat), motive (succ a)))

def MyNat.ctorElim.{u} : ∀ {motive : MyNat → Sort u} (ctorIdx : Nat) (t : MyNat), ctorIdx = MyNat.ctorIdx t → MyNat.ctorElimType ctorIdx → motive t :=
  fun motive ctorIdx t h k =>
    MyNat.casesOn
      (motive := fun t_1 => ctorIdx = MyNat.ctorIdx t_1 → motive t_1)
      t
      (fun h_1 => PULift.down (Eq.ndrec k h_1))
      (fun a h_1 => PULift.down (Eq.ndrec k h_1) a)
      h

def zero.elim.{u} : ∀ {motive : MyNat → Sort u} (t : MyNat), MyNat.ctorIdx t = 0 → motive zero → motive t :=
  fun motive t h zero => MyNat.ctorElim 0 t (Eq.symm h) (PULift.up zero)

def succ.elim.{u} : ∀ {motive : MyNat → Sort u} (t : MyNat), MyNat.ctorIdx t = 1 → (∀ (a : MyNat), motive (succ a)) → motive t :=
  fun motive t h succ => MyNat.ctorElim 1 t (Eq.symm h) (PULift.up succ)

def MyNat.noConfusionType.{u} : Sort u → MyNat → MyNat → Sort u :=
  fun P t t' =>
    MyNat.casesOn
      (motive := fun t_1 => Sort u)
      t
      (MyNat.casesOn (motive := fun t_1 => Sort u) t' (P → P) (fun a => P))
      (fun a => MyNat.casesOn (motive := fun t_1 => Sort u) t' P (fun a_1 => (a = a_1 → P) → P))

def MyNat.noConfusion.{u} : ∀ {P : Sort u} {t t' : MyNat}, t = t' → MyNat.noConfusionType P t t' :=
  fun P t t' eq =>
    Eq.ndrec
      (motive := fun t'_1 => MyNat.noConfusionType P t t'_1)
      (MyNat.casesOn
        (motive := fun t_1 => MyNat.noConfusionType P t_1 t_1)
        t
        (fun k => k)
        (fun a k => k (Eq.refl a)))
      eq

def MyNat.succ.noConfusion.{u} : ∀ {P : Sort u} {a a' : MyNat}, succ a = succ a' → (a = a' → P) → P :=
  fun P a a' eq k => id (MyNat.noConfusion eq k)

def MyNat.below.{u} : ∀ {motive : MyNat → Sort u}, MyNat → Sort (max 1 u) :=
  fun motive t =>
    MyNat.rec (motive := fun t_1 => Sort (max 1 u)) PUnit (fun a a_ih => PProd (motive a) a_ih) t

def brecOn.go.{u} : ∀ {motive : MyNat → Sort u} (t : MyNat), (∀ (t_1 : MyNat), MyNat.below t_1 → motive t_1) → PProd (motive t) (MyNat.below t) :=
  fun motive t F_1 =>
    MyNat.rec
      (motive := fun t_1 => PProd (motive t_1) (MyNat.below t_1))
      (PProd.mk (F_1 zero PUnit.unit) PUnit.unit)
      (fun a a_ih => PProd.mk (F_1 (succ a) a_ih) a_ih)
      t

def MyNat.brecOn.{u} : ∀ {motive : MyNat → Sort u} (t : MyNat), (∀ (t_1 : MyNat), MyNat.below t_1 → motive t_1) → motive t :=
  fun motive t F_1 => (brecOn.go t F_1).1

theorem brecOn.eq.{u} : ∀ {motive : MyNat → Sort u} (t : MyNat) (F_1 : ∀ (t_1 : MyNat), MyNat.below t_1 → motive t_1), MyNat.brecOn t F_1 = F_1 t (brecOn.go t F_1).2 :=
  fun motive t F_1 =>
    MyNat.casesOn
      (motive := fun x => MyNat.brecOn x F_1 = F_1 x (brecOn.go x F_1).2)
      t
      (Eq.refl (MyNat.brecOn zero F_1))
      (fun a => Eq.refl (MyNat.brecOn (succ a) F_1))

def _sizeOf_1 : MyNat → Nat :=
  fun t => MyNat.rec (motive := fun t_1 => Nat) 1 (fun a a_ih => 1 + a_ih) t

def _sizeOf_inst : SizeOf MyNat :=
  SizeOf.mk (fun m => _sizeOf_1 m)

theorem zero.sizeOf_spec : SizeOf.sizeOf zero = 1 :=
  Eq.refl 1

theorem succ.sizeOf_spec : ∀ (a : MyNat), SizeOf.sizeOf (succ a) = 1 + SizeOf.sizeOf a :=
  fun a => Eq.refl (1 + SizeOf.sizeOf a)

theorem succ.inj : ∀ {a a_1 : MyNat}, succ a = succ a_1 → a = a_1 :=
  fun a a_1 x => MyNat.succ.noConfusion x (fun a_eq => a_eq)

theorem succ.injEq : ∀ (a a_1 : MyNat), (succ a = succ a_1) = (a = a_1) :=
  fun a a_1 =>
    Eq.propIntro succ.inj (Eq.ndrec (motive := fun a_2 => succ a = succ a_2) (Eq.refl (succ a)))

def repr.match_1.{u_1} : ∀ (motive : MyNat → Sort u_1) (x : MyNat), (Unit → motive MyNat.zero) → (∀ (a : MyNat), motive (MyNat.succ a)) → motive x :=
  fun motive x h_1 h_2 =>
    MyNat.casesOn (motive := fun x_1 => motive x_1) x (h_1 Unit.unit) (fun a => h_2 a)

def repr : MyNat → Nat → Std.Format :=
  fun x prec => MyNat.brecOn (motive := fun x_1 => Nat → Std.Format) x repr._f prec

def repr._f : ∀ (x : MyNat), MyNat.below (motive := fun x_1 => Nat → Std.Format) x → Nat → Std.Format :=
  fun x f prec =>
    repr.match_1
      (fun x_1 => MyNat.below (motive := fun x_2 => Nat → Std.Format) x_1 → Std.Format)
      x
      (fun _ x_1 =>
        Repr.addAppParen
          (Std.Format.group
            (Std.Format.nest (ite (GE.ge prec 1024) 1 2) (Std.Format.text "MyNat.zero"))
            Std.Format.FlattenBehavior.allOrNone)
          prec)
      (fun a x_1 =>
        Repr.addAppParen
          (Std.Format.group
            (Std.Format.nest
              (ite (GE.ge prec 1024) 1 2)
              (HAppend.hAppend (HAppend.hAppend (Std.Format.text "MyNat.succ") Std.Format.line) (x_1.1 1024)))
            Std.Format.FlattenBehavior.allOrNone)
          prec)
      f

def repr._unsafe_rec : MyNat → Nat → Std.Format :=
  fun x prec =>
    repr.match_1
      (fun x_1 => Std.Format)
      x
      (fun _ =>
        Repr.addAppParen
          (Std.Format.group
            (Std.Format.nest (ite (GE.ge prec 1024) 1 2) (Std.Format.text "MyNat.zero"))
            Std.Format.FlattenBehavior.allOrNone)
          prec)
      (fun a =>
        Repr.addAppParen
          (Std.Format.group
            (Std.Format.nest
              (ite (GE.ge prec 1024) 1 2)
              (HAppend.hAppend
                (HAppend.hAppend (Std.Format.text "MyNat.succ") Std.Format.line)
                (repr._unsafe_rec a 1024)))
            Std.Format.FlattenBehavior.allOrNone)
          prec)

def repr._sunfold : MyNat → Nat → Std.Format :=
  fun x prec =>
    repr.match_1
      (fun x_1 => Std.Format)
      x
      (fun _ =>
        Repr.addAppParen
          (Std.Format.group
            (Std.Format.nest (ite (GE.ge prec 1024) 1 2) (Std.Format.text "MyNat.zero"))
            Std.Format.FlattenBehavior.allOrNone)
          prec)
      (fun a =>
        Repr.addAppParen
          (Std.Format.group
            (Std.Format.nest
              (ite (GE.ge prec 1024) 1 2)
              (HAppend.hAppend (HAppend.hAppend (Std.Format.text "MyNat.succ") Std.Format.line) (repr a 1024)))
            Std.Format.FlattenBehavior.allOrNone)
          prec)

def instReprMyNat : Repr MyNat :=
  Repr.mk instReprMyNat.repr

def add.match_1.{u_1} : ∀ (motive : MyNat → MyNat → Sort u_1) (x x_1 : MyNat), (∀ (a : MyNat), motive a zero) → (∀ (a b : MyNat), motive a (succ b)) → motive x x_1 :=
  fun motive x x_1 h_1 h_2 =>
    MyNat.casesOn (motive := fun x_2 => motive x x_2) x_1 (h_1 x) (fun a => h_2 x a)

def add._f : ∀ (x : MyNat), MyNat.below (motive := fun x_1 => MyNat → MyNat) x → MyNat → MyNat :=
  fun x f x_1 =>
    add.match_1
      (fun x_2 x_3 => MyNat.below (motive := fun x_4 => MyNat → MyNat) x_3 → MyNat)
      x_1
      x
      (fun a x_2 => a)
      (fun a b x_2 => succ (x_2.1 a))
      f

def add : MyNat → MyNat → MyNat :=
  fun x x_1 => MyNat.brecOn (motive := fun x_2 => MyNat → MyNat) x_1 add._f x

def add._unsafe_rec : MyNat → MyNat → MyNat :=
  fun x x_1 =>
    add.match_1 (fun x_2 x_3 => MyNat) x x_1 (fun a => a) (fun a b => succ (add._unsafe_rec a b))

def add._sunfold : MyNat → MyNat → MyNat :=
  fun x x_1 => add.match_1 (fun x_2 x_3 => MyNat) x x_1 (fun a => a) (fun a b => succ (add a b))

def instAdd : Add MyNat :=
  Add.mk add

theorem my_add_zero : ∀ (a : MyNat), a + zero = a :=
  fun a => Eq.refl (a + zero)

theorem my_add_succ : ∀ (a b : MyNat), a + succ b = succ (a + b) :=
  fun a b => Eq.refl (a + succ b)

theorem succ_add_succ : ∀ (a b : MyNat), succ a + b = succ (a + b) → succ a + succ b = succ (succ (a + b)) :=
  fun a b ih =>
    Eq.mpr
      (id (congrArg (fun _a => _a = succ (succ (a + b))) (my_add_succ (succ a) b)))
      (Eq.mpr (id (congrArg (fun _a => succ _a = succ (succ (a + b))) ih)) (Eq.refl (succ (succ (a + b)))))

theorem succ_add : ∀ (a b : MyNat), succ a + b = succ (a + b) :=
  fun a b =>
    MyNat.rec
      (motive := fun b_1 => succ a + b_1 = succ (a + b_1))
      (Eq.mpr
        (id (congrArg (fun _a => _a = succ (a + zero)) (my_add_zero (succ a))))
        (Eq.mpr (id (congrArg (fun _a => succ a = succ _a) (my_add_zero a))) (Eq.refl (succ a))))
      (fun n ih => succ_add_succ a n ih)
      b

theorem zero_add : ∀ (a : MyNat), zero + a = a :=
  fun a =>
    MyNat.rec
      (motive := fun a_1 => zero + a_1 = a_1)
      (Eq.refl (zero + zero))
      (fun n ih =>
        Eq.mpr
          (id (congrArg (fun _a => _a = succ n) (my_add_succ zero n)))
          (Eq.mpr (id (congrArg (fun _a => succ _a = succ n) ih)) (Eq.refl (succ n))))
      a

theorem add_comm : ∀ (a b : MyNat), a + b = b + a :=
  fun a b =>
    MyNat.rec
      (motive := fun b_1 => a + b_1 = b_1 + a)
      (Eq.mpr
        (id (congrArg (fun _a => _a = zero + a) (my_add_zero a)))
        (Eq.mpr (id (congrArg (fun _a => a = _a) (zero_add a))) (Eq.refl a)))
      (fun n ih =>
        Eq.mpr
          (id (congrArg (fun _a => _a = succ n + a) (my_add_succ a n)))
          (Eq.mpr
            (id (congrArg (fun _a => succ (a + n) = _a) (succ_add n a)))
            (Eq.mpr (id (congrArg (fun _a => succ _a = succ (n + a)) ih)) (Eq.refl (succ (n + a))))))
      b

theorem add_assoc : ∀ (a b c : MyNat), a + b + c = a + (b + c) :=
  fun a b c =>
    MyNat.rec
      (motive := fun c_1 => a + b + c_1 = a + (b + c_1))
      (Eq.mpr
        (id (congrArg (fun _a => _a = a + (b + zero)) (my_add_zero (a + b))))
        (Eq.mpr (id (congrArg (fun _a => a + b = a + _a) (my_add_zero b))) (Eq.refl (a + b))))
      (fun n ih =>
        Eq.mpr
          (id (congrArg (fun _a => _a = a + (b + succ n)) (my_add_succ (a + b) n)))
          (Eq.mpr
            (id (congrArg (fun _a => succ (a + b + n) = a + _a) (my_add_succ b n)))
            (Eq.mpr
              (id (congrArg (fun _a => succ _a = a + succ (b + n)) ih))
              (Eq.mpr
                (id (congrArg (fun _a => succ (a + (b + n)) = _a) (my_add_succ a (b + n))))
                (Eq.refl (succ (a + (b + n))))))))
      c

theorem add_right_comm : ∀ (a b c : MyNat), a + b + c = a + c + b :=
  fun a b c =>
    Eq.mpr
      (id (congrArg (fun _a => _a = a + c + b) (add_assoc a b c)))
      (Eq.mpr
        (id (congrArg (fun _a => a + _a = a + c + b) (add_comm b c)))
        (Eq.mpr (id (congrArg (fun _a => _a = a + c + b) (Eq.symm (add_assoc a c b)))) (Eq.refl (a + c + b))))

