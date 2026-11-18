# What The Sugar Hides

Every simple example in this repository, run through real Lean, captured at
the kernel, and decompiled back to text. The source is
[MyNatSuccAdd.lean](../MyNatSuccAdd.lean) (66 lines); the raw trees are in
[traces/MyNatSuccAdd.trace](traces/MyNatSuccAdd.trace) (about 21,500 lines,
most of it the standard library definitions the file depends on); the
full decompiled listing is
[traces/MyNatSuccAdd.decompiled.lean](traces/MyNatSuccAdd.decompiled.lean).

Regenerate any of it with:

```bash
LEAN_KERNEL_TRACE='*' lean4-src/build/release/stage1/bin/lean MyNatSuccAdd.lean 2> out.trace
python3 instrumentation/decompile.py out.trace
python3 instrumentation/roundtrip.py MyNatSuccAdd.lean
```

## The Short Answer

Yes: this tree

```text
HAdd.hAdd MyNat MyNat MyNat (instHAdd MyNat MyNat.instAdd) a zero
```

is exactly `a + zero` with type inference filled in. The constant's type says
which arguments are which:

```lean
HAdd.hAdd : ∀ {α : Type u} {β : Type v} {γ : outParam (Type w)} [self : HAdd α β γ], α → β → γ
```

| Argument | Binder | Who supplies it |
| --- | --- | --- |
| `MyNat`, `MyNat`, `MyNat` | `{α} {β} {γ}` implicit | unification, from the types of `a` and `zero` |
| `instHAdd MyNat MyNat.instAdd` | `[self]` instance | type class search |
| `a`, `zero` | explicit | you |

Only the last two are information. The decompiler drops the rest and writes
the two that remain around `+`.

## How The Decompiler Decides

[decompile.py](decompile.py) does not guess what is sugar. For each
application it looks up the head constant's type and reads the binder
annotations:

- `(x : T)` explicit: print the argument.
- `{x : T}` implicit, `[x : T]` instance: drop it.
- Exception: an implicit argument that is itself a `fun` is printed as a named
  argument, `(motive := fun b => ...)`. Unification cannot invent a function,
  so real Lean needs these written out too.
- If the application stops right before an implicit binder, hiding would
  change its meaning, so it is printed in full with `@`.

The types come from the trace itself: the kernel patch prints a `reference`
block for every constant a declaration mentions. The decompiler's
only built-in knowledge is two small tables: which constants print as infix
operators (`HAdd.hAdd` as `+`, `Eq` as `=`, ...) and which generated helper
names are `protected`.

Other presentation choices: de Bruijn indices become the binder's name, a
`Pi` whose body ignores its variable becomes `→`, `Sort 0` is `Prop` and
`Sort 1` is `Type`, universe levels are hidden, and `fun` binder types are
omitted. `--explicit` turns all hiding off.

## Is The Short Text Really Equivalent?

[roundtrip.py](roundtrip.py) tests it. It decompiles each declaration, appends
the text to the original file as a new declaration, runs Lean again, and
compares the two kernel trees node by node (ignoring binder names).

A pass means Lean's elaborator rebuilt the identical tree from the short text
alone, so nothing that was hidden was information.

```text
declaration           tree nodes  text chars  result
TrueProp                       2          29  PASS
true_intro                     2          45  PASS
true_is_true                   2          47  PASS
MyNat.add                     22         112  PASS
MyNat.my_add_zero             48          82  PASS
MyNat.my_add_succ             74         101  PASS
MyNat.succ_add_succ          736         328  PASS
MyNat.succ_add               510         391  PASS
MyNat.zero_add               426         350  PASS
MyNat.add_comm              1254         591  PASS
MyNat.add_assoc             2722         823  PASS
MyNat.add_right_comm        1434         356  PASS
MyNat.rewrite_step           448         230  PASS
```

`MyNat.add` is marked `noncomputable` in the test: Lean generates executable
code from the equations you wrote, not from the kernel term, and refuses to
compile the term form.

## The Examples, One Kind Of Sugar At A Time

### 1. No sugar: `True`

```lean
def TrueProp : Prop := True
theorem true_intro : TrueProp := True.intro
```

Kernel tree, complete:

```text
type:   Const TrueProp
value:  Const True.intro
```

Source and tree are the same thing. This is why Chapter 1 can be fully
faithful with almost no machinery.

### 2. `inductive`: one line, twenty-three declarations

```lean
inductive MyNat : Type where
  | zero : MyNat
  | succ : MyNat -> MyNat
```

The kernel receives the type and its two constructors, and builds the
recursor itself:

```lean
MyNat.rec : ∀ {motive : MyNat → Sort u},
  motive zero → (∀ (a : MyNat), motive a → motive (succ a)) → ∀ (t : MyNat), motive t
```

Lean then sends twenty more helper declarations defined in terms of
`MyNat.rec`: `recOn`, `casesOn`, `below`, `brecOn`, `noConfusion`,
`succ.inj`, `succ.injEq`, size-of lemmas, and others. `deriving Repr` adds six
more. Of all these, the rest of the file uses only `MyNat.rec`, `casesOn`,
`below`, and `brecOn`.

### 3. `def` by pattern matching: equations become a recursor call

```lean
def add : MyNat -> MyNat -> MyNat
  | a, zero => a
  | a, succ b => succ (add a b)
```

The kernel has no pattern matching and no recursion. It receives three
definitions:

```lean
def add.match_1 : ∀ (motive : MyNat → MyNat → Sort u_1) (x x_1 : MyNat),
    (∀ (a : MyNat), motive a zero) → (∀ (a b : MyNat), motive a (succ b)) → motive x x_1 :=
  fun motive x x_1 h_1 h_2 =>
    MyNat.casesOn (motive := fun x_2 => motive x x_2) x_1 (h_1 x) (fun a => h_2 x a)

def add._f : ∀ (x : MyNat), MyNat.below (motive := fun x_1 => MyNat → MyNat) x → MyNat → MyNat :=
  fun x f x_1 =>
    add.match_1
      (fun x_2 x_3 => MyNat.below (motive := fun x_4 => MyNat → MyNat) x_3 → MyNat)
      x_1 x
      (fun a x_2 => a)
      (fun a b x_2 => succ (x_2.1 a))
      f

def add : MyNat → MyNat → MyNat :=
  fun x x_1 => MyNat.brecOn (motive := fun x_2 => MyNat → MyNat) x_1 add._f x
```

- `add.match_1` is the `match`, compiled to `casesOn`.
- `add._f` is one step of the recursion. The recursive call `add a b` became
  `x_2.1 a`: a lookup in a table of results for smaller inputs.
- `add` ties the knot with `brecOn`, which is built from `MyNat.rec`.

Before sending these, the elaborator sends `add` as a temporary `axiom`
several times while it works out the recursion.

### 4. `instance` and `+`: type classes

```lean
instance : Add MyNat where
  add := add
```

```lean
def instAdd : Add MyNat :=
  Add.mk add
```

An instance is an ordinary definition building an ordinary structure. `a + b`
then becomes `HAdd.hAdd MyNat MyNat MyNat (instHAdd MyNat MyNat.instAdd) a b`,
as above. To compute with it the kernel must unfold its way through the
instances to `add`, then through `brecOn`, and finally reach `MyNat.rec`.

### 5. `rfl`: the proof is one node, the work is in the kernel

```lean
theorem my_add_zero (a : MyNat) : a + zero = a := by
  rfl
```

```lean
theorem my_add_zero : ∀ (a : MyNat), a + zero = a :=
  fun a => Eq.refl (a + zero)
```

`Eq.refl (a + zero)` has type `a + zero = a + zero`, not `a + zero = a`. The
kernel accepts it by computing `a + zero` down to `a` through the whole chain
in the previous section. Note also that theorem parameters before the colon
are sugar for `∀`, and `fun` introduces them.

### 6. `rw`: each rewrite is one `Eq.mpr`

```lean
theorem succ_add_succ (a b : MyNat) (ih : succ a + b = succ (a + b)) :
    succ a + succ b = succ (succ (a + b)) := by
  rw [my_add_succ]
  rw [ih]
```

```lean
theorem succ_add_succ : ∀ (a b : MyNat), succ a + b = succ (a + b) → succ a + succ b = succ (succ (a + b)) :=
  fun a b ih =>
    Eq.mpr
      (id (congrArg (fun _a => _a = succ (succ (a + b))) (my_add_succ (succ a) b)))
      (Eq.mpr
        (id (congrArg (fun _a => succ _a = succ (succ (a + b))) ih))
        (Eq.refl (succ (succ (a + b)))))
```

Two rewrites, two nested `Eq.mpr`, then the `Eq.refl` that `rw` tries at the
end. `rw [my_add_succ]` named no arguments; the elaborator found
`(succ a)` and `b` by matching the pattern against the goal. This is 736 tree
nodes, almost all of them repeated copies of the goal with `+` expanded.

### 7. `induction`: a direct call to the recursor

```lean
theorem zero_add (a : MyNat) : zero + a = a := by
  induction a with
  | zero => rfl
  | succ n ih => rw [my_add_succ, ih]
```

```lean
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
```

`induction a` is `MyNat.rec` with the goal abstracted over `a` as the motive,
one argument per case, then `a`.

### 8. `exact`, `←`: nothing new

`exact e` contributes `e` itself. `rw [← h]` is `rw` with `Eq.symm h`:

```lean
Eq.mpr (id (congrArg (fun _a => _a = a + c + b) (Eq.symm (add_assoc a c b)))) (Eq.refl (a + c + b))
```

## What A Faithful Checker Needs

Everything the kernel receives for `add` and the theorems is built from the
node kinds `Const`, `App`, `Lam`, `Pi`, `BVar`, and `Sort`, plus `Proj` in the
compiled recursion (`add._f` and `brecOn`). Literals and metadata appear only
in the `deriving Repr` and size-of helpers. To check the real traces a checker
needs:

1. Those node kinds, with de Bruijn indices and substitution.
2. Universe levels with parameters (`Sort u`, `max`, `succ`), because `Eq`,
   `MyNat.rec`, and `HAdd.hAdd` are universe-polymorphic.
3. Inductive types: generating the recursor and its computation rule.
4. Definitional equality with unfolding (delta), beta, the recursor rule
   (iota), and structure projection. `my_add_zero` cannot pass without all four.

It does not need tactics, pattern matching, type classes, implicit arguments,
or notation. Those are gone before the kernel is called.

## Size Of Everything

`tree nodes` counts type plus value.

```text
declaration                     tree nodes  decompiled chars
TrueProp                                 2                29
true_intro                               2                45
true_is_true                             2                47
MyNat                                    5                70
MyNat.recOn                             56               184
MyNat.casesOn                           56               193
MyNat.ctorIdx                           18               103
MyNat.ctorElimType                      38               199
MyNat.ctorElim                         140               384
MyNat.zero.elim                         70               181
MyNat.succ.elim                         82               202
MyNat.noConfusionType                   62               317
MyNat.noConfusion                       92               352
MyNat.succ.noConfusion                  76               151
MyNat.below                             34               192
MyNat.brecOn.go                        124               362
MyNat.brecOn                            47               167
MyNat.brecOn.eq                        128               383
MyNat._sizeOf_1                         52               107
MyNat._sizeOf_inst                      12                69
MyNat.zero.sizeOf_spec                  34                64
MyNat.succ.sizeOf_spec                  84               130
MyNat.succ.inj                          64               129
MyNat.succ.injEq                        88               186
instReprMyNat.repr.match_1              62               262
instReprMyNat.repr                      22               122
instReprMyNat.repr._f                  257               792
instReprMyNat.repr._unsafe_rec         204               707
instReprMyNat.repr._sunfold            207               660
instReprMyNat                            8                62
MyNat.add.match_1                       88               281
MyNat.add._f                            89               301
MyNat.add                               22               112
MyNat.add._unsafe_rec                   36               159
MyNat.add._sunfold                      39               140
MyNat.instAdd                            8                39
MyNat.my_add_zero                       48                82
MyNat.my_add_succ                       74               101
MyNat.succ_add_succ                    736               328
MyNat.succ_add                         510               391
MyNat.zero_add                         426               350
MyNat.add_comm                        1254               591
MyNat.add_assoc                       2722               823
MyNat.add_right_comm                  1434               356
```
