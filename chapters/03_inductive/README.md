# Chapter 3: Inductive Types

Goal: stop taking `inductive` on faith. Accept this, and build what it implies:

```lean
inductive MyNat : Type where
  | zero : MyNat
  | succ : MyNat → MyNat

def add (a b : MyNat) : MyNat :=
  @MyNat.rec (fun _ => MyNat) a (fun _ ih => succ ih) b
```

This is the largest chapter. You will edit `kernel/level.py`,
`kernel/subst.py`, `kernel/inductive.py`, and `kernel/typechecker.py`.

```bash
pytest tests/test_ch3_inductive.py
```

## 1. What The Kernel Receives

```text
[kernel-trace] inductive MyNat
  params: 0
  type:
    Sort 1
[kernel-trace] end MyNat
[kernel-trace] constructor MyNat.zero
  type:
    Const MyNat
[kernel-trace] end MyNat.zero
[kernel-trace] constructor MyNat.succ
  type:
    Pi a._@._internal._hyg.0 (default)
      Const MyNat
      Const MyNat
[kernel-trace] end MyNat.succ
```

That is all Lean sends: a type, a parameter count, and the constructors'
types. From it the kernel must produce a fourth constant by itself, the
**recursor**:

```lean
MyNat.rec.{u} :
  {motive : MyNat → Sort u} →
  (zero : motive MyNat.zero) →
  (succ : (a : MyNat) → motive a → motive (MyNat.succ a)) →
  (t : MyNat) → motive t
```

and its **computation rules**:

```text
MyNat.rec zero_case succ_case MyNat.zero      ~>  zero_case
MyNat.rec zero_case succ_case (MyNat.succ n)  ~>  succ_case n (MyNat.rec zero_case succ_case n)
```

The recursor is the only way to use a value of an inductive type. It is
induction and recursion at once: with `motive n := MyNat` it defines
functions, with `motive n := some proposition about n` it proves theorems.
Pattern matching, `match`, structural recursion, and the `induction` tactic
all compile to it (Chapter 5).

The trace also contains Lean's own recursor, as a `reference recursor` block.
The tests compare yours with it node for node, for six different types.

## 2. Universe Parameters

`MyNat.rec.{u}` works for a motive in any universe `u`. Such a constant is
*universe polymorphic*, and every use of it supplies levels:

```text
[kernel-trace] definition id
  universe params: u
  type:
    Pi α (implicit)
      Sort u
      ...
```

A use looks like `Const id [1]` in a trace, `Const("id", (Succ(Zero()),))` in
Python. Three things to do:

1. `instantiate_level` (in `level.py`) and `instantiate_level_params` (in
   `subst.py`): substitute levels for parameters.
2. The `Const` case of `infer`: the number of levels must match the number of
   `universe_params`; substitute them into the constant's type. Do the same to
   the value in `unfold_definition`.
3. `leq` with parameters. A parameter is only `≤` itself (plus `diff ≥ 0`),
   and `Zero ≤ Param`. `IMax(_, Param p)` is the hard case: the value depends
   on whether `p` is zero. Substitute `p := 0` and `p := p + 1` and require
   the answer to hold in both.

`check_level` (given) rejects a level that mentions a parameter the current
declaration did not declare.

## 3. Checking The Declaration

`add_inductive(env, decl, constructors)` in `kernel/inductive.py`. The file's
docstring has the general shape with parameters and indices. Work in this
order, and test with `MyNat` (no parameters, no indices) before the others.

**Step 1, the type.** Walk the `Pi`s of `decl.type`, creating an `FVar` for
each. The first `num_params` are parameters, the rest are indices, and what
remains must be a `Sort`. Then add the type to `env`, because the
constructors mention it.

**Step 2, each constructor.** Its type is `(params) → (fields) → I params indices`.

- Instantiate its first `num_params` binders with *your* parameter `FVar`s,
  so every constructor talks about the same parameters.
- Each remaining `Pi` is a field. Make an `FVar` for it.
- What is left must be the inductive type applied to exactly the parameters,
  then some index arguments.
- A field is **recursive** when its type is the inductive type itself (in
  general: `(xs) → I params indices`). `recursive_field` decides this.

**Step 3, safety checks.** These are what stop an `inductive` declaration from
proving `False`:

- *Strict positivity.* The type being defined may not appear to the left of
  an arrow inside a field. `inductive Bad | mk : (Bad → False) → Bad` must be
  rejected.
- *Universe size.* A field's type must live in a universe no larger than the
  inductive type's own, unless the inductive type is a `Prop`.
  `inductive Bad : Type | mk : Type → Bad` must be rejected.

## 4. Building The Recursor

With `FVar`s for the parameters, indices, and fields in hand, build:

```text
major    t      : I params indices
motive   motive : (indices) → (t : I params indices) → Sort u
minor_i         : (fields_i) → (ih for each recursive field) → motive idx_i (c_i params fields_i)
                  where ih for a field `f : I params idx` has type `motive idx f`

I.rec : (params) → (motive) → (minors) → (indices) → (t) → motive indices t
```

`mk_pi(fvars, body)` (given, in `subst.py`) builds `Π fvars, body` and turns
the free variables back into bound ones for you. Finish with
`infer_implicit(rec_type)` (given), which reproduces Lean's choice of which
arguments are implicit.

**Which universe?** Normally the motive returns `Sort u` for a fresh
parameter `u`, listed *first* in the recursor's universe parameters. If the
inductive type already uses the name `u`, use `u_1`.

The exception is the heart of `Prop`. Proofs carry no data: any two proofs of
a proposition are equal. So a recursor must not let you compute data by
inspecting a proof. For `Or a b`, you must not be able to ask *which* side
holds and return a different `MyNat` for each. The rule,
`elim_only_at_universe_zero`:

```text
the type is not a Prop                     -> any universe
it has no constructors                     -> any universe      (False)
it has two or more constructors            -> Prop only         (Or)
it has one constructor, and every field is
  a proof, or appears in the result's indices -> any universe   (And, True, Eq)
otherwise                                  -> Prop only         (Exists)
```

When the answer is "Prop only", the motive returns `Sort 0` and the recursor
gets no new universe parameter.

## 5. Computation

For each constructor, store one rule: a function taking the parameters, the
motive, the minors, and that constructor's fields, and returning the
right-hand side.

```text
rule_i = fun params motive minors fields_i =>
           minor_i fields_i (I.rec params motive minors idx f) ...
                             └ one recursive call per recursive field f ┘
```

`mk_lambda` builds it the same way `mk_pi` builds types.

Then, in `typechecker.py`, `reduce_recursor(head, args)`:

1. `head` must be a `Const` naming a recursor.
2. The major premise is argument number
   `num_params + 1 + num_minors + num_indices`. If there are not that many
   arguments, return `None`.
3. `whnf` the major premise (full `whnf`: it may need unfolding to become
   visible). If its head is not a constructor of this type, return `None`.
   The term is stuck, which is normal when the major premise is a variable.
4. Take that constructor's rule, substitute the recursor's universe levels,
   and apply it to: the parameters, motive, and minors; then the constructor's
   fields (its arguments after the parameters); then any arguments that came
   after the major premise.

Call it from `whnf_core` when the head of an application is not a `Lam`.
Beta reduction then finishes the job.

`one_plus_two` now computes: the test checks it is definitionally equal to
`three`.

## 6. `rules`, `k`, and what to skip

`ConstantInfo` has a `k` flag. Set it when the type is a `Prop` with exactly
one constructor and that constructor has no fields. It matters in Chapter 4.

This kernel does not support mutual or nested inductive types, where the
recursive occurrence is inside another type such as `List Tree`. Lean's kernel
does, by translating them to the form you are implementing. Raise a
`KernelError` if you meet one.

## Hints

<details>
<summary>Hint 1: get <code>MyNat</code> working first</summary>

With no parameters and no indices, half of each formula disappears. Compare
your `MyNat.rec` type against the `reference recursor MyNat.rec` block in the
trace by eye, using [examples.decompiled.lean](examples.decompiled.lean) or
`python3 instrumentation/decompile.py chapters/03_inductive/examples.trace --only MyNat.rec`.
Then `And` (parameters, no recursion), then `Prod` (universe parameters).

</details>

<details>
<summary>Hint 2: use free variables for everything</summary>

Do not compute de Bruijn indices by hand. Create an `FVar` for every
parameter, index, field, the motive, each minor, and the major premise. Write
every type in terms of those objects with `mk_app`. Call `mk_pi` and
`mk_lambda` once at the end.

</details>

<details>
<summary>Hint 3: the minor premise for <code>succ</code></summary>

```python
field = FVar("a", Const("MyNat"))
ih    = FVar("a_ih", App(motive, field))
result = App(motive, App(Const("MyNat.succ"), field))
minor = FVar("succ", mk_pi([field, ih], result))
```

In general there is one `ih` per recursive field, and they come after *all*
the fields.

</details>

<details>
<summary>Hint 4: the recursor does not reduce</summary>

Check, in order: is `reduce_recursor` being called at all (is the head a
`Const` and not a `Lam`)? Is the major premise index right? Did you `whnf`
the major premise, or only `whnf_core` it? `one_plus_two` is a defined
constant, so its constructor only appears after unfolding.

</details>

## In Lean's Source

| Here | [cpp-lean-kernel/src/kernel](../../cpp-lean-kernel/src/kernel) |
| --- | --- |
| `add_inductive` | `add_inductive_fn` in `inductive.cpp` |
| step 2, positivity | `check_constructors`, `check_positivity` |
| elimination universe | `elim_only_at_universe_zero` |
| recursor type | `mk_rec_infos`, `declare_recursors` |
| rules | `mk_rec_rules` |
| `reduce_recursor` | `inductive_reduce_rec` in `inductive.h` |
