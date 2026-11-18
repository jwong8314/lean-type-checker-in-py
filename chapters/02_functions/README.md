# Chapter 2: Functions

Goal: check proofs that are functions.

```lean
theorem id_proof : ∀ (p : Prop), p → p :=
  fun p h => h

theorem modus_ponens : ∀ (p q : Prop), (p → q) → p → q :=
  fun p q f h => f h
```

Under propositions-as-types, a proof of "`p` implies `q`" is a function from
proofs of `p` to proofs of `q`, and a proof of "for all `p`" is a function of
`p`. So this chapter is the lambda calculus: `Pi`, `Lam`, `App`, `BVar`.

You will edit `kernel/subst.py`, `kernel/level.py`, and
`kernel/typechecker.py`.

```bash
pytest tests/test_ch2_functions.py
```

## 1. What The Kernel Receives

```text
[kernel-trace] theorem id_proof
  type:
    Pi p (default)
      Sort 0
      Pi a._@._internal._hyg.0 (default)
        BVar 0
        BVar 1
  value:
    Lam p (default)
      Sort 0
      Lam h (default)
        BVar 0
        BVar 0
[kernel-trace] end id_proof
```

- `Pi name (binder)` has two children: the domain and the body. It is the type
  of functions. Both `∀ (p : Prop), ...` and `p → p` are `Pi`; an arrow is a
  `Pi` whose body does not use the variable. Lean made up the name
  `a._@._internal._hyg.0` for it.
- `Lam name (binder)` has the same two children and is `fun`.
- `App` has two children: a function and one argument. `f a b` is
  `App(App(f, a), b)`.
- `BVar n` is a variable. There are no variable names in the tree.

`(default)` is the binder annotation. The kernel carries it along and never
looks at it; Chapter 5 explains what it is for.

## 2. Bound Variables Are Numbers

`BVar n` means "the variable bound by the `n`th enclosing binder, counting
outward from zero". Read the type of `id_proof` again:

```text
Pi p            <- binder A
  Sort 0
  Pi _          <- binder B
    BVar 0      domain of B: we are inside A only, so 0 means A, i.e. p
    BVar 1      body of B:   inside A and B, so 0 is B and 1 is A, i.e. p
```

The same variable `p` is `BVar 0` in one place and `BVar 1` in another. This
is the de Bruijn representation. Its payoff is that two terms which differ
only in variable names are the same tree, so the kernel never renames
anything.

Its cost is that you cannot look at `BVar 0` out of context and know what it
is. The kernel's rule is therefore: **never look inside a binder without
replacing its variable first.**

- `instantiate(body, value)` replaces the variable of the binder that `body`
  sits under with `value`.
- When there is no value to substitute, because you only want to look at the
  body, invent a fresh free variable: `FVar(name, type)`. It stands for "some
  arbitrary thing of this type". Each `FVar` is equal only to itself.
- `abstract(expr, fvar)` goes back: it replaces that free variable with the
  right `BVar`.

```text
instantiate( App(BVar 0, BVar 0),            x )  =  App(x, x)
instantiate( Lam y. App(BVar 1, BVar 0),     x )  =  Lam y. App(x, BVar 0)
```

In the second line the variable we want is `BVar 1`, because we went under
one more binder to reach it. `BVar 0` there belongs to `y` and is left alone.

## 3. The Typing Rules

| Expression | Its type | Conditions |
| --- | --- | --- |
| `FVar` | the type stored in it | |
| `Pi x : A, B` | `Sort (imax u v)` | `A : Sort u`, and `B : Sort v` with `x` replaced by a fresh `FVar` |
| `Lam x : A, b` | `Pi x : A, B` | `A` is a type, and `b : B` with `x` replaced by a fresh `FVar` |
| `App f a` | `B` with `x := a` | `f : Pi x : A, B`, and the type of `a` is definitionally equal to `A` |

For `Lam`, after inferring the body's type `B` you hold a term containing your
`FVar`. Use `abstract` to turn it back into the body of a `Pi`.

For `App`, the function's type might not look like a `Pi` until it is reduced
(see `implies_refl` below). `ensure_pi` is `whnf` followed by a check.

`imax` is the one new idea about universes:

```text
imax u v  =  0          if v = 0
             max u v    otherwise
```

It says: a function *into a proposition* is a proposition, no matter how big
its domain. That is why `∀ (p : Prop), p → p` is a `Prop`, although it
quantifies over all of `Prop : Type`.

## 4. Reduction

`whnf_core` now does real work. Weak head normal form means: reduce just
enough that the outermost node is settled.

**Beta.** A function applied to an argument computes:

```text
App(Lam x : A, b,  a)   ~>   instantiate(b, a)
```

With several arguments, `f a b` is `App(App(f, a), b)`, so the `Lam` is at the
bottom of a chain. `spine(expr)` gives you `(head, [args])`; reduce the head,
and if it is a `Lam`, feed it arguments one at a time.

**Delta** you already have in `whnf`: after `whnf_core`, try
`unfold_definition`; if it fires, go round again. Extend `unfold_definition`
to handle a defined constant applied to arguments: unfold the head, keep the
arguments.

Why both are needed:

```lean
def Implies (p q : Prop) : Prop := p → q

theorem implies_refl : ∀ (p : Prop), Implies p p :=
  fun p h => h
```

The value has type `p → p`. The declared type is `App(App(Const Implies, p), p)`.
Delta turns `Implies` into `Lam p, Lam q, Pi _ : p, q`; two beta steps turn the
application into `Pi _ : p, p`.

## 5. Definitional Equality, Properly

Replace Chapter 1's `is_def_eq` with this structure:

```text
is_def_eq(t, s):
  1. identical trees                          -> True
  2. t, s = whnf_core(t), whnf_core(s)
  3. both Sort                                -> levels equivalent
     both Pi, or both Lam                     -> domains equal, and bodies equal
                                                 after instantiating both with
                                                 the SAME fresh FVar
  4. if either side has a definition at its head: unfold, whnf_core, go to 3
  5. both Const                               -> same name
     both FVar                                -> same object
     both App                                 -> same head and all arguments equal
  6. otherwise                                -> False
```

Do not compute full normal forms and compare. It is correct, and far too slow
once definitions get large: the real kernel unfolds as little as it can
("lazy delta reduction") and so should you.

## 6. Universe Levels, Part One

`kernel/level.py` compares levels. In this chapter every level is built from
`Zero`, `Succ`, `Max`, and `IMax`; Chapter 3 adds `Param`. Implement
`simplify`, `leq`, and `is_equiv` now. The docstring of `simplify` lists the
identities to apply, and `is_equiv(a, b)` is `leq(a, b) and leq(b, a)`.

`leq(a, b, diff)` answers "is `a ≤ b + diff`?". Peeling a `Succ` off the left
lowers `diff` by one; peeling one off the right raises it.

With levels in place, fix `is_prop` from Chapter 1: the type of a proposition
is `Sort l` where `l` *is equivalent to* zero. `Sort(IMax(Succ(Zero()), Zero()))`
is `Prop`, and is not the same tree as `Sort(Zero())`.

## What Must Be Rejected

- applying something that is not a function;
- applying a function to an argument of the wrong type;
- a correct proof offered for a different theorem;
- `fun p q h => h` as a proof of `∀ p q, p → q`.

## Hints

<details>
<summary>Hint 1: <code>instantiate</code> needs a depth</summary>

Carry a `depth` argument, starting at 0, and add one each time you step into
the *body* of a `Lam`, `Pi`, or `Let` (not the domain). Replace `BVar(i)` when
`i == depth`.

</details>

<details>
<summary>Hint 2: the <code>Lam</code> case of <code>infer</code></summary>

```python
self.ensure_sort(self.infer(domain))
fvar = FVar(name, domain, info)
body_type = self.infer(instantiate(body, fvar))
return Pi(name, info, domain, abstract(body_type, fvar))
```

</details>

<details>
<summary>Hint 3: comparing two binders</summary>

Make one `FVar` and instantiate *both* bodies with it. If you make two, the
bodies can never be equal, because two free variables are never equal.

</details>

<details>
<summary>Hint 4: a first <code>leq</code></summary>

Simplify both sides, then match on the pair:

```text
(Zero, _)          diff >= 0
(_, Zero)          only if diff >= 0 and the left is Zero
(Succ a, _)        leq(a, b, diff - 1)
(_, Succ b)        leq(a, b, diff + 1)
(Max(a1, a2), _)   both leq(a1, b, diff) and leq(a2, b, diff)
(_, Max(b1, b2))   either leq(a, b1, diff) or leq(a, b2, diff)
```

After `simplify`, an `IMax` whose right side is a numeral is gone, so with no
parameters you will not meet `IMax` here.

</details>

## In Lean's Source

| Here | [cpp-lean-kernel/src/kernel](../../cpp-lean-kernel/src/kernel) |
| --- | --- |
| `instantiate` | `instantiate` in `instantiate.cpp` |
| `abstract` | `abstract` in `abstract.cpp` |
| `Pi`, `Lam`, `App` cases | `infer_pi`, `infer_lambda`, `infer_app` in `type_checker.cpp` |
| `whnf_core` | `type_checker::whnf_core` |
| `is_def_eq` | `type_checker::is_def_eq_core`, `lazy_delta_reduction` |
| `leq` | `is_geq_core` in `level.cpp` |
