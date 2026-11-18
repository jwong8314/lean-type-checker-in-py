# Chapter 4: Equality

Goal: prove things about `add`.

```lean
theorem add_zero (a : MyNat) : Eq (add a zero) a :=
  Eq.refl a

theorem zero_add (a : MyNat) : Eq (add zero a) a :=
  @MyNat.rec (fun n => Eq (add zero n) n)
    (Eq.refl zero)
    (fun n ih => Eq.congrArg succ ih)
    a
```

There is very little new code in this chapter. If Chapter 3 is right, most of
[examples.trace](examples.trace) already checks. The point is to see *why*
these two theorems, which look alike, need completely different proofs.

```bash
pytest tests/test_ch4_equality.py
```

## 1. Equality Is An Inductive Type

```lean
inductive Eq {α : Sort u} : α → α → Prop where
  | refl (a : α) : Eq a a
```

The kernel has no built-in notion of "equals" for the user. `a = b` is the
type `Eq a b`, and a proof of it is a value of that type. There is one
constructor, and it only builds proofs of `Eq a a`.

In the trace:

```text
[kernel-trace] inductive Eq
  universe params: u
  params: 2
  ...
```

Two parameters (`α` and the left-hand side `a`) and one **index**: the
right-hand side. This is the first type you have met with an index, and the
reason Chapter 3 asked you to handle them. Its recursor is the principle that
equals may be substituted for equals:

```lean
Eq.rec.{u_1, u} : {α : Sort u} → {a : α} →
  {motive : (b : α) → Eq a b → Sort u_1} →
  (refl : motive a (Eq.refl a)) →
  {b : α} → (t : Eq a b) → motive b t
```

"To prove something about any `b` equal to `a`, it is enough to prove it for
`a` itself."

Note the universe parameter is `u_1`, because `u` was taken, and that `Eq` is
a `Prop` with one constructor whose only non-parameter data, `b`, is an index:
so it eliminates into any universe.

`Eq.symm`, `Eq.trans`, and `Eq.congrArg` in [examples.lean](examples.lean) are
each a single use of `Eq.rec`. Read them; the `rw` tactic in Chapter 5 is
built from `congrArg`.

## 2. Proof By Computation

```lean
theorem add_zero (a : MyNat) : Eq (add a zero) a := Eq.refl a
```

```text
value type:    Eq a a
declared type: Eq (add a zero) a
```

`is_def_eq` compares argument by argument and reaches `a` against
`add a zero`. Unfold `add`, beta reduce, and you have
`MyNat.rec a (fun _ ih => succ ih) zero`. The major premise is the constructor
`zero`, so the recursor rule fires and yields `a`.

Nothing in the proof term says "compute". The kernel computes because it was
asked whether two types are the same. This is what `rfl` means in Lean, and it
is why Chapter 3's computation rules are part of the trusted core.

## 3. Where Computation Stops

```lean
theorem zero_add (a : MyNat) : Eq (add zero a) a := Eq.refl a   -- rejected!
```

`add zero a` unfolds to `MyNat.rec zero (fun _ ih => succ ih) a`. The major
premise is `a`, a variable, not a constructor. No rule applies. The term is
*stuck*, it is not `a`, and the kernel must say no.

`add` recurses on its second argument, so facts about a concrete second
argument are free and facts about a concrete first argument are theorems. The
proof is by induction, which is to say by `MyNat.rec` with a proposition as
the motive:

```text
motive n  :=  Eq (add zero n) n

zero case:  Eq (add zero zero) zero            by Eq.refl zero   (computes)
succ case:  given ih : Eq (add zero n) n,
            show  Eq (add zero (succ n)) (succ n)
            which computes to Eq (succ (add zero n)) (succ n)
            so    Eq.congrArg succ ih
```

The test `test_refl_cannot_prove_zero_add` checks that your kernel accepts
`Eq.refl a` for `add_zero` and rejects the same term for `zero_add`. A kernel
that accepted both would be unsound; one that rejected both cannot compute.

## 4. What To Implement

Three small additions to `is_def_eq` in `kernel/typechecker.py`.

**Proof irrelevance.** If `t` is a proof (its type is a `Prop`), and `s` has
the same type, then `t` and `s` are equal, whatever they look like. Try this
right after the quick structural cases. It keeps the kernel from ever having
to compute with proofs.

**Eta.** `fun x => f x` equals `f`. When one side is a `Lam` and the other is
not, wrap the other side as `Lam(x, App(s, BVar(0)))` using its type's domain,
and compare again.

**K, for types like `Eq`.** `reduce_recursor` gets stuck on `Eq.rec ... h` when
`h` is a variable. But by proof irrelevance every `h : Eq a a` equals
`Eq.refl a`. So for a recursor with the `k` flag: if the major premise is not
a constructor, build `ctor params` from the *type* of the major premise, check
that it has the same type, and reduce with that instead. This is
`to_constructor_when_k`.

## 5. Stop And Look

Run the whole chapter through your kernel and read the output:

```bash
python3 -m kernel.check chapters/04_equality/examples.trace
```

Every line is something real Lean's kernel was asked to check, and yours
agreed, from the definition of the natural numbers up to commutativity of
addition. Nothing was assumed: `0 imported`.

## Hints

<details>
<summary>Hint 1: <code>Eq.rec</code> does not match Lean's</summary>

Indices come *after* the minors in the recursor's type, and the motive takes
the indices *and then* the major premise. For `Eq`, the constructor's result
is `Eq α a a`: the index argument of the result is the parameter `a`.

</details>

<details>
<summary>Hint 2: proof irrelevance fails on non-proofs</summary>

`infer` can raise on the way. Wrap the attempt in `try`/`except KernelError`
and treat an error as "not applicable".

</details>

<details>
<summary>Hint 3: <code>zero_add</code> is accepted with <code>Eq.refl</code></summary>

Then something compared equal that should not have. Usual causes: two
different `FVar`s compared equal; `is_def_eq` returns `True` at the end
instead of `False`; proof irrelevance applied without checking the two types
match.

</details>

## In Lean's Source

| Here | [cpp-lean-kernel/src/kernel](../../cpp-lean-kernel/src/kernel) |
| --- | --- |
| proof irrelevance | `type_checker::is_def_eq_proof_irrel` |
| eta | `type_checker::try_eta_expansion` |
| K | `to_cnstr_when_K` in `inductive.h` |
