# Chapter 5: Sugar

Goal: check a normal Lean file, written the way people actually write Lean,
and then implement one piece of the machinery that makes that possible.

```lean
theorem zero_add (a : MyNat) : zero + a = a := by
  induction a with
  | zero => rfl
  | succ n ih => rw [my_add_succ, ih]
```

Chapters 1 to 4 used `prelude` and spelled every term out. This chapter's
[examples.lean](examples.lean) does neither: it imports Lean's standard
library and uses pattern matching, `+`, `rfl`, `rw`, and `induction`.

```bash
pytest tests/test_ch5_sugar.py
```

## 1. There Is No Sugar In The Kernel

Your kernel has no idea what a tactic is, and it will check this file anyway.

By the time a declaration reaches the kernel, the **elaborator** has replaced
every convenience with plain terms built from the node kinds you already
handle. The source file is 66 lines; [examples.trace](examples.trace) is over
21,000. [SUGAR.md](../../instrumentation/SUGAR.md) walks through each
construct with the source and the result side by side. In brief:

| You write | The kernel receives |
| --- | --- |
| `a + b` | `HAdd.hAdd MyNat MyNat MyNat (instHAdd MyNat MyNat.instAdd) a b` |
| `inductive MyNat` | `MyNat`, its constructors, and about twenty generated helper definitions |
| `def add \| a, zero => a \| ...` | three definitions built on `casesOn` and `brecOn`, which are built on `MyNat.rec` |
| `instance : Add MyNat` | an ordinary definition, `Add.mk add` |
| `(a b : MyNat) : P` before the colon | `∀ (a b : MyNat), P`, and `fun a b =>` in the value |
| `by rfl` | `Eq.refl _` |
| `by rw [h]` | `Eq.mpr (id (congrArg (fun _a => ...) h)) ...` |
| `by induction a with ...` | `MyNat.rec (motive := ...) ... a` |

`{α : Sort u}` and `[inst : Add α]`, the binder annotations you have been
carrying since Chapter 2, exist for the elaborator: they mark arguments it
should fill in for you. The kernel ignores them.

## 2. Imports

The trace now has `reference` blocks: constants from the standard library
that this file mentions, such as `Eq`, `HAdd.hAdd`, and `id`. Lean's kernel
checked those when the library was compiled, and loads them from disk without
checking them again. `kernel/check.py` does the same: it adds them unchecked.

With one exception. For an imported *inductive type* your `add_inductive`
still runs, and the recursor it generates is compared with the one Lean
shipped. So this chapter also tests your Chapter 3 code against `Nat`,
`Bool`, `List`, `Decidable`, and the real `Eq`.

## 3. What The Kernel Still Needs

Three things appear in real traces that the `prelude` chapters avoided. All
are in `kernel/typechecker.py`.

**Projections.** `Proj S i e` is field `i` of the structure value `e`. The
compiled form of `add` uses it to look up recursive calls.

- `reduce_proj`: `whnf` the structure. If it is a constructor application,
  the answer is argument number `num_params + i`.
- `infer_proj`: `whnf` the type of `e` to get `S params`. Take the type of
  `S`'s only constructor, instantiate its parameters with `params`, then skip
  `i` fields. A later field's type may mention earlier fields: instantiate
  each skipped binder with `Proj S j e`.

**`let`.** `Let x : T := v, body`. To infer its type, check `v : T` and infer
`body` with `x` replaced by `v`. To reduce it, substitute.

**Number literals.** `Lit nat 3`. Lean stores these as big integers for
speed. `nat_literal_to_constructor` (given) turns one into `Nat.zero` or
`Nat.succ` of a smaller literal; use it in `reduce_recursor` when the major
premise is a literal, and in `is_def_eq` when a literal meets a constructor.

Then:

```bash
python3 -m kernel.check chapters/05_sugar/examples.trace
```

`unsafe` and `partial` definitions are skipped, as are the placeholder
`axiom`s the elaborator sends while it compiles a recursive function. The
replay explains each skip.

## 4. Implement `rw`

Now cross to the other side and write a piece of the elaborator, in
`kernel/rewrite.py`. Given a goal and a proof `h : lhs = rhs`, `rw [h]`:

1. **Finds the pattern.** `kabstract(goal, lhs)` replaces every occurrence of
   `lhs` in the goal with a bound variable.
2. **Builds the motive.** `motive := fun _a : α => (abstracted goal)`. By
   construction, `motive lhs` is the goal.
3. **Computes the new goal.** `motive rhs`, i.e. `instantiate(abstracted, rhs)`.
4. **Checks the motive.** Abstracting can produce an ill-typed function when
   other parts of the goal depend on `lhs`. Type check it, and fail with
   "motive is not type correct" if it does not pass.
5. **Builds the proof.** `congrArg motive h : goal = new_goal`.

Then `mk_eq_mpr` turns a proof of the new goal into a proof of the old one:

```lean
@Eq.mpr goal new_goal (@id (goal = new_goal) eq_proof) rest
```

The `id` does nothing. Lean inserts it as a type hint.

For example, in `rewrite_step`:

```text
goal      succ (succ a + n) = succ (succ (a + n))
h         ih : succ a + n = succ (a + n)
motive    fun _a => succ _a = succ (succ (a + n))
new goal  succ (succ (a + n)) = succ (succ (a + n))      closed by rfl
```

The test is strict. It finds all 20 uses of `rw` in the real trace, hands your
function the same goal and `h` that Lean's `rw` had, and requires your output
to equal Lean's **node for node**: same motive, same universe levels, same
`id` wrapper.

You must fill in the universe levels and implicit arguments yourself. That is
the elaborator's job, and now it is yours:

```lean
congrArg.{u, v} : {α : Sort u} → {β : Sort v} → {a₁ a₂ : α} → (f : α → β) → a₁ = a₂ → f a₁ = f a₂
Eq.mpr.{u}      : {α β : Sort u} → α = β → β → α
id.{u}          : {α : Sort u} → α → α
```

Use your type checker to find them: `infer` on a type gives you its `Sort`,
and the level is inside. Pass levels through `simplify`, so that you produce
`1` and not `imax 1 1`.

## 5. Why `rw` Cannot Break Anything

`kernel/rewrite.py` imports from the kernel, but nothing in the kernel
imports it. That one-way arrow is the whole safety argument.

```text
                  untrusted                       trusted
  rw [h]  --->  rewrite, mk_eq_mpr  --->  proof term  --->  infer, is_def_eq
```

- **A bug in `rw` cannot prove a false theorem.** Whatever term it builds is
  checked from scratch by a kernel that does not know a tactic produced it.
  If `kabstract` abstracts the wrong thing, the term does not type check and
  the theorem is rejected. The worst outcome is a proof that fails. Try it:
  break `kabstract` and run `infer` on the result.
- **The term uses nothing special.** `congrArg` and `Eq.mpr` are ordinary
  library theorems, each proved with `Eq.rec`, which your Chapter 3 code
  generated from the definition of `Eq`. Rewriting *is* the substitution
  principle. No axiom was added for it.
- **The kernel never rewrites with your equations.** `ih` is used only as an
  argument to `congrArg`. The kernel's own reductions are the fixed set you
  implemented: beta, delta, the recursor rules, projections. A user cannot
  register a new one. A `def` adds a delta rule only after its body is type
  checked; an `inductive` adds recursor rules derived mechanically from its
  constructors.

This arrangement is called the de Bruijn criterion: a large program that
nobody trusts writes proofs, and a small program that everybody can read
checks them. The elaborator in Lean is hundreds of thousands of lines. The
part you had to get right is `kernel/typechecker.py` and
`kernel/inductive.py`.

What does have to be trusted: the kernel itself, the machine running it, and
that the theorem's *statement* says what you meant. For the kernel there is a
further safeguard, which you have just contributed to: independent
reimplementations (`lean4lean`, `nanoda`, and now yours) that must all be
fooled at once.

## Hints

<details>
<summary>Hint 1: <code>kabstract</code> and binders</summary>

It is `abstract` from Chapter 2 with "is this the free variable?" replaced by
"is this subterm equal to the pattern?". Same `depth` bookkeeping.

</details>

<details>
<summary>Hint 2: reading the equation out of <code>h</code></summary>

```python
head, args = spine(checker.whnf(checker.infer(h)))
# head is Const("Eq", ...), args is [alpha, lhs, rhs]
```

</details>

<details>
<summary>Hint 3: my output differs from Lean's only in levels</summary>

For `congrArg.{u, v}`: `u` is the level of `α`'s sort, and `β` is the type of
the *goal*, normally `Prop`, whose own sort is `Sort 1`, so `v = 1`. For
`Eq.mpr.{u}`: the goal is a `Prop`, so `u = 0`. The `Eq` inside the `id`
compares two propositions, so it is `Eq.{1} Prop goal new_goal`.

</details>

<details>
<summary>Hint 4: decompile to see the difference</summary>

```bash
python3 instrumentation/decompile.py chapters/05_sugar/examples.trace --only MyNat.succ_add_succ
python3 instrumentation/decompile.py chapters/05_sugar/examples.trace --only MyNat.succ_add_succ --explicit
```

</details>

## What Real `rw` Does Beyond This

- `rw [my_add_succ]` without arguments: Lean creates placeholders for `a` and
  `b`, and fills them in by matching the pattern against the goal. The tests
  give you `h` with its arguments already supplied.
- Occurrences are found up to instances being unfolded, not by exact equality.
- `rw [← h]` uses `Eq.symm h`. That already works: it is just another `h`.
- After rewriting, `rw` tries `rfl` to close the goal.

## In Lean's Source

| Here | Lean |
| --- | --- |
| `rewrite` | `Lean.MVarId.rewrite` in `src/Lean/Meta/Tactic/Rewrite.lean` |
| `kabstract` | `Lean.Meta.kabstract` in `src/Lean/Meta/KAbstract.lean` |
| `mk_eq_mpr` | `Lean.MVarId.replaceTargetEq` in `src/Lean/Meta/Tactic/Replace.lean` |
| `infer_proj`, `reduce_proj` | `type_checker::infer_proj`, `reduce_proj` in `type_checker.cpp` |
