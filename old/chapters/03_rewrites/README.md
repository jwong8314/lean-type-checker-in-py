# Chapter 3: Equality and Rewrites

Goal: build equality and rewriting one declaration at a time.

Nothing in this chapter should feel like a hidden compiler default. Chapter 2
introduced equality and `rfl`; this script introduces each new computation and
rewrite ingredient before using it:

1. `add`, a `MyNat` function.
2. `add_zero a : a + zero = a`, the first named equation for addition.
3. `add_succ a b : a + succ b = succ (a + b)`, the second named equation.
4. `rw`, a tiny rewrite tactic/principle under `succ`.
5. Theorems that use those pieces.

The addition equations are:

```text
add a zero     --> a
add a (succ b) --> succ (add a b)
```

So `add : MyNat -> MyNat -> MyNat` is just the shape of the function. Its
behavior is introduced by `add_zero` and `add_succ`: those are the only
equations we are allowed to cite when we want to change an addition expression.

The important strictness point is that the checker does not silently identify
`a + zero` with `a`. Equality checking in this chapter is exact structural
equality. If the goal contains `a + zero`, the proof must explicitly use
`add_zero a`; `rfl` only works when both sides are already the same expression.

<details>
<summary>For type theory enthusiasts: why equality is universe-polymorphic</summary>

```lean
inductive Eq {α : Sort u} (a : α) : α → Prop where
  | refl : Eq a a
```

`refl` is a constructor of `Eq`. Notice that the type being compared is
`α : Sort u`, rather than only `α : Type`.

Had equality been declared with:

```lean
{α : Type}
```

it would only directly describe equality between values of ordinary data types
in that universe. Using:

```lean
{α : Sort u}
```

makes equality universe-polymorphic. It can compare values such as:

```text
3 = 3
```

where `3 : Nat` and `Nat : Sort 1`; propositions such as:

```text
True = True
```

where `True : Prop` and `Prop = Sort 0`; and types themselves:

```text
Nat = Nat
```

Here the values being compared are types, since `Nat : Type`, so Lean chooses
an appropriate higher universe for `α`.

### Reading The Declaration One Piece At A Time

```lean
inductive Eq {α : Sort u} (a : α) : α → Prop
```

means:

1. Choose a universe level `u`.
2. Choose a type: `α : Sort u`.
3. Choose a value: `a : α`.
4. For every other value `b : α`, form the proposition `Eq a b : Prop`.

The constructor is:

```text
Eq.refl : Eq a a
```

So the full family is approximately:

```text
Eq : {α : Sort u} → α → α → Prop
```

</details>

Tactics are not extra kernel rules. They are a small elaboration layer that
massages a proof script into an ordinary proof object before the type checker
sees it. In this chapter, `rfl` elaborates to a `Refl(...)` proof object. The
`rw h` tactic first inspects the current goal, checks that rewriting with `h`
would produce that exact goal shape, and then elaborates to `SuccCongr(h)`, an
ordinary congruence proof under `succ`. After that point, the checker is only
checking expression trees, not tactic syntax.

That mirrors the important Lean idea: tactics help build proof terms, but the
kernel still only accepts or rejects the proof term that tactics produce.

## How Real Lean Rewrites

It is tempting to imagine a "rewriter" inside Lean's kernel. There is not one.
Two different components do work that looks like rewriting, and they sit on
opposite sides of the trust boundary:

```text
                  untrusted                          trusted
  rw [h]  --->  Lean.MVarId.rewrite  --->  proof term  --->  kernel type checker
                (builds a term)                              (infer, whnf, is_def_eq)
```

| | `rw` | kernel reduction |
| --- | --- | --- |
| Lives in | the elaborator: `src/Lean/Meta/Tactic/Rewrite.lean` | the kernel: [type_checker.cpp](../../cpp-lean-kernel/src/kernel/type_checker.cpp) |
| Rewrites with | any equation you have *proved*, such as `ih` | a fixed list of *computation* rules only |
| Leaves evidence | yes, an explicit proof term | no, it happens silently inside `is_def_eq` |
| Trusted | no | yes |

### 1. What `rw [h]` Does

`rw` is a tactic, so its only job is to produce a proof term. The work is done
by `Lean.MVarId.rewrite`. Given a goal `e` and a proof `h : lhs = rhs`:

1. **Find the pattern.** `kabstract e lhs` walks the goal and replaces every
   instance of `lhs` with a bound variable. Call the result `e_abst`. If
   nothing was replaced, `rw` fails with "did not find instance of the pattern".
2. **Build the motive.** Wrap the abstracted goal in a lambda:
   `motive := fun _a => e_abst`. By construction `motive lhs` is the old goal.
3. **Compute the new goal.** `e_new := motive rhs`, the goal with `rhs` filled
   in where `lhs` used to be.
4. **Check the motive.** Abstracting can produce a lambda that does not type
   check (when other parts of the goal depend on `lhs`). `rw` checks this and
   fails early with "motive is not type correct".
5. **Build the proof.** `congrArg motive h : e = e_new`, and then
   `Eq.mpr (congrArg motive h) ?new_goal : e`, where `?new_goal : e_new` is
   what you still have to prove.
6. **Try `rfl`.** `rw` finally tries to close the new goal by reflexivity.

The two library lemmas involved are ordinary theorems, not kernel features:

```lean
congrArg : (f : α → β) → a₁ = a₂ → f a₁ = f a₂
Eq.mpr   : α = β → β → α
```

Both are proved with `Eq.rec`, the recursor Lean generates from the `Eq`
inductive declaration. So every `rw` in every Lean proof ultimately becomes
applications of one rule:

```text
Eq.rec : motive a → a = b → motive b      (simplified)
```

### 2. Worked Example

Take this chapter's `rewrite_step`:

```lean
theorem rewrite_step (a n : MyNat) (ih : succ a + n = succ (a + n)) :
    succ (succ a + n) = succ (succ (a + n)) := by
  rw [ih]
```

```text
goal     succ (succ a + n) = succ (succ (a + n))
lhs      succ a + n
e_abst   succ _a = succ (succ (a + n))
motive   fun _a => succ _a = succ (succ (a + n))
e_new    succ (succ (a + n)) = succ (succ (a + n))     -- closed by rfl
```

The term real Lean hands to the kernel, as printed by `#print rewrite_step`:

```lean
fun a n ih =>
  Eq.mpr
    (id (congrArg (fun _a => _a.succ = (a + n).succ.succ) ih))
    (Eq.refl (a + n).succ.succ)
```

The `id` is only a type hint and does nothing. This is the pretty-printed
view. The raw expression tree the kernel receives is much larger, because `+`
is really `HAdd.hAdd MyNat MyNat MyNat (instHAdd MyNat MyNat.instAdd) ...` and
every implicit argument of `Eq.mpr` and `congrArg` is spelled out. The full
448-node tree, captured from the
[instrumented kernel](../../instrumentation/README.md), is in
[rewrite_step.trace](../../instrumentation/traces/rewrite_step.trace), and
[SUGAR.md](../../instrumentation/SUGAR.md) walks through what each piece of
surface syntax turns into.

Notice that the motive abstracts the *whole goal*, so one mechanism handles a
rewrite at any depth. This chapter's `SuccCongr(h)` is the special case
`congrArg succ h`: it can only rewrite directly under one `succ`. Chapter 5
adds a few more fixed congruence steps, but still not a general motive.

### 3. What The Kernel Does Instead

The kernel never searches for a pattern and never uses a hypothesis like `ih`
as a rewrite rule. When it receives the term above it only runs its usual
loop: infer the type of each application and compare it with what was expected,
using `is_def_eq`.

`is_def_eq` is where the kernel's own "rewriting" happens. It calls `whnf`
(weak head normal form), which applies a fixed set of computation rules:

| Rule | Meaning | Where |
| --- | --- | --- |
| beta | `(fun x => b) a` becomes `b[x := a]` | `instantiate.cpp` |
| delta | unfold a definition to its body | `lazy_delta_reduction` |
| zeta | substitute a `let` | `whnf_core` |
| iota | a recursor applied to a constructor computes | `reduce_recursor`, `inductive.cpp` |
| projection | `(a, b).1` becomes `a` | `whnf_core` |

It also treats two terms as equal by eta and by proof irrelevance (any two
proofs of the same proposition are equal).

For the example above the kernel needs only beta: to accept `Eq.mpr ...` it
must see that `(fun _a => succ _a = ...) (succ a + n)` is the original goal.

The difference from this tutorial matters. In real Lean, `a + zero = a` is
proved by `rfl`, because the kernel unfolds `add` (delta) and computes its
recursor on `zero` (iota). Our Chapter 3 checker keeps `defeq` as exact
structural equality on purpose, so you must cite `add_zero` by name and can see
every step in the proof term.

### 4. Why We Can Trust It

**`rw` cannot make a false theorem true.** It is outside the kernel. Whatever
term it builds is checked from scratch, with no knowledge that a tactic made
it. A bug in `kabstract` or in the motive construction produces a term the
kernel rejects, or a tactic error. The worst case is a proof that fails. This
design is called the de Bruijn criterion: a large untrusted program writes
proofs, a small trusted program checks them.

**The term uses nothing special.** Rewriting reduces to `Eq.rec`, which is the
substitution principle: if `a = b`, anything true of `a` is true of `b`. It is
not an axiom added for `rw`; it is generated from the definition of `Eq` by the
same rule that generates `MyNat.rec`. `#print axioms rewrite_step` reports no
axioms.

**Kernel reduction is the part we really trust**, so that is where the care
goes:

- It is small. `type_checker.cpp` is about 1,200 lines, which a person can
  read in full.
- Its rules are fixed. Users cannot register new reduction rules; a `def` only
  adds a delta rule for a body the kernel has already type checked, and an
  `inductive` only adds iota rules derived from its constructors.
- Each rule replaces a term with one of the same type and meaning, so
  comparing terms after reduction cannot identify things that differ.
- The theory has been studied on paper. Mario Carneiro's *The Type Theory of
  Lean* gives a model showing the rules are consistent.
- It is checked by independent implementations. `lean4checker` replays
  compiled files through the kernel, and `lean4lean` (Lean) and `nanoda`
  (Rust) are separate kernels written from the same rules. A bug would have to
  appear in all of them to go unnoticed.

What remains trusted is the kernel code itself, the compiler and hardware that
run it, and that the theorem statement says what you meant.

### 5. The Same Split In This Chapter

| Role | Real Lean | This chapter |
| --- | --- | --- |
| Untrusted rewriter | `Lean.MVarId.rewrite` | `rewrite_goal` in [solution.py](solution.py) |
| Proof term it emits | `Eq.mpr (congrArg motive h) ...` | `SuccCongr(h)` |
| Trusted rule | typing of `Eq.rec` | the `SuccCongr` case of `infer` |

Try it: change `rewrite_goal` so it returns `SuccCongr(proof)` without
comparing against the goal. Scripts that were correct still pass. A script
that rewrites with the wrong hypothesis now gets past the tactic layer, and is
rejected by `check`, because the type inferred for `SuccCongr(proof)` is not
the theorem statement. The rewriter was never what kept you safe.

The runner processes [script.lean](script.lean) in declaration order.
[solution_runner.py](../../solution_runner.py) updates the checker as each
declaration is reached, so later theorems only type-check because earlier
declarations have already been added.

Try it:

```bash
python3 -B -m pylean.tutorial_type_checker 03
```
