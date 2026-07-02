# A Tiny Lean-Inspired Type Checker in Python

This repository contains a phased tutorial implementation of a very small
dependent type checker inspired by Lean's kernel.

The focus is not to reimplement Lean.  Instead, the code follows the same core
rhythm:

1. Infer the type of each expression.
2. Reduce to weak-head normal form when a `Sort` or dependent function type is
   expected.
3. Use definitional equality to compare types.
4. Let `rfl` prove equalities whose two sides compute to the same expression.
5. Add a small rewrite principle.
6. Use a small `Nat.ind` expression when computation alone is not enough.

## The Four Phases

### Phase 1: True and False

The first checker only knows:

```text
True : Prop
true_intro : True
False : Prop
```

This is enough to see the propositions-as-types idea: `True` and `False` are
types, and proofs are terms inhabiting those types.  The demo checks
`true_intro : True` and rejects `true_intro : False`.

### Phase 2: Natural-Number Objects

The second checker adds ordinary mathematical objects:

```text
Nat : Type
zero : Nat
succ : Nat -> Nat
```

At this point there is no equality, no rewriting, and no induction.  We can
only check that terms such as `zero`, `succ zero`, and `succ (succ zero)` are
well-typed natural numbers.

### Phase 3: Equality and Rewrites

The third checker adds equality proofs, `rfl`, and definitional equations for
addition:

```text
add a zero     --> a
add a (succ b) --> succ (add a b)
```

It can prove the computation lemmas by `rfl`:

```text
forall a,     a + zero = a
forall a n,   a + succ n = succ (a + n)
```

It also introduces a tiny rewrite principle, `congr_succ`: from
`ih : x = y`, it builds a proof of `succ x = succ y`.

### Phase 4: Induction

The final checker adds a small `Nat.ind` expression.  That is enough to prove:

The demo target is:

```text
forall a b : Nat, succ a + b = succ (a + b)
```

The proof is induction on `b`, matching the usual Lean shape:

```text
fun a b =>
  Nat.ind
    (fun b => succ a + b = succ (a + b))
    rfl
    (fun n ih => congr_succ ih)
    b
```

This is needed because `succ a + b = succ (a + b)` is not definitionally true
for a variable `b`.  The base and step cases are definitionally simple, but the
theorem itself needs the inductive hypothesis.

## Run It

```bash
python3 tutorial_type_checker.py
```

Expected output:

```text
Phase 1: True and False
  True : Prop
  False : Prop
  true_intro : True
  true_intro checked against False? no

Phase 2: Natural-number objects
  zero : Nat
  succ : Nat -> Nat
  succ (succ zero) : Nat

Phase 3: Equality and rewrites
  add_zero proof: fun (a : Nat) => rfl@Nat a
  add_succ proof: fun (a : Nat) => fun (n : Nat) => rfl@Nat (succ (a + n))
  rewrite step from ih: congr_succ ih
  rewrite goal: (succ a) + (succ n) = succ (succ (a + n))

Phase 4: Induction completes the proof
  Target theorem: forall (a : Nat), forall (b : Nat), (succ a) + b = succ (a + b)
  Proof term: fun (a : Nat) => fun (b : Nat) => Nat.ind (fun (b : Nat) => (succ a) + b = succ (a + b)) (rfl@Nat (succ a)) (fun (n : Nat) => fun (ih : (succ a) + n = succ (a + n)) => congr_succ ih) b
  Accepted with type: forall (a : Nat), forall (b : Nat), (succ a) + b = succ (a + b)
  Bare rfl proof accepted? no, rejected as expected
```

## Where To Read

Start with [tutorial_type_checker.py](/Users/wong.justin/Documents/lean-kernel/tutorial_type_checker.py).
It is written top-to-bottom:

1. Syntax.
2. Capture-avoiding substitution.
3. Type inference, weak-head reduction, and definitional equality.
4. Phase-specific environments for `True`/`False`, `Nat`, `add`, rewrites, and
   induction.
5. The theorem and proof.
