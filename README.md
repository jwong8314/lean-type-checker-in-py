# A Tiny Lean-Inspired Type Checker in Python

This repository contains a tutorial implementation of a very small dependent
type checker inspired by Lean's kernel.

The focus is not to reimplement Lean.  Instead, the code follows the same core
rhythm:

1. Infer the type of each expression.
2. Reduce to weak-head normal form when a `Sort` or dependent function type is
   expected.
3. Use definitional equality to compare types.
4. Let `rfl` prove equalities whose two sides compute to the same expression.
5. Use a small `Nat.ind` expression when computation alone is not enough.

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

This is needed because `Nat.add` computes by recursion on the second argument:

```text
add a zero     --> a
add a (succ b) --> succ (add a b)
```

So `succ a + b = succ (a + b)` is not definitionally true for a variable `b`.
The base and step cases are definitionally simple, but the theorem itself needs
the inductive hypothesis.

## Run It

```bash
python3 tutorial_type_checker.py
```

Expected output:

```text
Target theorem:
  forall (a : Nat), forall (b : Nat), (succ a) + b = succ (a + b)

Proof term:
  fun (a : Nat) => fun (b : Nat) => Nat.ind (fun (b : Nat) => (succ a) + b = succ (a + b)) (rfl@Nat (succ a)) (fun (n : Nat) => fun (ih : (succ a) + n = succ (a + n)) => congr_succ ih) b

The checker accepts the proof with type:
  forall (a : Nat), forall (b : Nat), (succ a) + b = succ (a + b)
```

## Where To Read

Start with [tutorial_type_checker.py](/Users/wong.justin/Documents/lean-kernel/tutorial_type_checker.py).
It is written top-to-bottom:

1. Syntax.
2. Capture-avoiding substitution.
3. Type inference, weak-head reduction, and definitional equality.
4. Natural numbers, addition, induction, and successor congruence.
5. The theorem and proof.
