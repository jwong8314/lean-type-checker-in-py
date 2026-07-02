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

The demo target is:

```text
forall a b : Nat, succ a + b = succ (a + b)
```

The proof is:

```text
fun a b => rfl
```

That works because this miniature kernel gives `Nat.add` the Lean-style
computation rule:

```text
add zero     b --> b
add (succ a) b --> succ (add a b)
```

So the left side of the theorem reduces to the right side during type checking.

## Run It

```bash
python3 tutorial_type_checker.py
```

Expected output:

```text
Target theorem:
  forall (a : Nat), forall (b : Nat), (succ a) + b = succ (a + b)

Proof term:
  fun (a : Nat) => fun (b : Nat) => rfl@Nat (succ (a + b))

The checker accepts the proof with type:
  forall (a : Nat), forall (b : Nat), succ (a + b) = succ (a + b)
```

The final type is the inferred type of the proof term.  The checker accepts it
against the target theorem because the target's left side is definitionally
equal to the displayed, reduced left side.

## Where To Read

Start with [tutorial_type_checker.py](/Users/wong.justin/Documents/lean-kernel/tutorial_type_checker.py).
It is written top-to-bottom:

1. Syntax.
2. Capture-avoiding substitution.
3. Type inference, weak-head reduction, and definitional equality.
4. Natural numbers and addition.
5. The theorem and proof.

