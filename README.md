# Lean-Style Type Checker in Python

This is a small workshop for building a Lean-like kernel step by step.

Each phase has:

```text
README.md    # what to implement
solution.py  # the kernel implementation for that phase
script.lean  # Lean-like declarations kept separate from the implementation
declarations.py # temporary AST bridge from script names to Python terms
```

The top-level [solution_runner.py](solution_runner.py) owns the default
environment setup for each phase. That keeps each `solution.py` focused on the
kernel syntax and typing rules instead of also seeding known declarations.

The top-level [type_checker.py](type_checker.py) defines the shared abstract
`TypeChecker`: it owns the environment and generic `check`. Each phase
customizes `infer`, and Phase 2 introduces recursive declaration registration.

The top-level [expressions.py](expressions.py) defines the shared `Expr`, `Sort`,
`Prop`, and `Type`. Every phase-specific expression node inherits from that
same top-level `Expr`.

## Run

Run every phase:

```bash
python3 -B tutorial_type_checker.py all
```

Run one phase:

```bash
python3 -B tutorial_type_checker.py 01
python3 -B tutorial_type_checker.py 02
python3 -B tutorial_type_checker.py 03
python3 -B tutorial_type_checker.py 04
python3 -B tutorial_type_checker.py 05
```

The runner builds the selected phase's checker with `solution_runner.py`, then
type-checks each declaration in that phase's separate `script.lean` file. If
anything fails to type check, the runner crashes with an error.

## Phases

Phase 1 builds a tiny checker for `True`, `False`, and proof terms.

Phase 2 adds `Nat` as a recursive type declaration, not as a built-in.

Phase 3 adds equality, `rfl`, definitional computation for `add`, and a tiny
rewrite principle.

Phase 4 adds induction over recursive type declarations and proves:

```text
forall a b : Nat, succ a + b = succ (a + b)
```

Phase 5 accepts the raw `MyNatSuccAdd.lean` script and proves the
commutativity layer:

```text
MyNat, zero_add, succ_add_succ, add_comm, add_assoc, add_right_comm
```

## Current Limitation

`script.lean` is intentionally tiny. It contains ordinary-looking `constant`,
`inductive`, `def`, and `theorem` declarations, but this project still does not
parse full Lean terms. For now, the runner extracts declaration names, and the
actual ASTs are produced by each phase’s separate `declarations.py` bridge.
That keeps scripts separate from the kernel implementation while avoiding a
full Lean parser too early.
