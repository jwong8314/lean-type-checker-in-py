# Lean-Style Type Checker in Python

This is a small workshop for building a Lean-like kernel step by step.

Each chapter has:

```text
README.md    # what to implement
solution.py  # the kernel implementation for that chapter
script.lean  # Lean-like declarations kept separate from the implementation
```

The repository is split into three conceptual layers:

```text
solution_runner.py  # top-level orchestration for checking chapter scripts
pylean/             # shared parser, expression nodes, and checker interface
chapters/           # tutorial chapters with script.lean + solution.py
```

[solution_runner.py](solution_runner.py) owns the generic declaration-checking
loop. It registers parsed `script.lean` declarations as they are checked instead
of carrying a separate table of theorem names. Before checking a chapter, it
imports every earlier chapter by parsing and registering those earlier
`script.lean` declarations.

[pylean/type_checker.py](pylean/type_checker.py) defines the shared abstract
`TypeChecker`: it owns the environment and generic `check`. Each chapter
customizes `infer`, and Chapter 2 introduces recursive declaration registration.

[pylean/expressions.py](pylean/expressions.py) defines the shared `Expr`,
`Sort`, `Prop`, and `Type`. Every chapter-specific expression node inherits from
that same package-level `Expr`.

## Run

Install the parser dependency:

```bash
python3 -m pip install -r requirements.txt
```

Run every chapter:

```bash
python3 -B -m pylean.tutorial_type_checker all
```

Run one chapter:

```bash
python3 -B -m pylean.tutorial_type_checker 01
python3 -B -m pylean.tutorial_type_checker 02
python3 -B -m pylean.tutorial_type_checker 03
python3 -B -m pylean.tutorial_type_checker 04
python3 -B -m pylean.tutorial_type_checker 05
```

Print the kernel expression trees produced from a chapter script:

```bash
python3 -B -m pylean.print_ast chapters/03_rewrites/script.lean
```

The runner builds the selected chapter's checker with `solution_runner.py`, then
type-checks each declaration in that chapter's separate `script.lean` file. If
anything fails to type check, the runner crashes with an error.

## Chapters

Chapter 1 builds a tiny checker for `True`, `False`, and proof terms.

Chapter 2 adds `MyNat` as a recursive type declaration, not as a built-in, and
introduces `rfl` for reflexive equality proofs.

Chapter 3 adds definitional computation for `add` and a tiny rewrite principle.

Chapter 4 adds induction over recursive type declarations and proves:

```text
forall a b : MyNat, succ a + b = succ (a + b)
```

Chapter 5 accepts the raw `MyNatSuccAdd.lean` script and proves the
commutativity layer:

```text
MyNat, zero_add, succ_add_succ, add_comm, add_assoc, add_right_comm
```

## Current Limitation

`script.lean` is intentionally tiny. It contains ordinary-looking `constant`,
`inductive`, `def`, and `theorem` declarations, but this project still does not
parse full Lean. For now, [pylean/lean_parser.py](pylean/lean_parser.py) parses
only the small subset used in these tutorial scripts. That keeps scripts
separate from the kernel implementation while avoiding a full Lean parser too
early.
