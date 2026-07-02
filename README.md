# A Tiny Lean-Inspired Type Checker in Python

This repository is organized like a tiny tutorial Lean project, but the files
are checked by our Python kernel.

Each phase lives in its own subdirectory under [phases](phases).  The `.lean` files are Lean-shaped tutorial files with `#kernel` directives.  The Python runner reads those directives and dispatches them to the under-development kernel.

## Layout

```text
lean_type_checker/
  core.py        # expressions, recursive type declarations, conversion, checking
  runner.py      # reads #kernel directives from the phase .lean files

phases/
  01_true_false/1_true_false.lean
  02_recursive_nat/2_recursive_nat.lean
  03_rewrites/3_rewrites.lean
  04_induction/4_induction.lean

tutorial_type_checker.py  # runs every phase
```

## Phases

Phase 1 starts with propositions-as-types:

```lean
#kernel check True : Prop
#kernel check true_intro : True
#kernel reject true_intro : False
```

Phase 2 introduces `Nat` as a recursive type declaration, not as a built-in:

```lean
#kernel inductive Nat : Type where
#kernel | zero : Nat
#kernel | succ : Nat -> Nat
```

Phase 3 adds equality, `rfl`, computation rules for `add`, and a tiny rewrite principle:

```lean
#kernel check add_zero : forall a : Nat, a + zero = a
#kernel check add_succ : forall a n : Nat, a + succ n = succ (a + n)
```

Phase 4 uses induction over the recursive `Nat` declaration to prove:

```lean
#kernel check succ_add : forall a b : Nat, succ a + b = succ (a + b)
```

The runner also checks that the tempting bare `rfl` proof is rejected, since `Nat.add` recurses on the second argument.

## Run It

```bash
python3 -B tutorial_type_checker.py
```

Expected output:

```text
phases/01_true_false/1_true_false.lean
  using phase 1 kernel
  True : Prop
  False : Prop
  true_intro : True
  rejected true_intro : False

phases/02_recursive_nat/2_recursive_nat.lean
  using phase 2 kernel
  registered recursive type Nat
  registered constructor zero
  registered constructor succ
  Nat : Type
  zero : Nat
  succ : Nat -> Nat
  succ zero : Nat
  succ (succ zero) : Nat

phases/03_rewrites/3_rewrites.lean
  using phase 3 kernel
  add_zero checked by rfl
  add_succ checked by rfl
  rewrite_step checked by congr_succ

phases/04_induction/4_induction.lean
  using phase 4 kernel
  rejected by_rfl
  succ_add : forall (a : Nat), forall (b : Nat), (succ a) + b = succ (a + b)
```

## Important Limitation

The `.lean` files are not parsed by Lean, and this project does not yet contain a full Lean parser.  For now, `#kernel` directives form a tiny tutorial command language.  That keeps the focus on kernel concepts: inference, weak-head reduction, definitional equality, recursive type declarations, rewrites, and induction.
