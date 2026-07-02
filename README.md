# Lean-Style Type Checker in Python

This is now structured as a small workshop. Each phase is its own directory
with:

```text
README.md    # what to build and why
solution.py  # one working implementation for that phase
```

The idea is to implement step by step. Read a phase README, try writing the
checker yourself, then compare against `solution.py`.

## Phases

```text
phases/
  01_true_false/
    README.md
    solution.py
  02_recursive_nat/
    README.md
    solution.py
  03_rewrites/
    README.md
    solution.py
  04_induction/
    README.md
    solution.py
```

Phase 1 builds a tiny checker for `True`, `False`, and proof terms.

Phase 2 adds `Nat` as a recursive type declaration, not as a built-in.

Phase 3 adds equality, `rfl`, definitional computation for `add`, and a tiny
rewrite principle.

Phase 4 adds induction over recursive type declarations and proves:

```text
forall a b : Nat, succ a + b = succ (a + b)
```

## Run Everything

```bash
python3 -B tutorial_type_checker.py
```

Or run one phase directly:

```bash
python3 -B phases/01_true_false/solution.py
python3 -B phases/02_recursive_nat/solution.py
python3 -B phases/03_rewrites/solution.py
python3 -B phases/04_induction/solution.py
```

Expected final phase output:

```text
bare rfl rejected
succ_add : forall (a : Nat), forall (b : Nat), (succ a) + b = succ (a + b)
```

## Note

The implementations are intentionally small and pedagogical. They are not a
full Lean parser or kernel; they isolate the kernel ideas needed for the final
proof: inference, conversion, recursive type declarations, computation,
rewriting, and induction.
