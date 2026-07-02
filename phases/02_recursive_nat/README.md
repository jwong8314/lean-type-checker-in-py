# Phase 2: Recursive Natural Numbers

Goal: add ordinary mathematical objects by declaring a recursive type.

Do not treat `Nat` as a built-in. Add it to the environment with a recursive
type declaration:

```text
inductive Nat : Type where
| zero : Nat
| succ : Nat -> Nat
```

New implementation pieces:

1. `Var`, `App`, and `Pi` expressions.
2. Function application checking.
3. A `RecursiveTypeSpec` that registers a type and derives constructor types.

Try it:

```bash
python3 -B phases/02_recursive_nat/solution.py
```
