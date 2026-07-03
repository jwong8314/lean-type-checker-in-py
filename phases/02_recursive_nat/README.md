# Phase 2: Recursive Natural Numbers

Goal: add ordinary mathematical objects by declaring a recursive type.

Do not treat `MyNat` as a built-in. Add it to the environment with a recursive
type declaration:

```text
inductive MyNat : Type where
| zero : MyNat
| succ : MyNat -> MyNat
```

New implementation pieces:

1. `Var`, `App`, and `Pi` expressions.
2. Function application checking.
3. A `RecursiveTypeSpec` that registers a type and derives constructor types.
4. `Eq` and `Refl`, so `rfl` can prove `x = x`.

Try it:

```bash
python3 -B tutorial_type_checker.py 02
```
