# Chapter 2: Recursive Natural Numbers

Goal: add ordinary mathematical objects by declaring a recursive type, then add
the equality proposition constructor.

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
4. `Eq(ty, lhs, rhs)`, the kernel expression for equality propositions.

The script introduces equality as a proposition former:

```text
constant Eq : Type -> MyNat -> MyNat -> Prop
```

This is intentionally only the type-level shape of equality. In Lean's real
kernel, `Eq` is an inductive proposition and `Eq.refl` is its constructor. A
declaration such as `constant h : a = b` would merely add an axiom/proof
constant; it would not explain how equality itself works. This tutorial mirrors
that split: Chapter 2 introduces equality propositions, and Chapter 4 introduces
`rfl` elaboration into an explicit reflexivity proof object.

Try it:

```bash
python3 -B -m pylean.tutorial_type_checker 02
```
