# Chapter 1: True and False

Goal: build the smallest useful checker.

In this chapter, propositions are just types and proofs are terms:

```text
Prop : Type
True : Prop
true_intro : True
False : Prop
```

Implement:

1. A tiny expression language with `Sort` and `Const`.
2. An environment mapping constant names to their types.
3. `infer(expr)` for `Sort` and `Const`.
4. `check(expr, expected)` by comparing the inferred type with the expected type.

The checks live in [script.lean](script.lean). Run them through the top-level
runner:

```bash
python3 -B -m pylean.tutorial_type_checker 01
```

Expected result:

```text
True : Prop
False : Prop
true_intro : True
true_is_true : True
```
