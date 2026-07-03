# Chapter 1: True and False

Goal: build the smallest useful checker.

In this chapter, propositions are just types and proofs are terms:

```text
Prop : Type
True : Prop
False : Prop
True.intro : True
```

The checks live in [script.lean](script.lean). Run them through the top-level
runner:

```bash
python3 -B -m pylean.tutorial_type_checker 01
```

Expected result:

```text
TrueProp : Prop
true_intro : TrueProp
true_is_true : TrueProp
```

## 1. The Parser Already Compiled The Script

By the time Chapter 1's `TypeChecker` runs, it is not reading raw Lean syntax
anymore.

[solution_runner.py](../../solution_runner.py) and the parser have already done
the "compilation" step for this tiny tutorial language:

```lean
theorem true_intro : TrueProp := True.intro
```

has already been turned into a declaration with two important pieces:

```text
expected type: Const("TrueProp")
proof term:    Const("True.intro")
```

Your job in `solution.py` is to check that the theorem is valid:

1. Infer the type of the proof term.
2. Compare that inferred type with the expected theorem type.
3. Accept the declaration only if those types match.

So the checker asks:

```text
Does Const("True.intro") really have type Const("TrueProp")?
```

The environment initially knows:

```text
True       : Prop
False      : Prop
True.intro : True
```

So `infer(Const("True.intro"))` returns `Const("True")`.

Then `check` compares:

```text
actual:   Const("True")
expected: Const("TrueProp")
```

In this chapter, `TrueProp` was defined as `True`, so the checker records a
transparent definition:

```text
TrueProp := True
```

Before the final equality comparison, it unfolds `Const("TrueProp")` to
`Const("True")`. Then `defeq` itself is just exact structural equality:

```text
defeq(Const("True"), Const("True")) = true
defeq(Const("True"), Const("TrueProp")) = false
```

That is why the theorem is accepted without adding a special equality shortcut.

## 2. Expression Trees

The type checker does not care about punctuation, keywords, or pretty syntax.
It cares about expression trees.

For this theorem:

```lean
theorem true_intro : TrueProp := True.intro
```

the relevant tree is intentionally tiny:

```text
Declaration(
  name     = "true_intro",
  expected = Const("TrueProp"),
  expr     = Const("True.intro"),
)
```

A good declaration is one where the expression's inferred type matches the
expected type:

```text
expr     = Const("True.intro")
infer    = Const("True")
expected = Const("TrueProp")
result   = accepted, because TrueProp unfolds to True before exact comparison
```

A bad declaration is one where the proof term cannot have the expected type:

```text
expr     = Const("False")
infer    = Prop
expected = Const("TrueProp")
result   = rejected, because a proposition is not a proof of TrueProp
```

Another bad declaration is an unknown constant:

```text
expr     = Const("made_up_proof")
result   = rejected, because made_up_proof is not in the environment
```

<details>
<summary>Optional refresher: from tokens to AST</summary>

A parser starts with text:

```lean
theorem true_intro : TrueProp := True.intro
```

It first recognizes tokens:

```text
theorem, true_intro, :, TrueProp, :=, True.intro
```

Then it groups those tokens into an AST, or abstract syntax tree:

```text
theorem
  name: true_intro
  type: TrueProp
  body: True.intro
```

Finally, the tutorial lowers that AST into our Python expression tree:

```text
expected type: Const("TrueProp")
proof term:    Const("True.intro")
```

The type checker's job starts here. It checks that the AST is well typed. It is
not responsible for tokenizing or parsing the original source text.

</details>

## 3. Sorts And Types

The same example also shows why Chapter 1 needs `Sort`.

Lean has a hierarchy of universes. This tutorial starts with only the first two:

```text
Prop : Type
Type : Type 1
```

In the Python expression tree:

```text
Prop  = Sort(0)
Type  = Sort(1)
Type1 = Sort(2)
```

That is why `infer(Sort(level))` returns `Sort(level + 1)`.

For ordinary constants, the checker looks up their type in the environment:

```text
infer(Const("True"))       = Prop
infer(Const("False"))      = Prop
infer(Const("True.intro")) = Const("True")
```

This is the propositions-as-types idea in its smallest form:

```text
True       : Prop
True.intro : True
```

`True` is a proposition. `True.intro` is a proof of that proposition.

So when we check:

```lean
theorem true_intro : TrueProp := True.intro
```

we are checking that:

```text
True.intro is a proof of TrueProp
```

and that succeeds because `TrueProp` is a transparent definition introduced by:

```lean
def TrueProp : Prop := True
```

## 4. Hints If You Get Stuck

Use these hints in order. Stop as soon as you can keep going.

### Hint 1: Implement The Truth Constants

Start by making sure the chapter can talk about the names it needs:

```text
True
False
True.intro
TrueProp
```

The initial environment should know:

```text
True       : Prop
False      : Prop
True.intro : True
```

`TrueProp` is declared by `script.lean`, so the runner registers it after the
checker accepts:

```lean
def TrueProp : Prop := True
```

### Hint 2: Start With A Dumb Checker

As a first draft, it is okay to write a checker that accepts everything. That is
not correct, but it proves the runner and parser are connected.

The shape is:

```text
check(expr, expected):
  accept
```

This should feel suspicious. It would accept nonsense, so we tighten it next.

### Hint 3: Reject False Proofs

Make the checker reject a term that is only a proposition when a proof is
expected.

For example, this should fail:

```text
expected = Const("TrueProp")
expr     = Const("False")
```

Why? Because `False : Prop`. `False` is a proposition, not a proof of
`TrueProp`.

### Hint 4: Add Sorts Properly

Now make `Sort` real:

```text
infer(Prop) = Type
infer(Type) = Type 1
```

In code, that is the rule:

```text
infer(Sort(level)) = Sort(level + 1)
```

This lets the checker validate declarations like:

```lean
def TrueProp : Prop := True
```

because it can check that `Prop` itself has a type.

### Hint 5: Use Environment Lookup For Constants

For `Const(name)`, look in the environment:

```text
infer(Const("True"))       = Prop
infer(Const("False"))      = Prop
infer(Const("True.intro")) = Const("True")
```

If the constant is missing, reject it. Unknown names should not type-check.

### Hint 6: Implement Check As Infer Plus Equality

The final shape is:

```text
check(expr, expected):
  actual = infer(expr)
  unfold transparent definitions in actual and expected
  accept only if the unfolded expressions are exactly equal
```

`defeq` itself should stay boring:

```text
defeq(left, right):
  return left == right
```

The definition table does the Lean-style transparency work instead:

```lean
def TrueProp : Prop := True
```

so `check` compares `Const("True")` with `Const("True")`, not with
`Const("TrueProp")`.

That is enough to validate:

```lean
theorem true_intro : TrueProp := True.intro
theorem true_is_true : TrueProp := true_intro
```
