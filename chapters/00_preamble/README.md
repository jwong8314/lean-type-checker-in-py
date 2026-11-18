# Chapter 0: Everything Is An Expression

This chapter is a conceptual preamble. There is no code and nothing to run. The goal is to establish the way Lean thinks
about programs, types, propositions, and proofs before we build a type checker.

## 1. Everything Is An Expression

Lean does not have completely separate languages for:

- values
- types
- propositions
- proofs

All of them are represented by expressions.

For example:

```lean
3
Nat
3 = 3
rfl
```

These expressions have types:

```text
3     : Nat
Nat   : Type
3 = 3 : Prop
rfl   : 3 = 3
```

So Lean repeatedly asks the same question:

```text
expression : type
```

A type itself is just an expression whose type is some universe such as `Type`
or `Prop`.

This is the foundation of the type checker we will build. The checker does not
need one separate mechanism for checking values and another for checking
proofs. It checks expressions against expected types. A proof is simply an
expression whose type is a proposition.

## 2. Sorts: The Types Of Types

At the top of Lean's hierarchy are expressions called `Sort`.

The important forms are:

```text
Prop
Type
Type 1
Type 2
...
```

Internally:

```text
Prop   = Sort 0
Type   = Sort 1
Type 1 = Sort 2
Type 2 = Sort 3
```

There is a slight surface-syntax offset:

```lean
#check Prop    -- Prop : Type
#check Type    -- Type : Type 1
#check Type 1  -- Type 1 : Type 2
```

The hierarchy prevents a contradiction like:

```text
Type : Type
```

which would make the system inconsistent. Instead:

```text
Type u : Type (u + 1)
```

Think of `Sort` as a type system over types themselves. It lets the checker
express not only that a term has a type, but also that a type belongs to a
particular universe.

## 3. Propositions As Types

`Prop` is the universe of propositions. A proposition is a type whose
inhabitants are proofs.

For example:

```text
2 + 2 = 4 : Prop
```

A proof of it is a term:

```text
rfl : 2 + 2 = 4
```

This is the propositions-as-types idea:

```text
proposition = type
proof       = value of that type
```

For example, each of these is a type in `Prop`:

```text
P ∧ Q
P ∨ Q
P → Q
∀ x, P x
∃ x, P x
```

To prove one, you construct a value of that type. To check a proof, infer the
type of the proof expression and compare it with the proposition that is
expected.

## 4. Equality Is An Inductive Type

Lean's equality is not built in as an external judgment. It is represented by
a type:

```text
Eq a b
```

written:

```text
a = b
```

Conceptually:

```lean
inductive Eq {α : Sort u} (a : α) : α → Prop where
  | refl : Eq a a
```

The basic constructor is:

```text
rfl : a = a
```

Why can this prove:

```text
2 + 2 = 4
```

Lean reduces both sides computationally, sees that they are definitionally
equal, and then uses reflexivity. This is why `rfl` can prove equalities whose
two sides are not written identically but compute to the same expression.

## 5. Why This Matters For The Kernel

The kernel does not check the surface syntax directly. Later, the parser and
elaboration layer will turn Lean syntax into expression trees. The kernel then
checks those expression trees using the same basic relation everywhere:

```text
term : type
```

In this workshop you never write that parser or elaboration layer. Real Lean
does it, and a patched copy of Lean's kernel prints the resulting expression
trees. Those printed trees are the input to the kernel you will build.

Chapter 1 begins with this smallest useful question for truth values. Later
chapters add functions, inductive types, and equality, and each new feature
still produces expressions that must have types. Chapter 5 returns to the
elaboration layer and shows what it had been doing all along.
