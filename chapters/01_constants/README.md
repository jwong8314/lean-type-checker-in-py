# Chapter 1: Constants

Goal: accept the first three real declarations.

```lean
def TrueProp : Prop := True
theorem true_intro : TrueProp := True.intro
theorem true_is_true : TrueProp := true_intro
```

Files for this chapter:

| File | What it is |
| --- | --- |
| [examples.lean](examples.lean) | the Lean source |
| [examples.trace](examples.trace) | what Lean's kernel received for it |
| [examples.decompiled.lean](examples.decompiled.lean) | the trace, printed back as Lean |

You will edit `kernel/typechecker.py`. Run the tests with:

```bash
pytest tests/test_ch1_constants.py
```

## 1. What The Kernel Receives

Open [examples.trace](examples.trace). It was produced by real Lean, patched
to print each declaration right before type checking it. The last three blocks
are:

```text
[kernel-trace] definition TrueProp
  type:
    Sort 0
  value:
    Const True
[kernel-trace] end TrueProp
[kernel-trace] theorem true_intro
  type:
    Const TrueProp
  value:
    Const True.intro
[kernel-trace] end true_intro
[kernel-trace] theorem true_is_true
  type:
    Const TrueProp
  value:
    Const true_intro
[kernel-trace] end true_is_true
```

Two kinds of node appear:

- `Const name`: a reference to something already declared.
- `Sort 0`: the type of propositions, written `Prop`. `Sort 1` is `Type`.

`kernel/trace.py` already parses this text into the classes in
`kernel/expr.py`, so `Const True` arrives as `Const("True")` and `Sort 0` as
`Sort(Zero())`. You never parse anything.

The earlier blocks declare `True`, `True.intro`, and `False`, plus helpers
Lean generates for them. Inductive types are Chapter 3. For now the test
harness adds those to the environment without checking them, so when your code
runs it can already look up:

```text
True       : Sort 0
True.intro : True
False      : Sort 0
```

## 2. The Job

For each `definition` or `theorem`, the kernel is given a name, a type, and a
value. It must decide: does the value really have that type?

```text
add_definition(env, name, universe_params, type, value, kind):
  1. the type must itself be a type         infer(type) is a Sort
  2. a theorem's type must be a proposition infer(type) is Sort 0
  3. compute the value's type               value_type = infer(value)
  4. it must match the declared type        is_def_eq(value_type, type)
  5. record the constant                    env.add(...)
```

Everything else in the kernel exists to make steps 3 and 4 work on bigger
expressions.

## 3. What To Implement

All in `kernel/typechecker.py`. Ignore the `universe_params` and `levels`
arguments until Chapter 3; in this chapter they are always empty.

| Function | This chapter's version |
| --- | --- |
| `infer`, `Const` case | look the name up in `self.env` and return its type |
| `infer`, `Sort` case | `Sort(l)` has type `Sort(Succ(l))` |
| `whnf_core` | return the expression unchanged (Chapter 2 fills this in) |
| `unfold_definition` | if the expression is a `Const` naming a definition with a value, return the value; otherwise `None` |
| `whnf` | call `unfold_definition` until it returns `None` |
| `ensure_sort` | `whnf` the argument; it must be a `Sort`, else raise `KernelError` |
| `is_prop` | the type of the argument, after `whnf`, is `Sort(Zero())` |
| `is_def_eq` | equal as trees, or equal after `whnf` on both sides |
| `add_axiom`, `add_definition` | the five steps above |

`env.get(name)` raises `KernelError` for an unknown name, which is exactly the
behavior you want. `env.add(info)` raises if the name is taken.

## 4. Why `true_intro` Needs Unfolding

```text
value type:     infer(Const("True.intro")) = Const("True")
declared type:                               Const("TrueProp")
```

These are different trees. They are equal only because `TrueProp` was
*defined* as `True`. Replacing a defined constant with its value is called
delta reduction, and `is_def_eq` ("definitionally equal") is equality up to
that kind of computation. The real kernel does the same thing here, in
`type_checker::is_def_eq`.

A `theorem`'s value is also stored. The kernel almost never unfolds it, but it
may.

## 5. What Must Be Rejected

A type checker that accepts everything passes the first test. The others
check that you reject:

- an unknown constant;
- `theorem bad : TrueProp := False`, because `False` has type `Prop`, not `TrueProp`;
- `theorem bad : False := True.intro`;
- a declaration whose "type" is not a type, such as `axiom bad : True.intro`;
- declaring the same name twice.

## Hints

<details>
<summary>Hint 1: the shape of <code>infer</code></summary>

`infer` is a `match` on the node class. Each `case` returns a type. This
chapter fills in two cases; every later chapter adds more.

</details>

<details>
<summary>Hint 2: <code>is_def_eq</code> in three lines</summary>

```python
if t == s:
    return True
return self.whnf(t) == self.whnf(s)
```

This is enough for Chapter 1 and wrong in general. Chapter 2 replaces it.

</details>

<details>
<summary>Hint 3: which constants unfold</summary>

`self.env.find(name)` returns a `ConstantInfo` or `None`. Unfold when
`info.kind` is `"definition"` or `"theorem"` and `info.value` is not `None`.
Axioms, inductive types, and constructors have no value.

</details>

## In Lean's Source

| Here | [cpp-lean-kernel/src/kernel](../../cpp-lean-kernel/src/kernel) |
| --- | --- |
| `add_definition` | `environment::add_definition`, `add_theorem` in `environment.cpp` |
| `infer` | `type_checker::infer_type_core` in `type_checker.cpp` |
| `Const` case | `type_checker::infer_constant` |
| `unfold_definition` | `type_checker::unfold_definition` |
