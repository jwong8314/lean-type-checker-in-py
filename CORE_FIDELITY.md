# Core Fidelity Rule

Never introduce a tutorial `Expr` node for something that is not a real Lean
core expression form.

This matters pedagogically: a fake node can make the student think the kernel
has a primitive that Lean does not actually have. When the real Lean kernel
represents something as a constant applied with `App`, the tutorial compiler
should do the same.

For Chapter 5, this means:

- `False.elim` is `Const("False.elim")` applied to the target proposition and a
  proof of `False`.
- `Or` is `Const("Or")` applied to its two proposition arguments.
- `Or.inl`, `Or.inr`, and `Or.elim` are constants applied with `App`.
- The `contradiction` and `cases` tactics are elaboration conveniences only.
  They disappear before kernel checking.

Custom expression nodes are appropriate only when they correspond to a real
core expression form being taught, or when the tutorial explicitly labels them
as a temporary approximation and removes them before presenting the Lean-core
story.
