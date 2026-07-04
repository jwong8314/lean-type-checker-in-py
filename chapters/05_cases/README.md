# Chapter 5: Cases

Goal: introduce disjunctions and the `cases` tactic before induction.

This chapter adds:

1. `Or` as an ordinary constant with type `Prop -> Prop -> Prop`.
2. `Or.inl` and `Or.inr` as ordinary constants used through `App`.
3. `Or.elim` as the ordinary eliminator that the `cases` tactic elaborates to.
4. `False.elim` as the ordinary constant that the tiny `contradiction` tactic
   elaborates to.

The important split is the same as with `rfl`: `cases` and `contradiction` are
not kernel magic. They elaborate into ordinary proof terms before the checker
runs. We deliberately do not add fake `Expr` nodes such as `FalseElim` or
`OrCases`; Lean core represents these as `Const` plus `App`, so the tutorial
does too.

Try it:

```bash
python3 -B -m pylean.tutorial_type_checker 05 --trace-elab
```
