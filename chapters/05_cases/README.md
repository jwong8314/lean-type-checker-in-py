# Chapter 5: Cases

Goal: introduce disjunctions and the `cases` tactic before induction.

This chapter adds:

1. `Or(left, right)` as a proposition.
2. `OrInl(left, right, proof)` and `OrInr(left, right, proof)` as explicit
   proof constructors.
3. `OrCases(target, left_case, right_case)` as the kernel proof object produced
   by `cases h with ...`.
4. `FalseElim(goal, proof)` as the proof object behind the tiny
   `contradiction` tactic.

The important split is the same as with `rfl`: `cases` and `contradiction` are
not kernel magic. They elaborate into ordinary proof terms before the checker
runs.

Try it:

```bash
python3 -B -m pylean.tutorial_type_checker 05 --trace-elab
```

