# Chapter 4: `rfl` Elaboration

This chapter keeps the Chapter 3 kernel, but moves `rfl` into the explicit
elaboration phase.

The source proof:

```text
fun x => rfl
```

is elaborated before kernel checking into:

```text
fun x => Refl(MyNat, x)
```

This mirrors Lean's split: the frontend elaborates `rfl` into `Eq.refl`, then
the kernel checks the resulting proof term.

Trace it with:

```bash
python3 -B -m pylean.tutorial_type_checker 04 --trace-elab
```

