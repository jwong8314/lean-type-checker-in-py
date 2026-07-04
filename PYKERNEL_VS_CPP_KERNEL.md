# Final Python Kernel vs. Lean C++ Kernel

This project's final Python kernel is a tutorial-sized Lean-style checker. It
can check the natural-number commutativity development in `MyNatSuccAdd.lean`,
but it is not trying to be a complete Lean 4 kernel. The vendored
`cpp-lean-kernel/` directory is a reference snapshot of Lean 4's real C++
kernel implementation, centered on `src/kernel/type_checker.cpp` and
`src/kernel/type_checker.h`.

## What the final Python kernel supports

The final Python kernel is the Chapter 7 checker in `chapters/07_comm/`. It
inherits the features built in Chapters 1-4 and adds just enough equality
machinery to check the commutativity layer for `MyNat`.

Its core expression language includes:

- Sorts: `Prop` and `Type`.
- Global constants and local variables.
- Function application.
- Dependent function types, represented as `Pi`.
- Lambda terms.
- Equality propositions.
- Reflexivity proofs through `rfl` / `Refl`.
- A small recursive type registration mechanism for declarations such as
  `MyNat`, with constructors like `zero` and `succ`.
- A small induction proof term for recursive types.

Its computation and definitional equality are deliberately narrow:

- It supports beta reduction for lambda application.
- It supports a pluggable reducer table, currently used for `add`.
- The `add` reducer knows the two recursive equations for addition on the
  second argument:
  - `a + zero` reduces to `a`.
  - `a + succ b` reduces to `succ (a + b)`.
- Definitional equality is essentially normalized structural equality in the
  tutorial fragment, not Lean's full convertibility algorithm.

The final chapter adds proof constructors needed by the commutativity script:

- `EqSymm` for symmetry of equality.
- `EqTrans` for transitivity of equality.
- `EqCongrAddLeft` for congruence under adding the same left argument.
- `SuccCongr` inherited from Chapter 3 for congruence under `succ`.

The parser/elaboration layer is also intentionally tiny. It can parse the small
subset used by the tutorial scripts: `constant`, `inductive`, constructor
lines, simple `def`, simple `theorem`, `forall`, arrows, equality, addition,
lambda syntax, and a small tactic fragment containing `rfl`, `rw`, `induction`,
and `exact`. Those tactics are not kernel primitives; they are lowered into
proof terms before checking.

## What the C++ Lean kernel supports that the Python kernel does not

The C++ kernel is the real Lean kernel machinery, not a tutorial model. Its
expression language is much richer:

- Universe levels and universe parameters.
- Bound variables, free variables, and rejected metavariables at kernel-check
  time.
- Constants with universe instantiations.
- Lambdas and dependent Pis with binder information.
- Let expressions.
- Literals such as natural numbers and strings.
- Metadata nodes.
- Structure projections.

Its environment and declaration model is also broader:

- Axioms.
- Definitions with reducibility hints.
- Theorems.
- Opaque declarations.
- Quotient declarations.
- Mutual definitions.
- Inductive declarations with parameters and multiple inductive types.
- Safety tracking for safe, unsafe, and partial declarations.

Its type checker implements much more than the Python checker:

- Full universe checking.
- Local context management using kernel free variables.
- Type inference and checking modes with caches.
- Weak-head normalization with beta, zeta, projection, recursor, quotient, and
  delta reduction.
- Controlled unfolding of definitions using reducibility hints.
- Definitional equality with lazy delta reduction, eta expansion, structural
  eta for records, proof irrelevance, unit-like optimization, offset/numeral
  handling, and failure caching.
- Built-in reduction support for natural-number operations and literals.
- Projection typing and projection reduction.
- Recursor reduction for inductives.
- Quotient reduction.
- Interrupt checks, diagnostics, and kernel exceptions.

In short, the C++ kernel is designed to validate arbitrary elaborated Lean
terms from the full Lean environment. The Python kernel is designed to make the
central ideas visible on a single tutorial path.

## Main architectural differences

The Python kernel uses plain dataclasses for syntax and simple dictionaries for
the environment and local context. Each chapter subclasses the previous checker,
so new features are added gradually and explicitly. This makes it easy to read,
but it also means features are special-purpose and often hard-coded for the
`MyNat` examples.

The C++ kernel uses Lean's runtime object representation, reference-counted
objects, hash-consing-style expression metadata, persistent names and levels,
specialized maps/caches, and a real `environment`. It is optimized for
correctness and performance at Lean scale.

The Python kernel's recursive-type support is intentionally minimal. It can
register a recursive type and derive a simple induction case type for recursive
arguments. The C++ kernel has a full inductive declaration system, recursors,
constructors, projections, reduction rules, parameters, indices, and support
for mutual inductives.

The Python kernel's equality story is explicit and tutorial-oriented:
symmetry, transitivity, reflexivity, and a couple of congruence principles are
represented as custom Python expression nodes. The C++ kernel does not need
these hard-coded tutorial proof nodes in the same way; it checks elaborated
proof terms in Lean's general dependent type theory and uses its convertibility
checker to decide definitional equality.

## Practical takeaway

The final Python kernel is best understood as a pedagogical slice of Lean:
small enough to follow, but strong enough to check a nontrivial natural-number
proof script about addition commutativity and associativity.

The C++ kernel is the production kernel: general, universe-polymorphic,
performance-conscious, and responsible for checking the fully elaborated terms
produced by Lean itself.

So the difference is not just implementation language. The Python kernel has a
small, hand-shaped feature set for one tutorial development. The C++ kernel is
Lean's general trusted core.
