# Build Lean's Kernel From Scratch

A workshop in five chapters. You write a type checker in Python, and it is
tested against what the real Lean 4 kernel was actually asked to check.

Nothing here is a simplified model of Lean. Lean was patched to print every
declaration, as a raw expression tree, immediately before its kernel type
checks it. Those printed trees are your input. By the end, your kernel accepts
an ordinary Lean file, with pattern matching, type classes, and tactic proofs
of commutativity and associativity of addition, exactly as Lean elaborated it.

```text
  Lean source  ──(real Lean: parse, elaborate, run tactics)──▶  expression trees
                                                                      │
                                         instrumented kernel prints them (the trace)
                                                                      │
                                                                      ▼
                                                    your kernel/ checks the same trees
```

## Chapters

| | Chapter | You build | Checks |
| --- | --- | --- | --- |
| 0 | [Preamble](chapters/00_preamble/README.md) | nothing; read this first | |
| 1 | [Constants](chapters/01_constants/README.md) | environment, `infer` for constants and sorts, unfolding | `true_intro` |
| 2 | [Functions](chapters/02_functions/README.md) | bound variables, substitution, `Pi`/`Lam`/`App`, beta, definitional equality | `modus_ponens` |
| 3 | [Inductive types](chapters/03_inductive/README.md) | universe levels, `inductive`, recursor generation and computation | `MyNat`, `add` |
| 4 | [Equality](chapters/04_equality/README.md) | proof irrelevance, eta; proofs by computation and by induction | `add_comm`, written as explicit terms |
| 5 | [Sugar](chapters/05_sugar/README.md) | projections; then the `rw` tactic itself | the real [MyNatSuccAdd.lean](MyNatSuccAdd.lean), tactics and all |

Chapters 1 to 4 use Lean files that begin with `prelude` (import nothing) and
spell every term out, so that the tree the kernel receives is the tree you
see in the source. Chapter 5 drops both restrictions, shows how much the
elaborator had been hiding, and has you implement one piece of it.

Each chapter folder has:

```text
README.md                 the handout: what to build, the rules, hints
examples.lean             Lean source
examples.trace            what Lean's kernel received for it (your test input)
examples.decompiled.lean  the trace printed back as readable Lean
```

## Setup

```bash
python3 -m venv .venv
```

```bash
.venv/bin/pip install -r requirements.txt
```

You do not need Lean installed. The traces are checked in.

## Working Through It

Your code goes in [kernel/](kernel). Functions to write are marked
`raise NotImplementedError("TODO: ...")`.

| File | Contents | Chapter |
| --- | --- | --- |
| `kernel/expr.py` | expression and level classes | given |
| `kernel/trace.py` | reads a trace into those classes | given |
| `kernel/environment.py` | the table of accepted constants | given |
| `kernel/check.py` | replays a trace through your kernel | given |
| `kernel/typechecker.py` | `infer`, `whnf`, `is_def_eq`, adding declarations | 1, 2, 3, 4, 5 |
| `kernel/subst.py` | `instantiate`, `abstract` | 2, 3 |
| `kernel/level.py` | comparing universe levels | 2, 3 |
| `kernel/inductive.py` | inductive types and recursors | 3 |
| `kernel/rewrite.py` | the `rw` tactic | 5 |

Run one chapter's tests, or all of them:

```bash
.venv/bin/pytest tests/test_ch1_constants.py
```

```bash
.venv/bin/pytest
```

Replay a whole trace and see what your kernel says about each declaration:

```bash
.venv/bin/python -m kernel.check chapters/04_equality/examples.trace
```

The tests check both directions: real declarations must be accepted, and
wrong proofs, such as `Eq.refl a` offered for `zero + a = a`, must be rejected.

## Reference Solution

[solution/kernel/](solution/kernel) is a complete implementation. Try each
chapter before reading it.

```bash
KERNEL_IMPL=solution .venv/bin/pytest
```

`kernel/` is generated from the solution by removing the marked regions:

```bash
.venv/bin/python tools/make_template.py --force
```

That overwrites `kernel/`, including any work in it.

## What This Kernel Leaves Out

It is a faithful subset, not all of Lean's kernel:

- Mutual and nested inductive types are not supported. Imported ones are
  accepted without generating a recursor.
- No structure eta (`⟨p.1, p.2⟩ = p`), and no quotient types.
- Number literals are supported only by unpacking them one `succ` at a time;
  Lean computes on them with big-integer arithmetic.
- `unsafe` and `partial` definitions are recorded, not checked.
- Imported declarations are trusted, as Lean trusts compiled library files.
- No caching, so it is slow on large inputs.

## How The Traces Are Made

[instrumentation/](instrumentation/README.md) has the patch to Lean's C++
kernel, build instructions, the trace format, and two tools:

- `decompile.py` prints a trace as short, readable Lean by hiding the
  arguments type inference can restore.
- `roundtrip.py` proves that text is equivalent, by feeding it back to Lean
  and comparing kernel trees.

[instrumentation/SUGAR.md](instrumentation/SUGAR.md) is a tour of what each
piece of Lean syntax becomes.

[cpp-lean-kernel/](cpp-lean-kernel) is a copy of the kernel's C++ source at
the same commit, for reading next to your Python. Each chapter ends with a
table mapping your functions to theirs.

## Earlier Version

[old/](old) holds the first version of this workshop, which used a
hand-written parser for a Lean-like language and a simplified checker. It is
kept for reference and is not maintained.
