# Instrumented Lean Kernel

This folder holds a small patch to Lean 4's C++ kernel. With the patch applied,
Lean prints the raw expression tree of each declaration immediately before the
kernel type checks it. The tutorial uses these traces as its ground truth: the
trees a chapter builds by hand should be the trees real Lean sends to its
kernel.

## What The Patch Does

[kernel-trace.patch](kernel-trace.patch) touches one file,
`src/kernel/environment.cpp`. Every declaration enters the kernel through
`environment::add(declaration, check)`. The patch adds one call at the top of
that function, before any checking happens:

```cpp
if (check) trace_declaration(d);
```

`trace_declaration` prints the declaration's type and value using only the
kernel's own `expr` accessors, so the output is exactly what the type checker
is about to receive: after parsing, elaboration, and tactic execution.

Before each declaration it also prints a `reference` block for every constant
the declaration mentions that has not been printed yet, then for the constants
those mention, and so on. These are constants already in the environment (for
example `Eq` or `HAdd.hAdd` from the standard library). The kernel is not
checking them now; they are printed so that a trace is self-contained and can
be replayed by another kernel with no access to Lean's library files.

- A referenced inductive type is printed with all its constructors.
- A referenced definition is printed with its value, because the kernel may
  unfold it.
- Referenced theorems, axioms, opaque constants, and recursors are printed
  with their type only.

The patch applies to upstream commit
`8f856a360656b71aca31a287a92f974176030eca`, the same commit as the reference
snapshot in [cpp-lean-kernel](../cpp-lean-kernel).

## Using It

Tracing is off unless `LEAN_KERNEL_TRACE` is set. Its value is a name prefix;
`*` traces everything. The trace goes to stderr.

```bash
LEAN_KERNEL_TRACE=MyNat lean4-src/build/release/stage1/bin/lean MyNatSuccAdd.lean
```

## Reading A Trace

```text
[kernel-trace] theorem <name>
  universe params: <names>        (only if there are any)
  params: <n>                     (inductive types: how many leading arguments are parameters)
  safety: unsafe | partial        (only for definitions the kernel does not fully check)
  type:
    <expression tree>
  value:
    <expression tree>
[kernel-trace] end <name>
```

`<kind>` in place of `theorem` is one of `definition`, `axiom`, `opaque`,
`mutual definition`, `inductive`, or `constructor`; or `reference` followed by
one of those, `recursor`, or `quot`.

Each line of a tree is one kernel `Expr` node; its children are indented below
it.

| Node | Children | Meaning |
| --- | --- | --- |
| `Sort <level>` | none | `Prop` is `Sort 0`, `Type` is `Sort 1` |
| `Const <name> [levels]` | none | a global constant |
| `BVar <n>` | none | bound variable, counted outward from the nearest binder (de Bruijn index) |
| `App` | function, argument | application of one argument |
| `Lam <name> (<binder>)` | domain, body | `fun` |
| `Pi <name> (<binder>)` | domain, body | `forall` and `->` |
| `Let <name>` | type, value, body | `let` |
| `Lit nat <n>` / `Lit string "<s>"` | none | literal |
| `MData` | expression | metadata wrapper, ignored by the checker |
| `Proj <structure> <index>` | expression | structure field projection |

`FVar` and `MVar` can never appear: the kernel rejects declarations that
contain them.

## Checked Examples

The patched binary was run on the proofs already in this repository. The
captured output is in [traces](traces):

| Trace | Source | Declarations |
| --- | --- | --- |
| [MyNatSuccAdd.trace](traces/MyNatSuccAdd.trace) | [MyNatSuccAdd.lean](../MyNatSuccAdd.lean) | the whole file, traced with `*` |
| [rewrite_step.trace](traces/rewrite_step.trace) | [examples/rewrite_step.lean](examples/rewrite_step.lean) | Chapter 3's `rewrite_step`, traced with `MyNat` |

Each trace has a `.decompiled.lean` file next to it, produced by
[decompile.py](decompile.py). [SUGAR.md](SUGAR.md) goes through the examples
one kind of syntax at a time.

The Chapter 1 trace is the whole chapter in three declarations:

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
```

Things the `MyNat` trace shows that the Lean source hides:

- One `inductive` line produces about twenty kernel declarations: `MyNat`,
  its constructors, then helpers such as `MyNat.casesOn`, `MyNat.below`, and
  `MyNat.noConfusion`. The recursor `MyNat.rec` is generated inside the kernel
  and never passes through `add`, so it shows up only as a `reference`.
- `MyNat.add` is sent first as an `axiom`, several times. The elaborator adds
  a temporary placeholder while it compiles the recursive definition, then
  sends the real `definition MyNat.add`.
- `a + zero` is not `MyNat.add a zero`. It is
  `HAdd.hAdd MyNat MyNat MyNat (instHAdd MyNat MyNat.instAdd) a zero`.
- `my_add_zero`, written `by rfl`, reaches the kernel as `Eq.refl MyNat (a + zero)`.
  The kernel accepts it only by unfolding `+` and computing.

## Decompiling A Trace

```bash
python3 instrumentation/decompile.py instrumentation/traces/MyNatSuccAdd.trace
python3 instrumentation/decompile.py instrumentation/traces/MyNatSuccAdd.trace --only MyNat.zero_add --explicit
python3 instrumentation/roundtrip.py MyNatSuccAdd.lean
```

`decompile.py` turns trees back into short Lean text by hiding the arguments
type inference can restore. `roundtrip.py` proves the text is equivalent: it
feeds the text back to Lean and checks the kernel receives the identical tree.

## Building

```bash
git clone https://github.com/leanprover/lean4.git lean4-src
cd lean4-src
git checkout 8f856a360656b71aca31a287a92f974176030eca
git apply ../instrumentation/kernel-trace.patch
cmake --preset release
make -C build/release -j stage1
```

The build needs CMake, a C++ compiler, GMP, and libuv. `lean4-src/` is ignored
by git.
