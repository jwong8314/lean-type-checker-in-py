# Lean C++ Kernel Snapshot

This directory vendors a small reference snapshot of Lean 4's C++ kernel code,
centered on:

```text
src/kernel/type_checker.cpp
src/kernel/type_checker.h
```

Source: https://github.com/leanprover/lean4

Upstream commit:

```text
8f856a360656b71aca31a287a92f974176030eca
```

Copied directories:

```text
src/include
src/initialize
src/kernel
src/library
src/runtime
src/util
```

These are included so `type_checker.cpp` can be read alongside its key local
dependencies such as expressions, declarations, environments, instantiation,
exceptions, reducers, inductives, quotations, and runtime utility headers.

This folder is intended as source reference material for the Python tutorial,
not as an integrated build target for this repository.

The quoted-include closure of `src/kernel/type_checker.cpp` and
`src/kernel/type_checker.h` is present in this snapshot. Some copied peripheral
files still refer to generated build headers such as `githash.h` or external
LLVM headers; those are outside the scope of this reference vendor.

The upstream Lean files are licensed under Apache 2.0; see [LICENSE](LICENSE).
