# Lean C++ Snapshot: Compiler Pass Summary

This vendored `cpp-lean-kernel/` tree is mostly a kernel/runtime snapshot. It
does not include the full Lean compiler implementation source tree, but it does
include the important entry points and runtime pieces that show how compiled
Lean code flows toward C/native execution.

The useful way to read it is as this pipeline:

```text
Lean declarations
  -> kernel/environment checking
  -> compiler environment extensions
  -> LCNF compilation
  -> IR export
  -> C emission or IR interpretation
  -> C compiler/linker/runtime
```

## 1. Kernel and Environment Checking

Before compiler code generation matters, declarations must be accepted into the
Lean environment.

Relevant files:

- `src/kernel/type_checker.cpp`
- `src/kernel/type_checker.h`
- `src/kernel/declaration.h`
- `src/kernel/environment.*`

What this stage does:

- Checks that elaborated Lean terms are well typed.
- Validates constants, definitions, theorems, inductives, universes, lets,
  projections, and applications.
- Decides definitional equality through normalization and controlled unfolding.
- Stores declarations in the environment with metadata such as reducibility,
  opacity, theorem/definition status, inductive data, and safety.

This is not a compiler optimization pass, but it is the trusted gate before
anything can be compiled.

## 2. Import and Compiler Setup

Relevant file:

- `src/LeanIR.lean`

`LeanIR.lean` is the separate-process code generation driver. It loads the
target module, imports private data and IR signatures, initializes compiler
environment extensions, and prepares the environment for runtime codegen.

What this stage does:

- Loads the module setup from JSON.
- Imports the target module with access to private declarations.
- Loads available IR signatures from dependencies.
- Initializes compiler-related environment extensions such as:
  - `[csimp]` replacement data.
  - instance/class data needed by compiler-side processing.
  - match-extension data.
  - IR declaration maps.
- Marks extern declarations and keeps already-compiled declarations visible to
  the compiler.

This is mostly orchestration: it makes sure the later passes have the same
environment view as the main Lean process.

## 3. Resume Postponed Compilation

Relevant file:

- `src/LeanIR.lean`

Lean can postpone compilation of declarations while elaborating a module.
`LeanIR.lean` collects those postponed declarations and resumes compilation for
each one.

What this stage does:

- Reads postponed declaration entries from the environment.
- Rebuilds the postponed-compilation map so dependency order can be managed.
- Calls `resumeCompilation` on each pending declaration.
- Emits compiler diagnostics as Lean messages.

This is where the real Lean compiler pipeline is invoked. In this snapshot,
the implementation is imported from Lean modules such as:

- `Lean.Compiler.LCNF.Main`
- `Lean.Compiler.LCNF.PhaseExt`
- `Lean.Compiler.LCNF.EmitC`
- `Lean.Compiler.IR.CompilerM`

The detailed LCNF pass implementations are not present as C++ files in this
vendor directory.

## 4. LCNF Lowering and Optimization

Relevant imported modules:

- `Lean.Compiler.LCNF.Main`
- `Lean.Compiler.LCNF.PhaseExt`

LCNF is Lean's lower-level compiler representation, roughly where high-level
Lean declarations become a simpler first-order/control-flow-like form suitable
for runtime code generation.

At a high level, this stage is responsible for transformations such as:

- Lowering elaborated declarations into compiler IR.
- Making control flow explicit.
- Representing local functions, join points, cases, and returns.
- Applying compiler phase extensions.
- Respecting compiler-specific simplifications and replacement declarations,
  including `[csimp]` replacements.
- Preparing code for reference-counting and runtime object operations.

Because the actual `Lean.Compiler.LCNF.*` source files are not included in this
snapshot, this document should not be read as a line-by-line inventory of the
LCNF optimizer. It is a map of the pass role visible from this vendor copy.

## 5. IR Export

Relevant files:

- `src/LeanIR.lean`
- `src/library/ir_types.h`

After compilation, `LeanIR.lean` writes module IR data:

- `.ir.sig` data contains enough signature/import information for dependent
  modules.
- `.ir` data contains full IR entries for the current module.

`src/library/ir_types.h` exposes the C++ view of Lean's IR object tags and
types. It includes IR scalar/object types such as:

- `Float`, `Float32`
- `UInt8`, `UInt16`, `UInt32`, `UInt64`, `USize`
- `Object`, `TObject`, `Tagged`
- `Irrelevant`, `Void`

This stage serializes compiler output into module data so later modules and
runtime tools can find compiled declarations.

## 6. C Code Emission

Relevant file:

- `src/LeanIR.lean`

The line to watch is the call to:

```lean
Compiler.LCNF.emitC modName
```

What this stage does:

- Converts LCNF/IR declarations into C code.
- Emits calls into the Lean runtime object model.
- Emits constructors, projections, function calls, closures, reference-counting
  operations, case splits, and returns in a C representation.
- Writes the generated C file to disk.

The full emitter implementation is imported from `Lean.Compiler.LCNF.EmitC`;
the detailed source is not included in the vendored C++ snapshot.

## 7. Optional LLVM Backend Bindings

Relevant file:

- `src/library/llvm.cpp`

This file is not the optimizer itself. It is a set of C/C++ FFI bindings that
allows Lean-side code such as `Lean.Compiler.IR.EmitLLVM` to talk to LLVM.

What this stage can provide when Lean is built with LLVM support:

- LLVM target initialization.
- Creation of LLVM contexts/modules/builders/types/values.
- Bitcode/object emission support through the LLVM C API.

The actual LLVM IR emission logic lives on the Lean side; this file exposes the
native LLVM API to that Lean code.

## 8. IR Interpreter

Relevant files:

- `src/library/ir_interpreter.cpp`
- `src/library/ir_interpreter.h`
- `src/library/ir_types.h`

The IR interpreter evaluates Lean compiler IR directly instead of compiling it
to native code first. The source comments describe it as an interpreter for
lambda-RC IR.

What it does:

- Uses a homogeneous value stack for boxed objects and unboxed scalars.
- Maps IR variables to stack slots.
- Handles IR expressions such as:
  - constructors
  - projections
  - function applications
  - partial applications
  - boxed/unboxed conversions
  - literals
  - object sharing tests
  - constructor reuse/reset operations
- Handles function bodies such as:
  - variable declarations
  - join-point declarations
  - field updates
  - reference-count increments/decrements/deletes
  - case analysis
  - returns
  - jumps
- Tries to call native code when a compiled symbol is available.
- Falls back to interpreting IR when native code is unavailable.

This is a runtime execution path, not a compiler optimization pass, but it is
part of the compiled-code story.

## 9. C Compiler Wrapper

Relevant file:

- `src/Leanc.lean`

`Leanc.lean` is a small wrapper around the platform C compiler.

What it does:

- Computes Lean runtime include flags and linker flags.
- Honors `LEAN_CC` if the user wants a different C compiler.
- Supports printing C flags and linker flags.
- Invokes the underlying C compiler with the generated C source and Lean
  runtime libraries.

This is the final native build step after C emission.

## 10. Runtime Object Model

Relevant files:

- `src/include/lean/lean.h`
- `src/runtime/*`

Generated C code targets Lean's runtime object model. The runtime provides:

- Boxed scalar representation.
- Heap object layout.
- Constructors and closure objects.
- Arrays, strings, thunks, tasks, promises, references, and external objects.
- Reference counting operations.
- Borrowed and owned calling conventions.
- Primitive numeric/string/IO/task operations.

The compiler's later passes and generated C are shaped around this runtime.
For example, reference-counting operations in IR eventually become calls or
inline operations against this object model.

## Short Version

In this snapshot, the compiler path is visible as:

1. The kernel accepts declarations into the environment.
2. `LeanIR.lean` imports the module and initializes compiler extensions.
3. Postponed declarations are resumed through the Lean-side LCNF compiler.
4. LCNF/IR is saved into `.ir.sig` and `.ir` module data.
5. `emitC` generates C from LCNF.
6. `Leanc.lean` invokes the platform C compiler.
7. The generated code runs against the Lean runtime, or the IR interpreter can
   execute IR directly when native code is unavailable.

The main caveat is important: the detailed compiler optimization passes are
mostly Lean code imported by this snapshot, not C++ files inside the vendored
tree. The C++ side here is the trusted kernel, runtime, IR interpreter, LLVM
FFI, and support code that those passes target.
