"""Replay a kernel trace through this kernel. (Given.)

    python3 -m kernel.check chapters/04_equality/examples.trace

Each declaration in the trace is handled the way Lean's kernel handled it:

- `reference` blocks were checked by Lean when their own file was compiled.
  They are added without checking, like loading a compiled `.olean` file.
  The one exception is recursors: this kernel generates its own, and the
  imported recursor type is compared against it.
- Everything else is type checked from scratch.
"""

from __future__ import annotations

import argparse
import sys
from dataclasses import dataclass
from pathlib import Path

from .environment import ConstantInfo, Environment, KernelError
from .expr import erase_binder_names
from .inductive import add_inductive
from .trace import Declaration, load_trace
from .typechecker import add_axiom, add_definition


@dataclass
class Result:
    name: str
    kind: str
    status: str  # checked, imported, skipped, FAILED
    detail: str = ""


def check_trace(path: str | Path, env: Environment | None = None, only: set[str] | None = None) -> list[Result]:
    """Replay every declaration in the trace. Never raises: failures are in the results.

    `only`, if given, is the set of names to check; every other declaration
    is added without checking. Early chapters use this to skip declarations
    that need features they have not built yet.
    """

    env = Environment() if env is None else env
    declarations = load_trace(path)
    results: list[Result] = []

    # Lean's elaborator sometimes sends a declaration as a placeholder `axiom`
    # first and the real thing later. Only the last one counts.
    last_index = {decl.name: i for i, decl in enumerate(declarations)}

    # Imported declarations arrive in the order Lean discovered them, which is
    # not dependency order. Hold them back and add them, retrying, right
    # before the next declaration that is actually checked.
    pending: list[list[Declaration]] = []

    def flush_imports() -> None:
        while pending:
            failed: list[tuple[list[Declaration], str]] = []
            for group in pending:
                try:
                    results.append(add_declaration(env, group[0], group[1:], trusted=True))
                except KernelError as error:
                    failed.append((group, str(error)))
            if len(failed) == len(pending):  # no progress
                results.extend(Result(g[0].name, g[0].kind, "FAILED", message) for g, message in failed)
                pending.clear()
                return
            pending[:] = [group for group, _ in failed]

    i = 0
    while i < len(declarations):
        decl = declarations[i]
        i += 1
        group = [decl]
        if decl.kind == "inductive":
            while i < len(declarations) and declarations[i].kind == "constructor":
                group.append(declarations[i])
                i += 1
        if decl.imported:
            if decl.name not in env.constants or decl.kind == "recursor":
                pending.append(group)
            continue
        flush_imports()
        if last_index[decl.name] != i - len(group) and decl.kind == "axiom":
            results.append(Result(decl.name, decl.kind, "skipped", "placeholder, replaced later"))
            continue
        if decl.name in env.constants and decl.kind != "recursor":
            results.append(Result(decl.name, decl.kind, "skipped", "already declared"))
            continue
        trusted = decl.imported or (only is not None and decl.name not in only)
        try:
            results.append(add_declaration(env, decl, group[1:], trusted))
        except KernelError as error:
            results.append(Result(decl.name, decl.kind, "FAILED", str(error)))
        except RecursionError:
            results.append(Result(decl.name, decl.kind, "FAILED", "recursion limit exceeded"))
        except NotImplementedError as error:
            results.append(Result(decl.name, decl.kind, "FAILED", f"not implemented yet: {error}"))
    flush_imports()
    return results


def add_declaration(env: Environment, decl: Declaration, constructors: list[Declaration], trusted: bool) -> Result:
    status = "imported" if trusted else "checked"
    match decl.kind:
        case "inductive":
            before = set(env.constants)
            try:
                add_inductive(env, decl, constructors, check=not trusted)
            except (KernelError, NotImplementedError) as error:
                for name in set(env.constants) - before:  # undo the partial work
                    del env.constants[name]
                if not trusted or str(error).startswith("unknown constant"):
                    raise
                # An imported type this kernel cannot build a recursor for
                # (nested or mutual). Record the type and its constructors;
                # Lean's own recursor will be imported as an opaque constant.
                info = ConstantInfo(decl.name, "inductive", decl.universe_params, decl.type)
                info.num_params = decl.num_params or 0
                info.constructors = tuple(c.name for c in constructors)
                env.add(info)
                for index, ctor in enumerate(constructors):
                    env.add(
                        ConstantInfo(
                            ctor.name, "constructor", ctor.universe_params, ctor.type,
                            inductive=decl.name, constructor_index=index, num_params=info.num_params,
                        )
                    )  # fmt: skip
                return Result(decl.name, decl.kind, "imported", f"no recursor generated: {error}")
        case "recursor":
            # Never trusted: compare Lean's recursor with the one we generated.
            ours = env.find(decl.name)
            if ours is None and env.find(decl.name.removesuffix(".rec")) is None:
                raise KernelError(f"unknown constant: {decl.name.removesuffix('.rec')}")  # wait for the inductive type
            if ours is None:
                env.add(ConstantInfo(decl.name, "recursor", decl.universe_params, decl.type))
                return Result(decl.name, decl.kind, "imported", "no generated recursor to compare with")
            if erase_binder_names(ours.type) != erase_binder_names(decl.type):
                raise KernelError("generated recursor type differs from Lean's")
            return Result(decl.name, decl.kind, "checked", "generated recursor matches Lean's")
        case "definition" | "theorem" if decl.safety is not None:
            # `unsafe` and `partial` definitions may call themselves; Lean
            # checks them with a separate, weaker procedure. They cannot be
            # used in proofs, so we only record their type.
            env.add(ConstantInfo(decl.name, "opaque", decl.universe_params, decl.type))
            return Result(decl.name, decl.kind, "skipped", decl.safety)
        case "definition" | "theorem":
            if trusted:
                env.add(ConstantInfo(decl.name, decl.kind, decl.universe_params, decl.type, decl.value))
            else:
                add_definition(env, decl.name, decl.universe_params, decl.type, decl.value, decl.kind)
        case "opaque" if not trusted:
            add_definition(env, decl.name, decl.universe_params, decl.type, decl.value, "opaque")
        case _ if trusted:
            env.add(ConstantInfo(decl.name, decl.kind, decl.universe_params, decl.type))
        case "axiom":
            add_axiom(env, decl.name, decl.universe_params, decl.type)
        case _:
            raise KernelError(f"unsupported declaration kind: {decl.kind}")
    return Result(decl.name, decl.kind, status)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("trace", type=Path)
    parser.add_argument("--quiet", action="store_true", help="print only failures and the summary")
    args = parser.parse_args()

    sys.setrecursionlimit(100_000)
    results = check_trace(args.trace)
    for result in results:
        if args.quiet and result.status != "FAILED":
            continue
        detail = f"  ({result.detail.splitlines()[0]})" if result.detail else ""
        print(f"{result.status:<8} {result.kind:<11} {result.name}{detail}")
    counts = {status: sum(r.status == status for r in results) for status in ("checked", "imported", "skipped", "FAILED")}
    print(", ".join(f"{count} {status}" for status, count in counts.items()))
    sys.exit(1 if counts["FAILED"] else 0)


if __name__ == "__main__":
    main()
