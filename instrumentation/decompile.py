"""Decompile kernel traces back into readable Lean.

The instrumented kernel (see README.md) prints every declaration as a raw
expression tree. Those trees are fully explicit: every implicit argument,
every type class instance, and every universe level is spelled out. This
module reverses the *presentation* part of elaboration:

    HAdd.hAdd MyNat MyNat MyNat (instHAdd MyNat MyNat.instAdd) a zero
        -->   a + zero

It does not guess. Which arguments are hidden is decided from the binder
annotations of each constant's type, and those types are in the trace itself
(the `reference` blocks). The only built-in knowledge is the small `INFIX`
table below, which says how a handful of constants are written as operators.

Usage:

    python3 instrumentation/decompile.py TRACE              # readable Lean
    python3 instrumentation/decompile.py TRACE --explicit   # hide nothing
    python3 instrumentation/decompile.py TRACE --only NAME  # one declaration
    python3 instrumentation/decompile.py TRACE --stats      # size table
"""

from __future__ import annotations

import argparse
import re
import sys
from dataclasses import dataclass, field
from pathlib import Path


# --------------------------------------------------------------------------
# Expression tree. One class per kernel `Expr` constructor.
# --------------------------------------------------------------------------


@dataclass(frozen=True)
class Expr:
    pass


@dataclass(frozen=True)
class BVar(Expr):
    index: int


@dataclass(frozen=True)
class Sort(Expr):
    level: str


@dataclass(frozen=True)
class Const(Expr):
    name: str
    levels: tuple[str, ...] = ()


@dataclass(frozen=True)
class App(Expr):
    fn: Expr
    arg: Expr


@dataclass(frozen=True)
class Lam(Expr):
    name: str
    info: str
    domain: Expr
    body: Expr


@dataclass(frozen=True)
class Pi(Expr):
    name: str
    info: str
    domain: Expr
    body: Expr


@dataclass(frozen=True)
class Let(Expr):
    name: str
    type: Expr
    value: Expr
    body: Expr


@dataclass(frozen=True)
class Lit(Expr):
    kind: str
    value: str


@dataclass(frozen=True)
class MData(Expr):
    expr: Expr


@dataclass(frozen=True)
class Proj(Expr):
    struct: str
    index: int
    expr: Expr


@dataclass
class Declaration:
    kind: str  # theorem, definition, axiom, inductive, constructor, reference, ...
    name: str
    universe_params: list[str]
    type: Expr
    value: Expr | None = None


# --------------------------------------------------------------------------
# Parsing the trace format.
# --------------------------------------------------------------------------

HEADER = re.compile(r"^\[kernel-trace\] (?!end )(.+) (\S+)$")
BINDER = re.compile(r"^(Lam|Pi) (.*) \((\w+)\)$")
CONST = re.compile(r"^Const (.*?)(?: \[(.*)\])?$")


class TraceError(Exception):
    pass


def parse_trace(text: str) -> list[Declaration]:
    lines = text.splitlines()
    declarations: list[Declaration] = []
    i = 0
    while i < len(lines):
        match = HEADER.match(lines[i])
        if match is None:
            i += 1
            continue
        kind, name = match.group(1), match.group(2)
        i += 1
        universe_params: list[str] = []
        ty: Expr | None = None
        value: Expr | None = None
        while not lines[i].startswith("[kernel-trace] end "):
            line = lines[i]
            if line.startswith("  universe params:"):
                universe_params = line.split(":", 1)[1].split()
                i += 1
            elif line.startswith(("  params:", "  safety:")):
                i += 1
            elif line == "  type:":
                ty, i = parse_expr(lines, i + 1, 2)
            elif line == "  value:":
                value, i = parse_expr(lines, i + 1, 2)
            else:
                raise TraceError(f"unexpected line {i + 1}: {line!r}")
        i += 1
        if ty is None:
            raise TraceError(f"declaration {name} has no type")
        declarations.append(Declaration(kind, name, universe_params, ty, value))
    return declarations


def parse_expr(lines: list[str], i: int, depth: int) -> tuple[Expr, int]:
    """Parse the node at `lines[i]`, which must be indented by `depth`."""

    line = lines[i]
    indent = "  " * depth
    if not line.startswith(indent) or line[len(indent) :].startswith(" "):
        raise TraceError(f"bad indentation at line {i + 1}: {line!r}")
    text = line[len(indent) :]
    i += 1

    def child() -> Expr:
        nonlocal i
        expr, i = parse_expr(lines, i, depth + 1)
        return expr

    if text == "App":
        fn = child()
        return App(fn, child()), i
    if text == "MData":
        return MData(child()), i
    binder = BINDER.match(text)
    if binder is not None:
        domain = child()
        body = child()
        cls = Lam if binder.group(1) == "Lam" else Pi
        return cls(binder.group(2), binder.group(3), domain, body), i
    head, _, rest = text.partition(" ")
    if head == "BVar":
        return BVar(int(rest)), i
    if head == "Sort":
        return Sort(rest), i
    if head == "Const":
        const = CONST.match(text)
        levels = tuple(const.group(2).split(", ")) if const.group(2) else ()
        return Const(const.group(1), levels), i
    if head == "Let":
        ty = child()
        value = child()
        return Let(rest, ty, value, child()), i
    if head == "Lit":
        kind, _, value = rest.partition(" ")
        return Lit(kind, value), i
    if head == "Proj":
        struct, _, index = rest.rpartition(" ")
        return Proj(struct, int(index), child()), i
    raise TraceError(f"unknown node at line {i}: {text!r}")


# --------------------------------------------------------------------------
# Small helpers on trees.
# --------------------------------------------------------------------------


def size(expr: Expr) -> int:
    """Number of nodes in the tree."""

    match expr:
        case App(fn, arg):
            return 1 + size(fn) + size(arg)
        case Lam(_, _, domain, body) | Pi(_, _, domain, body):
            return 1 + size(domain) + size(body)
        case Let(_, ty, value, body):
            return 1 + size(ty) + size(value) + size(body)
        case MData(inner) | Proj(_, _, inner):
            return 1 + size(inner)
        case _:
            return 1


def uses_bvar(expr: Expr, index: int) -> bool:
    """Does `expr` mention the variable bound `index` binders above it?"""

    match expr:
        case BVar(i):
            return i == index
        case App(fn, arg):
            return uses_bvar(fn, index) or uses_bvar(arg, index)
        case Lam(_, _, domain, body) | Pi(_, _, domain, body):
            return uses_bvar(domain, index) or uses_bvar(body, index + 1)
        case Let(_, ty, value, body):
            return uses_bvar(ty, index) or uses_bvar(value, index) or uses_bvar(body, index + 1)
        case MData(inner) | Proj(_, _, inner):
            return uses_bvar(inner, index)
        case _:
            return False


def spine(expr: Expr) -> tuple[Expr, list[Expr]]:
    """Split `f a b c` into `(f, [a, b, c])`."""

    args: list[Expr] = []
    while isinstance(expr, App):
        args.append(expr.arg)
        expr = expr.fn
    args.reverse()
    return expr, args


def strip_mdata(expr: Expr) -> Expr:
    while isinstance(expr, MData):
        expr = expr.expr
    return expr


def binder_infos(ty: Expr) -> list[tuple[str, str]]:
    """The `(name, annotation)` of each leading `Pi` in a constant's type."""

    infos: list[tuple[str, str]] = []
    ty = strip_mdata(ty)
    while isinstance(ty, Pi):
        infos.append((ty.name, ty.info))
        ty = strip_mdata(ty.body)
    return infos


# --------------------------------------------------------------------------
# Printing.
# --------------------------------------------------------------------------

# The one table of built-in knowledge: constants that Lean writes as infix
# operators. `(symbol, precedence, left precedence, right precedence)`, with
# the numbers taken from Lean's own `infixl`/`infix` declarations.
INFIX: dict[str, tuple[str, int, int, int]] = {
    "HAdd.hAdd": ("+", 65, 65, 66),
    "HSub.hSub": ("-", 65, 65, 66),
    "HMul.hMul": ("*", 70, 70, 71),
    "Eq": ("=", 50, 51, 51),
    "Ne": ("≠", 50, 51, 51),
    "LE.le": ("≤", 50, 51, 51),
    "LT.lt": ("<", 50, 51, 51),
    "And": ("∧", 35, 36, 35),
    "Or": ("∨", 30, 31, 30),
    "Iff": ("↔", 20, 21, 21),
}

# Helpers Lean generates for every inductive type are `protected`: they must be
# written with their full name even inside the type's namespace.
PROTECTED = {
    "rec", "recOn", "casesOn", "brecOn", "binductionOn", "below", "ibelow",
    "noConfusion", "noConfusionType", "ctorIdx", "ctorElim", "ctorElimType",
}  # fmt: skip

APP_PREC = 1024  # an argument position: anything but an atom needs parentheses
ARROW_PREC = 25
HIDDEN = {"implicit", "strict_implicit", "inst_implicit"}
AUTO_INSERTED = {"implicit", "inst_implicit"}
IDENT = re.compile(r"^[^\W\d][\w'!?]*$")  # Lean identifiers may use Greek letters
WIDTH = 100  # break an application over several lines beyond this


def indent(text: str) -> str:
    return "\n".join("  " + line for line in text.splitlines())


def lean_level(level: str) -> str:
    """Rewrite the kernel's spelling of a universe level into Lean syntax.

    The kernel prints `succ (max 1 u)`; Lean source writes `(max 1 u)+1`.
    """

    tokens = re.findall(r"[()]|[^\s()]+", level)
    pos = 0

    def atom() -> tuple[str, bool]:
        nonlocal pos
        token = tokens[pos]
        pos += 1
        if token == "(":
            inner = term()
            pos += 1  # closing parenthesis
            return inner
        return token, True

    def term() -> tuple[str, bool]:
        nonlocal pos
        token = tokens[pos]
        if token == "succ":
            pos += 1
            text, atomic = atom()
            if text.isdigit():
                return str(int(text) + 1), True
            return (text if atomic else f"({text})") + "+1", False
        if token in ("max", "imax"):
            pos += 1
            parts = []
            while pos < len(tokens) and tokens[pos] != ")":  # `max a b c` is `max a (max b c)`
                text, atomic = atom()
                parts.append(text if atomic else f"({text})")
            return f"{token} {' '.join(parts)}", False
        return atom()

    return term()[0]


@dataclass
class Printer:
    """Turns expression trees into Lean source text."""

    signatures: dict[str, Expr]  # constant name -> its type
    local_names: set[str] = field(default_factory=set)  # constants defined in this trace
    namespace: str = ""
    explicit: bool = False  # show every argument and universe level
    binder_types: bool = False  # write `fun (a : T) =>` instead of `fun a =>`

    # ---- names ----

    def const_name(self, name: str) -> str:
        prefix = self.namespace + "."
        if self.namespace and name in self.local_names and name.startswith(prefix):
            if name.rpartition(".")[2] not in PROTECTED:
                return name[len(prefix) :]
        return name

    @staticmethod
    def fresh(name: str, ctx: list[str]) -> str:
        """A printable binder name that does not shadow anything in `ctx`."""

        base = name.split("._@")[0]
        if not IDENT.match(base):
            base = "x"
        candidate, n = base, 0
        while candidate in ctx:
            n += 1
            candidate = f"{base}_{n}"
        return candidate

    # ---- entry points ----

    def declaration(self, decl: Declaration, name: str | None = None) -> str:
        """Print one declaration as Lean source. `name` overrides its name."""

        keyword = {"mutual definition": "def", "definition": "def"}.get(decl.kind, decl.kind)
        if decl.kind.startswith("reference"):
            keyword, decl = "#check", Declaration(decl.kind, decl.name, [], decl.type)
        name = self.const_name(decl.name) if name is None else name
        if decl.universe_params:
            name += ".{" + ", ".join(decl.universe_params) + "}"
        head = f"{keyword} {name} : {self.expr(decl.type)}"
        if decl.value is None:
            return head
        return f"{head} :=\n{indent(self.expr(decl.value))}"

    def inductive(self, decl: Declaration, constructors: list[Declaration]) -> str:
        lines = [f"inductive {self.const_name(decl.name)} : {self.expr(decl.type)} where"]
        for ctor in constructors:
            lines.append(f"  | {ctor.name.rpartition('.')[2]} : {self.expr(ctor.type)}")
        return "\n".join(lines)

    def expr(self, expr: Expr, ctx: list[str] | None = None, prec: int = 0) -> str:
        """Print `expr`. `ctx` names the enclosing binders, innermost last.

        `prec` is how tightly the surrounding text binds; the result is
        parenthesized when it binds more loosely than that.
        """

        ctx = [] if ctx is None else ctx
        text, own = self.pp(expr, ctx)
        return f"({text})" if own < prec else text

    # ---- one case per constructor; returns (text, precedence of text) ----

    def pp(self, expr: Expr, ctx: list[str]) -> tuple[str, int]:
        match expr:
            case BVar(index):
                if index >= len(ctx):
                    return f"#{index}", APP_PREC
                return ctx[len(ctx) - 1 - index], APP_PREC
            case Sort(level):
                return self.pp_sort(level)
            case Const(_, _) | App(_, _):
                return self.pp_app(expr, ctx)
            case Lam(_, _, _, _):
                return self.pp_lam(expr, ctx)
            case Pi(_, _, _, _):
                return self.pp_pi(expr, ctx)
            case Let(name, ty, value, body):
                name = self.fresh(name, ctx)
                text = f"let {name} : {self.expr(ty, ctx)} := {self.expr(value, ctx)}; "
                return text + self.expr(body, ctx + [name]), 0
            case Lit("nat", value):
                return value, APP_PREC
            case Lit(_, value):
                return value, APP_PREC
            case MData(inner):
                return self.pp(inner, ctx)
            case Proj(_, index, inner):
                return f"{self.expr(inner, ctx, APP_PREC)}.{index + 1}", APP_PREC
        raise TraceError(f"cannot print {expr!r}")

    @staticmethod
    def layout(head: str, parts: list[str]) -> str:
        """`head part part ...` on one line, or one part per line if too long."""

        flat = " ".join([head] + parts)
        if len(flat) <= WIDTH and "\n" not in flat:
            return flat
        return "\n".join([head] + [indent(part) for part in parts])

    def pp_sort(self, level: str) -> tuple[str, int]:
        level = lean_level(level)
        if level == "0":
            return "Prop", APP_PREC
        if level == "1":
            return "Type", APP_PREC
        if level.isdigit():
            return f"Type {int(level) - 1}", APP_PREC - 1
        if level.endswith("+1") and IDENT.match(level[:-2]):
            return f"Type {level[:-2]}", APP_PREC - 1
        if IDENT.match(level):
            return f"Sort {level}", APP_PREC - 1
        return f"Sort ({level})", APP_PREC - 1

    def pp_lam(self, expr: Expr, ctx: list[str]) -> tuple[str, int]:
        ctx = list(ctx)
        binders: list[str] = []
        while isinstance(expr, Lam):
            name = self.fresh(expr.name, ctx)
            if self.binder_types or self.explicit:
                binders.append(self.binder(name, expr.info, self.expr(expr.domain, ctx)))
            else:
                binders.append(name)
            ctx.append(name)
            expr = expr.body
        return self.layout(f"fun {' '.join(binders)} =>", [self.expr(expr, ctx)]), 0

    def pp_pi(self, expr: Expr, ctx: list[str]) -> tuple[str, int]:
        # A `Pi` whose body ignores the bound variable is a plain arrow.
        if isinstance(expr, Pi) and expr.info == "default" and not uses_bvar(expr.body, 0):
            domain = self.expr(expr.domain, ctx, ARROW_PREC + 1)
            body = self.expr(expr.body, ctx + [self.fresh("x", ctx)])  # `→` extends as far right as possible
            return f"{domain} → {body}", ARROW_PREC

        ctx = list(ctx)
        groups: list[tuple[list[str], str, str]] = []  # (names, annotation, type text)
        while isinstance(expr, Pi) and (expr.info != "default" or uses_bvar(expr.body, 0)):
            domain = self.expr(expr.domain, ctx)
            name = self.fresh(expr.name, ctx)
            # `∀ (a b : T)`: merge neighbours with the same type. The type text
            # must not mention the previous binder, which `fresh` guarantees is
            # a distinct name, so comparing text is enough.
            if groups and groups[-1][1] == expr.info and groups[-1][2] == domain and expr.info != "inst_implicit":
                groups[-1][0].append(name)
            else:
                groups.append(([name], expr.info, domain))
            ctx.append(name)
            expr = expr.body
        binders = " ".join(self.binder(" ".join(names), info, domain) for names, info, domain in groups)
        return f"∀ {binders}, {self.expr(expr, ctx)}", 0

    @staticmethod
    def binder(names: str, info: str, domain: str) -> str:
        if info == "implicit":
            return f"{{{names} : {domain}}}"
        if info == "strict_implicit":
            return f"⦃{names} : {domain}⦄"
        if info == "inst_implicit":
            return f"[{names} : {domain}]"
        return f"({names} : {domain})"

    def pp_app(self, expr: Expr, ctx: list[str]) -> tuple[str, int]:
        head, args = spine(expr)
        head = strip_mdata(head)
        if not isinstance(head, Const):
            parts = [self.expr(arg, ctx, APP_PREC) for arg in args]
            return self.layout(self.expr(head, ctx, APP_PREC), parts), APP_PREC - 1

        name = self.const_name(head.name)
        infos = binder_infos(self.signatures[head.name]) if head.name in self.signatures else []

        # If we hid the implicit arguments, would Lean put back exactly the
        # ones that are there? Lean inserts implicit arguments up to the next
        # explicit one, so the answer is no when the application stops right
        # before an implicit binder. Then we must write `@f` and show them all.
        stops_before_implicit = len(args) < len(infos) and infos[len(args)][1] in AUTO_INSERTED
        hidden_any = any(info in HIDDEN for _, info in infos[: len(args)])

        if self.explicit or (stops_before_implicit and (hidden_any or not args)):
            if self.explicit and head.levels:
                name = f"{name}.{{{', '.join(lean_level(level) for level in head.levels)}}}"
            if any(info in HIDDEN for _, info in infos):
                name = "@" + name
            if not args:
                return name, APP_PREC
            return self.layout(name, [self.expr(arg, ctx, APP_PREC) for arg in args]), APP_PREC - 1

        positional: list[Expr] = []
        shown: list[str] = []
        named = False
        for i, arg in enumerate(args):
            binder_name, info = infos[i] if i < len(infos) else ("", "default")
            if info not in HIDDEN:
                positional.append(arg)
                shown.append(self.expr(arg, ctx, APP_PREC))
            elif isinstance(strip_mdata(arg), Lam) and IDENT.match(binder_name):
                # A hidden argument that is itself a function (such as the
                # `motive` of a recursor) cannot be recovered by unification,
                # so real Lean needs it written out. Use a named argument.
                shown.append(f"({binder_name} := {self.expr(arg, ctx)})")
                named = True

        if not named and len(positional) == 2 and head.name in INFIX:
            symbol, prec, left, right = INFIX[head.name]
            return f"{self.expr(positional[0], ctx, left)} {symbol} {self.expr(positional[1], ctx, right)}", prec
        if head.name == "OfNat.ofNat" and len(args) == 3 and isinstance(strip_mdata(args[1]), Lit):
            return strip_mdata(args[1]).value, APP_PREC
        if not shown:
            return name, APP_PREC
        return self.layout(name, shown), APP_PREC - 1


# --------------------------------------------------------------------------
# Command line.
# --------------------------------------------------------------------------


def namespace_of(name: str) -> str:
    """The top-level namespace a declaration lives in (`MyNat` for `MyNat.succ.inj`)."""

    head, dot, _ = name.partition(".")
    return head if dot else ""


def build_printer(declarations: list[Declaration], **options) -> Printer:
    signatures = {decl.name: decl.type for decl in declarations}
    local_names = {decl.name for decl in declarations if not decl.kind.startswith("reference")}
    return Printer(signatures, local_names, **options)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("trace", type=Path)
    parser.add_argument("--explicit", action="store_true", help="show every argument and universe level")
    parser.add_argument("--binder-types", action="store_true", help="write the type of every `fun` binder")
    parser.add_argument("--only", action="append", default=[], help="print only this declaration (repeatable)")
    parser.add_argument("--references", action="store_true", help="also print referenced library constants")
    parser.add_argument("--stats", action="store_true", help="print a size table instead of Lean text")
    args = parser.parse_args()

    declarations = parse_trace(args.trace.read_text())
    printer = build_printer(declarations, explicit=args.explicit, binder_types=args.binder_types)

    # A declaration can be sent to the kernel more than once (Lean first adds a
    # recursive function as a placeholder axiom); keep the last version.
    latest: dict[str, Declaration] = {}
    for decl in declarations:
        latest[decl.name] = decl

    rows: list[tuple[str, int, int]] = []
    for decl in latest.values():
        if args.only and decl.name not in args.only:
            continue
        if decl.kind.startswith("reference") and not args.references and not args.only:
            continue
        nodes = size(decl.type) + (size(decl.value) if decl.value is not None else 0)
        if decl.kind == "constructor" and not args.only:
            continue  # printed under its inductive type
        if decl.kind == "inductive":
            constructors = [
                other for other in latest.values() if other.kind == "constructor" and other.name.rpartition(".")[0] == decl.name
            ]
            printer.namespace = decl.name
            text = printer.inductive(decl, constructors)
            nodes += sum(size(ctor.type) for ctor in constructors)
        else:
            printer.namespace = namespace_of(decl.name)
            text = printer.declaration(decl)
        rows.append((decl.name, nodes, len(text)))
        if not args.stats:
            print(text)
            print()

    if args.stats:
        width = max(len(name) for name, _, _ in rows)
        print(f"{'declaration':<{width}}  {'tree nodes':>10}  {'decompiled chars':>16}")
        for name, nodes, chars in rows:
            print(f"{name:<{width}}  {nodes:>10}  {chars:>16}")


if __name__ == "__main__":
    try:
        main()
    except BrokenPipeError:
        sys.exit(0)
