"""Tiny parser for the Lean-like tutorial scripts.

This is intentionally not a full Lean parser. It parses the small declaration
forms used in the tutorial scripts and builds the corresponding Python ASTs.
Later phases still use named proof constructors for tactic-heavy blocks, but
the runner now reads `script.lean` directly instead of a parallel
`declarations.py` file.
"""

from __future__ import annotations

import re
from dataclasses import dataclass
from pathlib import Path
from types import ModuleType


@dataclass(frozen=True)
class ParsedDeclaration:
    name: str
    expr: object
    expected: object


class ParseError(Exception):
    pass


def parse_script(phase_name: str, phase_dir: Path, solution: ModuleType) -> list[ParsedDeclaration]:
    text = strip_block_comments((phase_dir / "script.lean").read_text())
    blocks = declaration_blocks(text)
    return [parse_declaration(phase_name, solution, block) for block in blocks]


def strip_block_comments(text: str) -> str:
    while "/-" in text:
        start = text.index("/-")
        end = text.index("-/", start) + 2
        text = text[:start] + text[end:]
    return text


def declaration_blocks(text: str) -> list[str]:
    blocks: list[list[str]] = []
    current: list[str] = []
    for raw_line in text.splitlines():
        line = raw_line.rstrip()
        stripped = line.strip()
        if not stripped or stripped.startswith("--"):
            continue
        if is_declaration_start(stripped):
            if current:
                blocks.append(current)
            current = [line]
        elif stripped.startswith("| ") and ":" in stripped and "=>" not in stripped and current and current[0].strip().startswith(("inductive ", "| ")):
            blocks.append(current)
            current = [line]
        elif current:
            current.append(line)
        elif stripped.startswith(("deriving ", "namespace ", "end ", "instance ", "add :=")):
            continue
        else:
            raise ParseError(f"cannot parse top-level line: {stripped}")
    if current:
        blocks.append(current)
    return ["\n".join(block) for block in blocks]


def is_declaration_start(stripped: str) -> bool:
    return stripped.startswith(("constant ", "inductive ", "def ", "theorem "))


def parse_declaration(phase_name: str, solution: ModuleType, block: str) -> ParsedDeclaration:
    first = block.strip().splitlines()[0].strip()
    if phase_name == "01_true_false":
        return parse_phase1(solution, block, first)
    if phase_name == "02_recursive_nat":
        return parse_phase2(solution, block, first)
    if phase_name == "03_rewrites":
        return parse_phase3(solution, block, first)
    if phase_name == "04_induction":
        return parse_phase4(solution, block, first)
    if phase_name == "05_comm":
        return parse_phase5(solution, block, first)
    raise ParseError(f"unknown phase {phase_name}")


def parse_phase1(solution: ModuleType, block: str, first: str) -> ParsedDeclaration:
    if match := re.fullmatch(r"constant\s+(\w+)\s*:\s*(.+)", first):
        name, ty_src = match.groups()
        expr = const_for_name(solution, name)
        return ParsedDeclaration(name, expr, parse_type(solution, ty_src))
    if match := re.fullmatch(r"theorem\s+(\w+)\s*:\s*(.+?)\s*:=\s*(.+)", first):
        name, ty_src, term_src = match.groups()
        return ParsedDeclaration(name, parse_expr(solution, term_src), parse_type(solution, ty_src))
    raise ParseError(f"unsupported phase 1 declaration: {first}")


def parse_phase2(solution: ModuleType, block: str, first: str) -> ParsedDeclaration:
    if first.startswith("inductive "):
        return ParsedDeclaration("MyNat", solution.MyNat, solution.Type)
    if first.startswith("| "):
        name, ty_src = parse_constructor_line(first)
        return ParsedDeclaration(name, const_for_name(solution, name), parse_type(solution, ty_src))
    if match := re.fullmatch(r"def\s+(\w+)\s*:\s*(.+?)\s*:=\s*(.+)", first):
        name, ty_src, term_src = match.groups()
        return ParsedDeclaration(name, parse_expr(solution, term_src), parse_type(solution, ty_src))
    if match := re.fullmatch(r"constant\s+(\w+)\s*:\s*(.+)", first):
        name, ty_src = match.groups()
        return ParsedDeclaration(name, const_for_name(solution, name), parse_type(solution, ty_src))
    if first.startswith("theorem "):
        name, ty_src, body_src = split_theorem(block)
        expected = parse_type(solution, ty_src)
        return ParsedDeclaration(name, parse_proof(solution, body_src, expected), expected)
    raise ParseError(f"unsupported phase 2 declaration: {first}")


def parse_phase3(solution: ModuleType, block: str, first: str) -> ParsedDeclaration:
    if match := re.fullmatch(r"def\s+(\w+)\s*:\s*(.+)", first):
        name, ty_src = match.groups()
        return ParsedDeclaration(name, const_for_name(solution, name), parse_type(solution, ty_src))
    if first.startswith("theorem "):
        name, ty_src, body_src = split_theorem(block)
        expected = parse_type(solution, ty_src)
        return ParsedDeclaration(name, parse_proof(solution, body_src, expected), expected)
    raise ParseError(f"unsupported phase 3 declaration: {first}")


def parse_phase4(solution: ModuleType, block: str, first: str) -> ParsedDeclaration:
    name, _, _ = split_theorem(block)
    if name != "succ_add":
        raise ParseError(f"unsupported phase 4 theorem: {name}")
    return ParsedDeclaration(name, solution.theorem_proof(), solution.theorem_type())


def parse_phase5(solution: ModuleType, block: str, first: str) -> ParsedDeclaration:
    if first.startswith("inductive "):
        return ParsedDeclaration("MyNat", *solution.mynat_case())
    if first.startswith("| "):
        name, _ = parse_constructor_line(first)
        if name == "zero":
            return ParsedDeclaration(name, *solution.zero_case())
        if name == "succ":
            return ParsedDeclaration(name, *solution.succ_case())
    if first.startswith("def add"):
        return ParsedDeclaration("add", *solution.add_case())
    if first.startswith(("deriving ", "namespace ", "instance ", "end ")):
        raise ParseError(f"unexpected non-declaration block: {first}")
    if first.startswith("theorem "):
        name = theorem_name(first)
        cases = {
            "my_add_zero": solution.my_add_zero_case,
            "my_add_succ": solution.my_add_succ_case,
            "succ_add_succ": solution.succ_add_succ_case,
            "succ_add": solution.succ_add_case,
            "zero_add": solution.zero_add_case,
            "add_comm": solution.add_comm_case,
            "add_assoc": solution.add_assoc_case,
            "add_right_comm": solution.add_right_comm_case,
        }
        if name in cases:
            return ParsedDeclaration(name, *cases[name]())
    raise ParseError(f"unsupported phase 5 declaration: {first}")


def parse_constructor_line(line: str) -> tuple[str, str]:
    match = re.fullmatch(r"\|\s+(\w+)\s*:\s*(.+)", line.strip())
    if match is None:
        raise ParseError(f"bad constructor line: {line}")
    return match.group(1), match.group(2)


def split_theorem(block: str) -> tuple[str, str, str]:
    compact = " ".join(line.strip() for line in block.splitlines())
    match = re.fullmatch(r"theorem\s+(\w+)\s*:\s*(.+?)\s*:=\s*(.+)", compact)
    if match is None:
        raise ParseError(f"bad theorem block: {block}")
    return match.group(1), match.group(2), match.group(3)


def theorem_name(first: str) -> str:
    match = re.match(r"theorem\s+(\w+)", first)
    if match is None:
        raise ParseError(f"bad theorem line: {first}")
    return match.group(1)


def const_for_name(solution: ModuleType, name: str):
    if name == "Eq" and hasattr(solution, "EqConst"):
        return solution.EqConst
    if hasattr(solution, name):
        return getattr(solution, name)
    return solution.p2.Const(name) if hasattr(solution, "p2") else solution.Const(name)


VARIABLE_NAMES = {"a", "b", "c", "n", "x", "y", "h", "ih"}


def parse_type(solution: ModuleType, src: str):
    src = strip_outer_parens(src.strip())
    if src == "Prop":
        return prop_sort(solution)
    if src == "Type":
        return type_sort(solution)
    if src == "True":
        return solution.TrueProp
    if src == "MyNat":
        return mynat(solution)
    if src.startswith("Eq "):
        parts = src.split()
        if len(parts) != 4:
            raise ParseError(f"unsupported Eq type: {src}")
        return eq_ctor(solution)(parse_type(solution, parts[1]), parse_expr(solution, parts[2]), parse_expr(solution, parts[3]))
    if src.startswith("forall "):
        return parse_forall(solution, src)
    if "->" in src:
        left, right = split_top_level_arrow(src)
        return arrow(solution)(parse_type(solution, left), parse_type(solution, right))
    if "=" in src:
        lhs, rhs = split_top_level_equals(src)
        return eq_ctor(solution)(mynat(solution), parse_expr(solution, lhs), parse_expr(solution, rhs))
    raise ParseError(f"unsupported type: {src}")


def parse_forall(solution: ModuleType, src: str):
    match = re.fullmatch(r"forall\s+(.+?)\s*:\s*MyNat,\s*(.+)", src)
    if match is None:
        raise ParseError(f"unsupported forall: {src}")
    names = match.group(1).split()
    body = parse_type(solution, match.group(2))
    for name in reversed(names):
        body = pi_ctor(solution)(name, mynat(solution), body)
    return body


def parse_proof(solution: ModuleType, src: str, expected):
    src = src.strip()
    if src == "true_intro":
        return solution.true_intro
    if src.startswith("fun "):
        return parse_fun(solution, src, expected)
    if src == "rfl":
        return refl_for(solution, expected)
    if src.startswith("rw "):
        return solution.Rw(parse_expr(solution, src.removeprefix("rw ")))
    return parse_expr(solution, src)


def parse_fun(solution: ModuleType, src: str, expected):
    head, body_src = src.split("=>", 1)
    names = head.removeprefix("fun").strip().split()
    expr = parse_proof_under_binders(solution, names, body_src.strip(), expected)
    return expr


def parse_proof_under_binders(solution: ModuleType, names: list[str], body_src: str, expected):
    if not names:
        return parse_proof(solution, body_src, expected)
    if not isinstance(expected, pi_ctor(solution)):
        raise ParseError(f"lambda has too many binders for {solution.pretty(expected)}")
    name = names[0]
    renamed_body = subst(solution)(expected.body, expected.var, var_ctor(solution)(name))
    body = parse_proof_under_binders(solution, names[1:], body_src, renamed_body)
    return lam_ctor(solution)(name, expected.domain, body)


def refl_for(solution: ModuleType, expected):
    if not isinstance(expected, eq_ctor(solution)):
        raise ParseError("rfl expected an equality goal")
    return refl_ctor(solution)(expected.ty, expected.rhs)


def parse_expr(solution: ModuleType, src: str):
    src = strip_outer_parens(src.strip())
    if has_top_level_operator(src, "+"):
        left, right = split_top_level_plus(src)
        add = getattr(solution, "add", None) or solution.p3.add
        return apps(solution)(add, parse_expr(solution, left), parse_expr(solution, right))
    if src.startswith("succ "):
        return apps(solution)(succ_const(solution), parse_expr(solution, src.removeprefix("succ ")))
    parts = src.split()
    if len(parts) > 1:
        head = parse_expr(solution, parts[0])
        return apps(solution)(head, *(parse_expr(solution, part) for part in parts[1:]))
    if hasattr(solution, src):
        return getattr(solution, src)
    if src == "Eq" and hasattr(solution, "EqConst"):
        return solution.EqConst
    if src in VARIABLE_NAMES:
        return var_ctor(solution)(src)
    const_cls = solution.p2.Const if hasattr(solution, "p2") else solution.Const
    return const_cls(src)


def arrow(solution: ModuleType):
    return solution.arrow if hasattr(solution, "arrow") else solution.p2.arrow


def apps(solution: ModuleType):
    return solution.apps if hasattr(solution, "apps") else solution.p2.apps


def subst(solution: ModuleType):
    if hasattr(solution, "p3"):
        return solution.p3.subst
    return solution.subst


def prop_sort(solution: ModuleType):
    return solution.Prop if hasattr(solution, "Prop") else solution.p2.Prop


def type_sort(solution: ModuleType):
    return solution.Type if hasattr(solution, "Type") else solution.p2.Type


def mynat(solution: ModuleType):
    return solution.MyNat if hasattr(solution, "MyNat") else solution.p2.MyNat


def succ_const(solution: ModuleType):
    return solution.succ if hasattr(solution, "succ") else solution.p2.succ


def var_ctor(solution: ModuleType):
    return solution.Var if hasattr(solution, "Var") else solution.p2.Var


def pi_ctor(solution: ModuleType):
    return solution.Pi if hasattr(solution, "Pi") else solution.p2.Pi


def lam_ctor(solution: ModuleType):
    return solution.Lam if hasattr(solution, "Lam") else solution.p3.Lam


def eq_ctor(solution: ModuleType):
    return solution.Eq if hasattr(solution, "Eq") else solution.p3.Eq


def refl_ctor(solution: ModuleType):
    return solution.Refl if hasattr(solution, "Refl") else solution.p3.Refl


def split_top_level_arrow(src: str) -> tuple[str, str]:
    return split_top_level_operator(src, "->")


def split_top_level_equals(src: str) -> tuple[str, str]:
    return split_top_level_operator(src, "=")


def split_top_level_plus(src: str) -> tuple[str, str]:
    return split_top_level_operator(src, "+")


def split_top_level_operator(src: str, op: str) -> tuple[str, str]:
    depth = 0
    for i, char in enumerate(src):
        if char == "(":
            depth += 1
        elif char == ")":
            depth -= 1
        elif depth == 0 and src.startswith(op, i):
            return src[:i].strip(), src[i + len(op) :].strip()
    raise ParseError(f"missing top-level {op!r} in {src!r}")


def has_top_level_operator(src: str, op: str) -> bool:
    depth = 0
    for i, char in enumerate(src):
        if char == "(":
            depth += 1
        elif char == ")":
            depth -= 1
        elif depth == 0 and src.startswith(op, i):
            return True
    return False


def strip_outer_parens(src: str) -> str:
    while src.startswith("(") and src.endswith(")") and encloses_all(src):
        src = src[1:-1].strip()
    return src


def encloses_all(src: str) -> bool:
    depth = 0
    for index, char in enumerate(src):
        if char == "(":
            depth += 1
        elif char == ")":
            depth -= 1
            if depth == 0 and index != len(src) - 1:
                return False
    return depth == 0
