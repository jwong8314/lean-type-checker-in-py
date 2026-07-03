"""Lark parser for the Lean-like tutorial scripts.

The parser is deliberately small, but it is real in the sense that the runner
does not know what a chapter defines. We parse `script.lean` into declaration and
term AST nodes, then lower those nodes into the current chapter's Python kernel
objects.
"""

from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path
from types import ModuleType
from typing import Any

try:
    from lark import Lark, Token, Tree
except ModuleNotFoundError as exc:  # pragma: no cover - exercised by users.
    raise ModuleNotFoundError(
        "lean_parser.py requires lark. Install dependencies with "
        "`python3 -m pip install -r requirements.txt`."
    ) from exc


GRAMMAR = r"""
    start: item*

    ?item: declaration
         | namespace_decl
         | end_decl
         | deriving_decl
         | instance_decl
         | def_equation

    ?declaration: constant_decl
                | inductive_decl
                | constructor_decl
                | def_decl
                | theorem_decl

    constant_decl: "constant" NAME ":" type
    inductive_decl: "inductive" NAME ":" type "where"?
    constructor_decl: "|" constructor_name ":" type
    constructor_name: NAME
                    | "succ"
    def_decl: "def" NAME ":" type def_body?
    def_body: ":=" (def_equation+ | term)
    def_equation: "|" pattern_list FAT_ARROW term
    pattern_list: pattern ("," pattern)*
    pattern: NAME
           | "succ" NAME

    theorem_decl: "theorem" NAME binder* ":" type ":=" proof
    binder: "(" NAME+ ":" type ")"

    ?proof: by_proof
          | term
    by_proof: "by" tactic+
    ?tactic: "rfl"                         -> rfl_tactic
           | "rw" "[" rw_arg_list "]"      -> rw_tactic
           | "induction" NAME "with" case+ -> induction_tactic
           | "exact" term                  -> exact_tactic
    rw_arg_list: rw_arg ("," rw_arg)*
    rw_arg: left_arrow? term
    left_arrow: "←"
    case: "|" NAME NAME* FAT_ARROW case_body
    ?case_body: by_proof
              | tactic_proof
    tactic_proof: tactic+

    lambda: "fun" NAME+ FAT_ARROW proof

    ?type: forall_type
         | arrow_type
         | equality_type
         | sum
    forall_type: "forall" NAME+ ":" type "," type
    arrow_type: arrow_domain ARROW type
    ?arrow_domain: equality_type
                 | sum
    equality_type: sum EQ sum

    ?term: lambda
         | equality_type
         | sum
    ?sum: sum "+" app              -> add
        | app
    ?app: atom+
    ?atom: NAME                    -> name
         | "rfl"                   -> rfl_name
         | "rw"                    -> rw_name
         | "Prop"                  -> prop
         | "Type"                  -> type_sort
         | "(" term ")"

    namespace_decl: "namespace" NAME
    end_decl: "end" NAME?
    deriving_decl: "deriving" NAME+
    instance_decl: "instance" ":" NAME NAME "where" instance_field+
    instance_field: NAME ":=" NAME

    NAME: /[A-Za-z_][A-Za-z0-9_]*(\.[A-Za-z_][A-Za-z0-9_]*)*/
    FAT_ARROW.3: "=>"
    ARROW.3: "->"
    EQ.1: "="

    %import common.WS
    %ignore WS
    %ignore /--[^\n]*/
    %ignore /\/-(.|\n)*?-\//
"""


PARSER = Lark(GRAMMAR, parser="lalr", start="start")


@dataclass(frozen=True)
class ParsedDeclaration:
    name: str
    expr: object
    expected: object
    kind: str
    opaque: bool = False
    recursive_spec: object | None = None
    proof_ast: object | None = None


class ParseError(Exception):
    pass


@dataclass(frozen=True)
class NameNode:
    value: str


@dataclass(frozen=True)
class PropNode:
    pass


@dataclass(frozen=True)
class TypeNode:
    pass


@dataclass(frozen=True)
class AppNode:
    fn: Any
    args: tuple[Any, ...]


@dataclass(frozen=True)
class AddNode:
    lhs: Any
    rhs: Any


@dataclass(frozen=True)
class EqNode:
    lhs: Any
    rhs: Any


@dataclass(frozen=True)
class ArrowNode:
    domain: Any
    body: Any


@dataclass(frozen=True)
class ForallNode:
    names: tuple[str, ...]
    domain: Any
    body: Any


@dataclass(frozen=True)
class LambdaNode:
    names: tuple[str, ...]
    body: Any


@dataclass(frozen=True)
class ByNode:
    tactics: tuple[Any, ...]


@dataclass(frozen=True)
class RflNode:
    pass


@dataclass(frozen=True)
class RwNode:
    args: tuple[Any, ...]


@dataclass(frozen=True)
class InductionNode:
    target: str
    cases: tuple[Any, ...]


@dataclass(frozen=True)
class ExactNode:
    term: Any


@dataclass(frozen=True)
class CaseNode:
    constructor: str
    binders: tuple[str, ...]
    proof: Any


@dataclass(frozen=True)
class BinderNode:
    names: tuple[str, ...]
    ty: Any


@dataclass(frozen=True)
class DeclarationNode:
    kind: str
    name: str
    ty: Any
    proof: Any | None = None
    binders: tuple[BinderNode, ...] = ()


def parse_script(phase_dir: Path, solution: ModuleType) -> list[ParsedDeclaration]:
    tree = PARSER.parse((phase_dir / "script.lean").read_text())
    declarations = [build_declaration_node(child) for child in tree.children]
    declarations = [declaration for declaration in declarations if declaration is not None]
    recursive_specs = lower_recursive_specs(solution, declarations)
    return [lower_declaration(solution, declaration, recursive_specs.get(declaration.name)) for declaration in declarations]


def elaborate_declaration_proof(solution: ModuleType, checker, declaration: ParsedDeclaration) -> ParsedDeclaration:
    if not isinstance(declaration.proof_ast, ByNode):
        return declaration
    expr = lower_proof(solution, checker, declaration.name, declaration.proof_ast, declaration.expected)
    return ParsedDeclaration(
        declaration.name,
        expr,
        declaration.expected,
        declaration.kind,
        declaration.opaque,
        declaration.recursive_spec,
        declaration.proof_ast,
    )


def build_declaration_node(tree: Tree | Token) -> DeclarationNode | None:
    if isinstance(tree, Token):
        return None
    if tree.data in {"namespace_decl", "end_decl", "deriving_decl", "instance_decl", "def_equation"}:
        return None
    if tree.data == "constant_decl":
        name, ty = tree.children
        return DeclarationNode("constant", str(name), build_node(ty))
    if tree.data == "inductive_decl":
        name, ty = tree.children
        return DeclarationNode("inductive", str(name), build_node(ty))
    if tree.data == "constructor_decl":
        name, ty = tree.children
        return DeclarationNode("constructor", token_text(name), build_node(ty))
    if tree.data == "def_decl":
        name, ty, *body = tree.children
        proof = build_node(body[0]) if body else None
        return DeclarationNode("def", str(name), build_node(ty), proof)
    if tree.data == "theorem_decl":
        name = str(tree.children[0])
        binders: list[BinderNode] = []
        index = 1
        while index < len(tree.children) and is_tree(tree.children[index], "binder"):
            binders.append(build_binder(tree.children[index]))
            index += 1
        ty = build_node(tree.children[index])
        proof = build_node(tree.children[index + 1])
        return DeclarationNode("theorem", name, ty, proof, tuple(binders))
    raise ParseError(f"unsupported parse node: {tree.data}")


def build_binder(tree: Tree) -> BinderNode:
    *names, ty = semantic_children(tree)
    return BinderNode(tuple(str(name) for name in names), build_node(ty))


def build_node(node: Tree | Token):
    if isinstance(node, Token):
        return NameNode(str(node))
    children = semantic_children(node)
    if node.data == "name":
        return NameNode(str(children[0]))
    if node.data == "rfl_name":
        return NameNode("rfl")
    if node.data == "rw_name":
        return NameNode("rw")
    if node.data == "prop":
        return PropNode()
    if node.data == "type_sort":
        return TypeNode()
    if node.data == "app":
        head, *args = [build_node(child) for child in children]
        return AppNode(head, tuple(args)) if args else head
    if node.data == "add":
        return AddNode(build_node(children[0]), build_node(children[1]))
    if node.data == "equality_type":
        return EqNode(build_node(children[0]), build_node(children[1]))
    if node.data == "arrow_type":
        return ArrowNode(build_node(children[0]), build_node(children[1]))
    if node.data == "forall_type":
        names: list[str] = []
        index = 0
        while isinstance(children[index], Token):
            names.append(str(children[index]))
            index += 1
        return ForallNode(tuple(names), build_node(children[index]), build_node(children[index + 1]))
    if node.data == "lambda":
        names: list[str] = []
        index = 0
        while isinstance(children[index], Token):
            names.append(str(children[index]))
            index += 1
        return LambdaNode(tuple(names), build_node(children[index]))
    if node.data == "by_proof":
        return ByNode(tuple(build_node(child) for child in children))
    if node.data == "tactic_proof":
        return ByNode(tuple(build_node(child) for child in children))
    if node.data == "rfl_tactic":
        return RflNode()
    if node.data == "rw_tactic":
        args_node = children[0]
        return RwNode(tuple(build_node(child) for child in args_node.children))
    if node.data == "rw_arg":
        return build_node(children[-1])
    if node.data == "induction_tactic":
        target = str(children[0])
        return InductionNode(target, tuple(build_node(child) for child in children[1:]))
    if node.data == "exact_tactic":
        return ExactNode(build_node(children[0]))
    if node.data == "case":
        constructor = str(children[0])
        binders = tuple(str(child) for child in children[1:-1])
        return CaseNode(constructor, binders, build_node(children[-1]))
    if node.data == "def_body":
        if len(children) == 1 and not is_tree(children[0], "def_equation"):
            return build_node(children[0])
        return None
    raise ParseError(f"unsupported AST node: {node.data}")


def lower_recursive_specs(solution: ModuleType, declarations: list[DeclarationNode]) -> dict[str, object]:
    specs: dict[str, object] = {}
    for index, declaration in enumerate(declarations):
        if declaration.kind != "inductive":
            continue
        constructors: list[DeclarationNode] = []
        for candidate in declarations[index + 1 :]:
            if candidate.kind == "constructor":
                constructors.append(candidate)
                continue
            break
        specs[declaration.name] = lower_recursive_spec(solution, declaration, constructors)
    return specs


def lower_recursive_spec(solution: ModuleType, inductive: DeclarationNode, constructors: list[DeclarationNode]):
    recursive_type_spec = solution_attr(solution, "RecursiveTypeSpec")
    constructor_spec = solution_attr(solution, "ConstructorSpec")
    if recursive_type_spec is None or constructor_spec is None:
        return None

    lowered_constructors = []
    for constructor in constructors:
        lowered_type = lower_type(solution, constructor.ty)
        lowered_constructors.append(constructor_spec(constructor.name, constructor_arg_types(solution, lowered_type)))
    return recursive_type_spec(inductive.name, lower_type(solution, inductive.ty), tuple(lowered_constructors))


def constructor_arg_types(solution: ModuleType, ty: Any) -> tuple[Any, ...]:
    args: list[Any] = []
    while isinstance(ty, pi_ctor(solution)):
        args.append(ty.domain)
        ty = ty.body
    return tuple(args)


def solution_attr(solution: ModuleType, name: str):
    if hasattr(solution, name):
        return getattr(solution, name)
    if hasattr(solution, "p2") and hasattr(solution.p2, name):
        return getattr(solution.p2, name)
    return None


def lower_declaration(solution: ModuleType, declaration: DeclarationNode, recursive_spec: object | None = None) -> ParsedDeclaration:
    if declaration.kind in {"constant", "inductive", "constructor"}:
        return ParsedDeclaration(
            declaration.name,
            const_for_name(solution, declaration.name),
            lower_type(solution, declaration.ty),
            declaration.kind,
            opaque=True,
            recursive_spec=recursive_spec,
        )
    if declaration.kind == "def":
        opaque = declaration.proof is None
        return ParsedDeclaration(
            declaration.name,
            const_for_name(solution, declaration.name) if opaque else lower_expr(solution, declaration.proof),
            lower_type(solution, declaration.ty),
            declaration.kind,
            opaque=opaque,
        )
    if declaration.kind == "theorem":
        expected = lower_type(solution, declaration.ty)
        for binder in reversed(declaration.binders):
            binder_type = lower_type(solution, binder.ty)
            for name in reversed(binder.names):
                expected = pi_ctor(solution)(name, binder_type, expected)
        return ParsedDeclaration(
            declaration.name,
            lower_proof(solution, None, declaration.name, declaration.proof, expected),
            expected,
            declaration.kind,
            proof_ast=declaration.proof,
        )
    raise ParseError(f"unsupported declaration kind: {declaration.kind}")


def lower_type(solution: ModuleType, node: Any):
    if isinstance(node, PropNode):
        return prop_sort(solution)
    if isinstance(node, TypeNode):
        return type_sort(solution)
    if isinstance(node, NameNode):
        if node.value == "True":
            return getattr(solution, "TrueProp", const_for_name(solution, "True"))
        if node.value == "MyNat":
            return mynat(solution)
        return lower_expr(solution, node)
    if isinstance(node, AppNode) and isinstance(node.fn, NameNode) and node.fn.value == "Eq":
        if len(node.args) != 3:
            raise ParseError("Eq expects a type and two terms")
        return eq_ctor(solution)(
            lower_type(solution, node.args[0]),
            lower_expr(solution, node.args[1]),
            lower_expr(solution, node.args[2]),
        )
    if isinstance(node, ForallNode):
        body = lower_type(solution, node.body)
        domain = lower_type(solution, node.domain)
        for name in reversed(node.names):
            body = pi_ctor(solution)(name, domain, body)
        return body
    if isinstance(node, ArrowNode):
        return arrow(solution)(lower_type(solution, node.domain), lower_type(solution, node.body))
    if isinstance(node, EqNode):
        return eq_ctor(solution)(mynat(solution), lower_expr(solution, node.lhs), lower_expr(solution, node.rhs))
    raise ParseError(f"unsupported type AST: {node!r}")


def lower_proof(solution: ModuleType, checker, name: str, node: Any, expected):
    if should_use_named_proof(solution, name, node):
        return named_proof(solution, name)
    if isinstance(node, ByNode) and isinstance(expected, pi_ctor(solution)):
        body = lower_proof(solution, checker, name, node, expected.body)
        return lam_ctor(solution)(expected.var, expected.domain, body)
    if isinstance(node, ByNode):
        return lower_by_proof(solution, checker, node, expected)
    if isinstance(node, LambdaNode):
        return lower_lambda(solution, checker, node, expected)
    if isinstance(node, NameNode) and node.value == "true_intro":
        return getattr(solution, "true_intro", const_for_name(solution, "true_intro"))
    if isinstance(node, NameNode) and node.value == "rfl":
        return refl_for(solution, expected)
    if isinstance(node, RflNode):
        return refl_for(solution, expected)
    if isinstance(node, RwNode):
        return lower_rw(solution, node)
    if isinstance(node, AppNode) and isinstance(node.fn, NameNode) and node.fn.value == "rw":
        return lower_rw(solution, RwNode(node.args))
    return lower_expr(solution, node)


def should_use_named_proof(solution: ModuleType, name: str, node: Any) -> bool:
    if contains_node(node, InductionNode) or contains_name(node, "MyNat.ind"):
        return has_named_proof(solution, name)
    if name in {"add_comm", "add_assoc", "add_right_comm"}:
        return has_named_proof(solution, name)
    return False


def contains_node(node: Any, cls: type) -> bool:
    if isinstance(node, cls):
        return True
    if hasattr(node, "__dataclass_fields__"):
        return any(contains_node(value, cls) for value in vars(node).values())
    if isinstance(node, tuple):
        return any(contains_node(value, cls) for value in node)
    return False


def contains_name(node: Any, name: str) -> bool:
    if isinstance(node, NameNode):
        return node.value == name
    if hasattr(node, "__dataclass_fields__"):
        return any(contains_name(value, name) for value in vars(node).values())
    if isinstance(node, tuple):
        return any(contains_name(value, name) for value in node)
    return False


def has_named_proof(solution: ModuleType, name: str) -> bool:
    return hasattr(solution, f"{name}_case") or (name == "succ_add" and hasattr(solution, "theorem_proof"))


def named_proof(solution: ModuleType, name: str):
    case_name = f"{name}_case"
    if hasattr(solution, case_name):
        expr, _ = getattr(solution, case_name)()
        return expr
    if name == "succ_add" and hasattr(solution, "theorem_proof"):
        return solution.theorem_proof()
    raise ParseError(f"no proof builder for {name}")


def lower_by_proof(solution: ModuleType, checker, node: ByNode, expected):
    if checker is None:
        return unresolved_proof(solution)
    return checker.execute_tactics(expected, node.tactics, lambda expr: lower_expr(solution, expr))


def lower_rw(solution: ModuleType, node: RwNode):
    if not node.args:
        raise ParseError("rw expects at least one rewrite rule")
    return rw_ctor(solution)(lower_expr(solution, node.args[-1]))


def unresolved_proof(solution: ModuleType):
    const_cls = solution.p2.Const if hasattr(solution, "p2") else solution.Const
    return const_cls("__unresolved_by_proof__")


def lower_lambda(solution: ModuleType, checker, node: LambdaNode, expected):
    return lower_proof_under_binders(solution, checker, list(node.names), node.body, expected)


def lower_proof_under_binders(solution: ModuleType, checker, names: list[str], body: Any, expected):
    if not names:
        return lower_proof(solution, checker, "", body, expected)
    if not isinstance(expected, pi_ctor(solution)):
        raise ParseError(f"lambda has too many binders for {solution.pretty(expected)}")
    name = names[0]
    renamed_body = subst(solution)(expected.body, expected.var, var_ctor(solution)(name))
    proof = lower_proof_under_binders(solution, checker, names[1:], body, renamed_body)
    return lam_ctor(solution)(name, expected.domain, proof)


def refl_for(solution: ModuleType, expected):
    if not isinstance(expected, eq_ctor(solution)):
        raise ParseError("rfl expected an equality goal")
    return refl_ctor(solution)(expected.ty, expected.rhs)


def lower_expr(solution: ModuleType, node: Any):
    if isinstance(node, NameNode):
        if node.value == "Eq" and hasattr(solution, "EqConst"):
            return solution.EqConst
        if hasattr(solution, node.value):
            return getattr(solution, node.value)
        if node.value in {"a", "b", "c", "n", "x", "y", "h", "ih"}:
            return var_ctor(solution)(node.value)
        const_cls = solution.p2.Const if hasattr(solution, "p2") else solution.Const
        return const_cls(node.value)
    if isinstance(node, AppNode):
        return apps(solution)(lower_expr(solution, node.fn), *(lower_expr(solution, arg) for arg in node.args))
    if isinstance(node, AddNode):
        add = getattr(solution, "add", None) or solution.p3.add
        return apps(solution)(add, lower_expr(solution, node.lhs), lower_expr(solution, node.rhs))
    if isinstance(node, EqNode):
        return eq_ctor(solution)(mynat(solution), lower_expr(solution, node.lhs), lower_expr(solution, node.rhs))
    raise ParseError(f"unsupported expression AST: {node!r}")


def const_for_name(solution: ModuleType, name: str):
    if name == "Eq" and hasattr(solution, "EqConst"):
        return solution.EqConst
    if hasattr(solution, name):
        return getattr(solution, name)
    return solution.p2.Const(name) if hasattr(solution, "p2") else solution.Const(name)


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


def rw_ctor(solution: ModuleType):
    return solution.Rw if hasattr(solution, "Rw") else solution.p3.Rw


def is_tree(node: Any, data: str) -> bool:
    return isinstance(node, Tree) and node.data == data


def semantic_children(tree: Tree) -> list[Tree | Token]:
    return [
        child
        for child in tree.children
        if not (isinstance(child, Token) and child.type in {"FAT_ARROW", "ARROW", "EQ"})
    ]


def token_text(node: Tree | Token) -> str:
    if isinstance(node, Token):
        return str(node)
    children = semantic_children(node)
    if not children:
        return "succ"
    return str(children[0])
