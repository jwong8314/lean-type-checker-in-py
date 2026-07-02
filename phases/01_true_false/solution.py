"""Phase 1 solution: propositions as types."""

from __future__ import annotations

from dataclasses import dataclass


@dataclass(frozen=True)
class Expr:
    pass


@dataclass(frozen=True)
class Sort(Expr):
    level: int


@dataclass(frozen=True)
class Const(Expr):
    name: str


class TypeError(Exception):
    pass


class TypeChecker:
    def __init__(self) -> None:
        self.env: dict[str, Expr] = {}

    def add(self, name: str, ty: Expr) -> None:
        self.env[name] = ty

    def infer(self, expr: Expr) -> Expr:
        match expr:
            case Sort(level):
                return Sort(level + 1)
            case Const(name):
                if name not in self.env:
                    raise TypeError(f"unknown constant {name}")
                return self.env[name]
            case _:
                raise TypeError(f"cannot infer {expr!r}")

    def check(self, expr: Expr, expected: Expr) -> None:
        actual = self.infer(expr)
        if actual != expected:
            raise TypeError(f"expected {pretty(expected)}, got {pretty(actual)}")


Prop = Sort(0)
Type = Sort(1)
TrueProp = Const("True")
FalseProp = Const("False")
true_intro = Const("true_intro")


def phase1_checker() -> TypeChecker:
    tc = TypeChecker()
    tc.add("True", Prop)
    tc.add("False", Prop)
    tc.add("true_intro", TrueProp)
    return tc


def pretty(expr: Expr) -> str:
    match expr:
        case Sort(0):
            return "Prop"
        case Sort(1):
            return "Type"
        case Sort(level):
            return f"Type {level - 1}"
        case Const(name):
            return name
        case _:
            return repr(expr)


def rejected(action) -> bool:
    try:
        action()
    except TypeError:
        return True
    return False


def main() -> None:
    tc = phase1_checker()
    tc.check(TrueProp, Prop)
    tc.check(FalseProp, Prop)
    tc.check(true_intro, TrueProp)
    assert rejected(lambda: tc.check(true_intro, FalseProp))

    print("True : Prop")
    print("False : Prop")
    print("true_intro : True")
    print("true_intro : False rejected")


if __name__ == "__main__":
    main()
