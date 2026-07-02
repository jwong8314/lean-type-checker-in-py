"""Run the tutorial `.lean` files through the Python kernel.

The files in `phases/` are intentionally Lean-shaped, but this project does not
yet implement a Lean parser.  Instead, each file contains `#kernel` directives.
This runner recognizes those tutorial directives and dispatches them to the
under-development Python kernel.
"""

from __future__ import annotations

from pathlib import Path
from typing import Callable

from lean_type_checker.core import (
    CongSucc,
    Eq,
    FalseProp,
    Lam,
    Nat,
    Pi,
    Prop,
    Refl,
    TrueProp,
    Type,
    Var,
    add,
    apps,
    arrow,
    base_checker,
    phase1_checker,
    phase2_checker,
    phase3_checker,
    pretty,
    rfl_only_proof,
    succ,
    theorem_proof,
    theorem_type,
    true_intro,
    zero,
)


ROOT = Path(__file__).resolve().parents[1]
PHASE_FILES = (
    ROOT / "phases/01_true_false/1_true_false.lean",
    ROOT / "phases/02_recursive_nat/2_recursive_nat.lean",
    ROOT / "phases/03_rewrites/3_rewrites.lean",
    ROOT / "phases/04_induction/4_induction.lean",
)


class KernelDirectiveError(Exception):
    pass


def rejected(action: Callable[[], object]) -> bool:
    try:
        action()
    except Exception:
        return True
    return False


def check_rewrite_step() -> None:
    tc = phase3_checker()
    a = Var("a")
    n = Var("n")
    ih = Var("ih")
    premise = Eq(Nat, apps(add, apps(succ, a), n), apps(succ, apps(add, a, n)))
    goal = Eq(
        Nat,
        apps(add, apps(succ, a), apps(succ, n)),
        apps(succ, apps(succ, apps(add, a, n))),
    )
    proof = Lam("a", Nat, Lam("n", Nat, Lam("ih", premise, CongSucc(ih))))
    expected = Pi("a", Nat, Pi("n", Nat, arrow(premise, goal)))
    tc.check(proof, expected)


def check_add_zero() -> None:
    tc = phase3_checker()
    a = Var("a")
    proof = Lam("a", Nat, Refl(Nat, a))
    expected = Pi("a", Nat, Eq(Nat, apps(add, a, zero), a))
    tc.check(proof, expected)


def check_add_succ() -> None:
    tc = phase3_checker()
    a = Var("a")
    n = Var("n")
    proof = Lam("a", Nat, Lam("n", Nat, Refl(Nat, apps(succ, apps(add, a, n)))))
    expected = Pi("a", Nat, Pi("n", Nat, Eq(Nat, apps(add, a, apps(succ, n)), apps(succ, apps(add, a, n)))))
    tc.check(proof, expected)


def directive_table() -> dict[str, Callable[[], str]]:
    return {
        "phase 1": lambda: "using phase 1 kernel",
        "check True : Prop": check_phase1_true,
        "check False : Prop": check_phase1_false,
        "check true_intro : True": check_phase1_true_intro,
        "reject true_intro : False": reject_phase1_false_intro,
        "phase 2": lambda: "using phase 2 kernel",
        "inductive Nat : Type where": lambda: "registered recursive type Nat",
        "| zero : Nat": lambda: "registered constructor zero",
        "| succ : Nat -> Nat": lambda: "registered constructor succ",
        "check Nat : Type": check_phase2_nat,
        "check zero : Nat": check_phase2_zero,
        "check succ : Nat -> Nat": check_phase2_succ,
        "check succ zero : Nat": check_phase2_one,
        "check succ (succ zero) : Nat": check_phase2_two,
        "phase 3": lambda: "using phase 3 kernel",
        "check add_zero : forall a : Nat, a + zero = a": check_phase3_add_zero,
        "check add_succ : forall a n : Nat, a + succ n = succ (a + n)": check_phase3_add_succ,
        "check rewrite_step : forall a n : Nat, (succ a + n = succ (a + n)) -> succ a + succ n = succ (succ (a + n))": check_phase3_rewrite_step,
        "phase 4": lambda: "using phase 4 kernel",
        "reject by_rfl : forall a b : Nat, succ a + b = succ (a + b)": reject_phase4_rfl,
        "check succ_add : forall a b : Nat, succ a + b = succ (a + b)": check_phase4_succ_add,
    }


def check_phase1_true() -> str:
    tc = phase1_checker()
    tc.check(TrueProp, Prop)
    return "True : Prop"


def check_phase1_false() -> str:
    tc = phase1_checker()
    tc.check(FalseProp, Prop)
    return "False : Prop"


def check_phase1_true_intro() -> str:
    tc = phase1_checker()
    tc.check(true_intro, TrueProp)
    return "true_intro : True"


def reject_phase1_false_intro() -> str:
    tc = phase1_checker()
    if not rejected(lambda: tc.check(true_intro, FalseProp)):
        raise KernelDirectiveError("true_intro unexpectedly checked as False")
    return "rejected true_intro : False"


def check_phase2_nat() -> str:
    tc = phase2_checker()
    tc.check(Nat, Type)
    return "Nat : Type"


def check_phase2_zero() -> str:
    tc = phase2_checker()
    tc.check(zero, Nat)
    return "zero : Nat"


def check_phase2_succ() -> str:
    tc = phase2_checker()
    tc.check(succ, arrow(Nat, Nat))
    return "succ : Nat -> Nat"


def check_phase2_one() -> str:
    tc = phase2_checker()
    one = apps(succ, zero)
    tc.check(one, Nat)
    return "succ zero : Nat"


def check_phase2_two() -> str:
    tc = phase2_checker()
    two = apps(succ, apps(succ, zero))
    tc.check(two, Nat)
    return "succ (succ zero) : Nat"


def check_phase3_add_zero() -> str:
    check_add_zero()
    return "add_zero checked by rfl"


def check_phase3_add_succ() -> str:
    check_add_succ()
    return "add_succ checked by rfl"


def check_phase3_rewrite_step() -> str:
    check_rewrite_step()
    return "rewrite_step checked by congr_succ"


def reject_phase4_rfl() -> str:
    tc = base_checker()
    if not rejected(lambda: tc.check(rfl_only_proof(), theorem_type())):
        raise KernelDirectiveError("bare rfl unexpectedly proved succ_add")
    return "rejected by_rfl"


def check_phase4_succ_add() -> str:
    tc = base_checker()
    inferred = tc.check(theorem_proof(), theorem_type())
    return f"succ_add : {pretty(inferred)}"


def run_file(path: Path) -> list[str]:
    table = directive_table()
    output: list[str] = []
    for lineno, line in enumerate(path.read_text().splitlines(), start=1):
        stripped = line.strip()
        if not stripped.startswith("#kernel "):
            continue
        directive = stripped.removeprefix("#kernel ").strip()
        action = table.get(directive)
        if action is None:
            raise KernelDirectiveError(f"{path}:{lineno}: unknown directive: {directive}")
        output.append(action())
    return output


def run_all(paths: tuple[Path, ...] = PHASE_FILES) -> None:
    for path in paths:
        print(path.relative_to(ROOT))
        for line in run_file(path):
            print(" ", line)
        print()


if __name__ == "__main__":
    run_all()
