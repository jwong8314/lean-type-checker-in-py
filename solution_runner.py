"""Build phase checkers and register script declarations.

The phase `solution.py` files define the kernel pieces for that phase.  This
runner module owns the tutorial-time environment setup: which constants are
available before a declaration is checked, and which declarations get added
afterwards.
"""

from __future__ import annotations

from types import ModuleType

from expressions import Prop


def setting_default_types(phase_name: str, solution: ModuleType):
    if phase_name == "01_true_false":
        return phase1_checker(solution)
    if phase_name == "02_recursive_nat":
        return phase2_checker(solution)
    if phase_name == "03_rewrites":
        return phase3_checker(solution)
    if phase_name == "04_induction":
        return phase4_checker(solution)
    if phase_name == "05_comm":
        return phase5_checker(solution)
    raise ValueError(f"unknown phase {phase_name}")


def phase1_checker(solution: ModuleType):
    tc = solution.TypeChecker()
    default_types = {
        "True": Prop,
        "False": Prop,
        "true_intro": solution.TrueProp,
    }
    for name, ty in default_types.items():
        tc.add(name, ty)
    return tc


def phase2_checker(solution: ModuleType):
    tc = solution.TypeChecker()
    tc.add_recursive_type(solution.mynat_type_spec())
    return tc


def phase3_checker(solution: ModuleType):
    tc = solution.TypeChecker()
    tc.add_recursive_type(solution.p2.mynat_type_spec())
    return tc


def phase4_checker(solution: ModuleType):
    tc = solution.TypeChecker()
    tc.add_recursive_type(solution.p2.mynat_type_spec())
    tc.add("add", solution.p2.arrow(solution.p2.MyNat, solution.p2.arrow(solution.p2.MyNat, solution.p2.MyNat)))
    tc.add_reducer("add", solution.p3.nat_add_reducer)
    return tc


def phase5_checker(solution: ModuleType):
    return solution.TypeChecker()


def register_before_check(phase_name: str) -> set[str]:
    if phase_name == "02_recursive_nat":
        return {"Eq"}
    if phase_name == "03_rewrites":
        return {"add", "add_zero", "add_succ", "rw"}
    if phase_name == "05_comm":
        return {"MyNat", "add"}
    return set()


def register_declaration(phase_name: str, solution: ModuleType, tc, name: str) -> None:
    if phase_name == "01_true_false":
        return
    if phase_name == "02_recursive_nat":
        register_phase2(solution, tc, name)
    if phase_name == "03_rewrites":
        register_phase3(solution, tc, name)
    elif phase_name == "04_induction":
        if name == "succ_add":
            tc.add("succ_add", solution.theorem_type())
    elif phase_name == "05_comm":
        register_phase5(solution, tc, name)


def register_phase2(solution: ModuleType, tc, name: str) -> None:
    if name in {"one", "two"}:
        tc.add(name, solution.MyNat)
    elif name == "Eq":
        tc.add(
            "Eq",
            solution.arrow(
                solution.Type,
                solution.arrow(solution.MyNat, solution.arrow(solution.MyNat, solution.Prop)),
            ),
        )
    elif name == "rfl_nat":
        x = solution.Var("x")
        tc.add("rfl_nat", solution.Pi("x", solution.MyNat, solution.Eq(solution.MyNat, x, x)))


def register_phase3(solution: ModuleType, tc, name: str) -> None:
    if name == "add":
        tc.add("add", solution.add_decl_case()[1])
    elif name == "add_zero":
        tc.add("add_zero", solution.add_zero_type())
        tc.add_reducer("add", solution.nat_add_reducer)
    elif name == "add_succ":
        tc.add("add_succ", solution.add_succ_type())
        tc.add_reducer("add", solution.nat_add_reducer)
    elif name == "rw":
        tc.add("rw", solution.rw_type())
    elif name == "add_zero_by_rfl":
        tc.add(name, solution.add_zero_by_rfl_case()[1])
    elif name == "add_succ_by_rfl":
        tc.add(name, solution.add_succ_by_rfl_case()[1])
    elif name == "rewrite_step":
        tc.add(name, solution.rewrite_step_case()[1])


def register_phase5(solution: ModuleType, tc, name: str) -> None:
    if name == "MyNat":
        tc.add_recursive_type(solution.mynat_type_spec())
    elif name == "add":
        tc.add("add", solution.add_type())
        tc.add_reducer("add", solution.p3.nat_add_reducer)
    elif name == "my_add_zero":
        tc.add("my_add_zero", solution.my_add_zero_type())
    elif name == "my_add_succ":
        tc.add("my_add_succ", solution.my_add_succ_type())
    elif name == "succ_add":
        tc.add("succ_add", solution.succ_add_type())
    elif name == "succ_add_succ":
        tc.add("succ_add_succ", solution.succ_add_succ_type())
    elif name == "zero_add":
        tc.add("zero_add", solution.zero_add_type())
    elif name == "add_comm":
        tc.add("add_comm", solution.add_comm_type())
    elif name == "add_assoc":
        tc.add("add_assoc", solution.add_assoc_type())
    elif name == "add_right_comm":
        tc.add("add_right_comm", solution.add_right_comm_type())
