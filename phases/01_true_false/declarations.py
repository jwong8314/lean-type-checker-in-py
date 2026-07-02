"""AST bridge for phase 1 script declarations."""

from __future__ import annotations

import solution


def declaration(name: str):
    if name == "True":
        return solution.TrueProp, solution.Prop
    if name == "False":
        return solution.FalseProp, solution.Prop
    if name == "true_intro":
        return solution.true_intro, solution.TrueProp
    if name == "true_is_true":
        return solution.true_intro, solution.TrueProp
    raise KeyError(name)
