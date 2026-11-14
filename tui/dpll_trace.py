"""DPLL trace engine — textbook DPLL with recorded steps.

Produces a list of Step objects so a visualizer can walk forward and
backward through the algorithm. Chronological backtracking only, no
clause learning. Features:
  - unit propagation
  - pure literal elimination
  - branching (first unassigned variable, ascending)
  - chronological backtracking (flip the last branch)
"""
from __future__ import annotations

from dataclasses import dataclass, field


@dataclass
class DStep:
    """One visualization step."""
    kind: str            # init|unit|pure|branch|conflict|backtrack|sat|unsat
    desc: str            # human-readable explanation
    assign: dict         # var(1-based) -> True/False
    frame_clauses: list  # CNF clauses snapshot (list of lists of ints)
    highlight: list = field(default_factory=list)  # clause indices to highlight
    focus_var: int = 0   # variable in focus (0 = none)
    depth: int = 0


class DPLLTracer:
    def __init__(self, clauses, num_vars):
        self.steps: list[DStep] = []
        self.clauses = [list(c) for c in clauses]
        self.num_vars = num_vars

    def record(self, kind, desc, assign, frame_clauses, highlight=(),
               focus_var=0, depth=0):
        self.steps.append(DStep(kind, desc, dict(assign),
                                [list(c) for c in frame_clauses],
                                list(highlight), focus_var, depth))

    def run(self) -> list[DStep]:
        self._solve({}, 0, [list(c) for c in self.clauses])
        return self.steps

    def _solve(self, assign, depth, clauses):
        # ---- unit propagation ----
        while True:
            unit = None
            for i, c in enumerate(clauses):
                if len(c) == 0:
                    self.record("conflict", "Empty clause — conflict!",
                                assign, clauses, highlight=[i], depth=depth)
                    return False
                if len(c) == 1:
                    unit = (i, c[0])
                    break
            if unit is None:
                break
            ci, lit = unit
            v = abs(lit)
            self.record("unit", f"Unit clause {fmt_cl(clauses[ci])}: "
                                f"x{v} = {lit > 0}",
                        assign, clauses, highlight=[ci], focus_var=v,
                        depth=depth)
            assign[v] = lit > 0
            new_clauses = simplify(clauses, lit)
            self.record("unit", f"Assign x{v}={lit > 0}; simplify",
                        assign, new_clauses, focus_var=v, depth=depth)
            clauses = new_clauses

        # ---- pure literal elimination ----
        lits = set()
        for c in clauses:
            lits.update(c)
        for v in range(1, self.num_vars + 1):
            pos, neg = v in lits, -v in lits
            if pos != neg and v not in assign:
                lit = v if pos else -v
                self.record("pure", f"Pure literal x{v} only occurs "
                                    f"{'positive' if pos else 'negative'}: "
                                    f"x{v} = {pos}",
                            assign, clauses, focus_var=v, depth=depth)
                assign[v] = pos
                clauses = simplify(clauses, lit)
                self.record("pure", f"Assign x{v}={pos}; simplify",
                            assign, clauses, focus_var=v, depth=depth)

        # ---- all clauses satisfied? ----
        if not clauses:
            self.record("sat", "All clauses satisfied — SAT!",
                        assign, clauses, depth=depth)
            return True

        # ---- branch on first unassigned var ----
        branch_var = next((v for v in range(1, self.num_vars + 1)
                           if v not in assign), None)
        if branch_var is None:
            # all vars assigned but clauses remain (shouldn't happen after
            # unit checks, but guard)
            self.record("conflict", "Variables exhausted with clauses left",
                        assign, clauses, depth=depth)
            return False

        self.record("branch", f"Branch: try x{branch_var} = True",
                    assign, clauses, focus_var=branch_var, depth=depth)
        trial = dict(assign)
        trial[branch_var] = True
        if self._solve(trial, depth + 1,
                       simplify(clauses, branch_var)):
            return True
        self.record("backtrack", f"x{branch_var}=True failed — try x{branch_var} = False",
                    assign, clauses, focus_var=branch_var, depth=depth)
        trial2 = dict(assign)
        trial2[branch_var] = False
        if self._solve(trial2, depth + 1,
                       simplify(clauses, -branch_var)):
            return True
        return False


def simplify(clauses, lit):
    """Remove satisfied clauses, drop falsified literals."""
    out = []
    for c in clauses:
        if lit in c:
            continue
        if -lit in c:
            c2 = [l for l in c if l != -lit]
            out.append(c2)
        else:
            out.append(list(c))
    return out


def fmt_cl(c):
    if not c:
        return "⊥ (empty)"
    return "(" + " ∨ ".join(
        f"x{abs(l)}" if l > 0 else f"¬x{abs(l)}" for l in c) + ")"


def fmt_cnf(clauses):
    if not clauses:
        return "∅ (all satisfied)"
    return " ∧ ".join(fmt_cl(c) for c in clauses)
