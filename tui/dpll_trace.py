"""DPLL trace engine v2 — textbook DPLL with fully recorded reasoning.

Every decision point records a SCAN step showing what was checked
(unit clauses? pure literals?) and what was found — so a learner sees
*why* the algorithm branches when nothing else applies. Branching uses
the lowest-index unassigned variable, trying True first.
"""
from __future__ import annotations

from dataclasses import dataclass, field


@dataclass
class DStep:
    kind: str            # init|scan|unit|pure|branch|conflict|backtrack|sat|unsat
    desc: str
    assign: dict
    frame_clauses: list
    highlight: list = field(default_factory=list)
    focus_var: int = 0
    depth: int = 0
    note: str = ""       # extra explanatory line shown in UI


class DPLLTracer:
    def __init__(self, clauses, num_vars):
        self.steps: list[DStep] = []
        self.clauses = [list(c) for c in clauses]
        self.num_vars = num_vars

    def record(self, kind, desc, assign, frame_clauses, highlight=(),
               focus_var=0, depth=0, note=""):
        self.steps.append(DStep(kind, desc, dict(assign),
                                [list(c) for c in frame_clauses],
                                list(highlight), focus_var, depth, note))

    def run(self) -> list[DStep]:
        self.record("init", "Start: full formula, nothing assigned.",
                    {}, self.clauses,
                    note=f"{len(self.clauses)} clauses, "
                         f"{self.num_vars} variables")
        self._solve({}, 0, [list(c) for c in self.clauses])
        return self.steps

    # ------------------------------------------------------------------
    def _scan_step(self, assign, clauses, depth):
        """Record a scan step: what did we look for, what did we find?"""
        unit_i = next((i for i, c in enumerate(clauses) if len(c) == 1), None)
        if unit_i is not None:
            lit = clauses[unit_i][0]
            self.record("scan",
                        f"Scan: found unit clause {fmt_cl(clauses[unit_i])} "
                        f"→ must assign x{abs(lit)}={lit > 0}",
                        assign, clauses, highlight=[unit_i],
                        focus_var=abs(lit), depth=depth,
                        note="A clause with one unassigned literal "
                             "forces its value (unit propagation)")
            return "unit", unit_i

        # any empty clause?
        empty_i = next((i for i, c in enumerate(clauses) if not c), None)
        if empty_i is not None:
            self.record("scan", "Scan: found an empty clause — conflict",
                        assign, clauses, highlight=[empty_i], depth=depth,
                        note="A clause whose literals are all falsified "
                             "can never be satisfied")
            return "conflict", empty_i

        # pure literal?
        lits = set()
        for c in clauses:
            lits.update(c)
        for v in range(1, self.num_vars + 1):
            if v in assign:
                continue
            pos, neg = v in lits, -v in lits
            if pos != neg:
                self.record("scan",
                            f"Scan: no unit clause. x{v} occurs only "
                            f"{'positively' if pos else 'negatively'} "
                            f"→ pure literal, set x{v}={pos}",
                            assign, clauses, focus_var=v, depth=depth,
                            note="A pure literal can always be set to make "
                                 "its clauses true — never hurts")
                return "pure", (v, pos)

        if not clauses:
            return "sat", None

        # nothing forced: branch on lowest-index unassigned var
        bv = next(v for v in range(1, self.num_vars + 1) if v not in assign)
        self.record("scan",
                    f"Scan: no unit clause, no pure literal "
                    f"({len(clauses)} clauses remain, all with ≥2 free "
                    f"literals). Branch on lowest-index unassigned x{bv}",
                    assign, clauses, focus_var=bv, depth=depth,
                    note="Nothing is forced — DPLL must guess. "
                         "Try True first; backtrack if it fails")
        return "branch", bv

    # ------------------------------------------------------------------
    def _solve(self, assign, depth, clauses):
        while True:
            kind, info = self._scan_step(assign, clauses, depth)
            if kind == "conflict":
                self.record("conflict", "Empty clause — this branch fails",
                            assign, clauses, highlight=[info], depth=depth)
                return False
            if kind == "sat":
                self.record("sat", "No clauses remain — all satisfied. SAT!",
                            assign, clauses, depth=depth)
                return True
            if kind == "unit":
                lit = clauses[info][0]
                v = abs(lit)
                self.record("unit", f"Unit propagation: x{v} = {lit > 0}",
                            assign, clauses, highlight=[info], focus_var=v,
                            depth=depth)
                assign[v] = lit > 0
                clauses = simplify(clauses, lit)
                continue
            if kind == "pure":
                v, pos = info
                lit = v if pos else -v
                self.record("pure", f"Pure literal: x{v} = {pos}",
                            assign, clauses, focus_var=v, depth=depth)
                assign[v] = pos
                clauses = simplify(clauses, lit)
                continue
            if kind == "branch":
                bv = info
                self.record("branch", f"Branch 1: x{bv} = True",
                            assign, clauses, focus_var=bv, depth=depth)
                trial = dict(assign)
                trial[bv] = True
                if self._solve(trial, depth + 1,
                               simplify(clauses, bv)):
                    return True
                self.record("backtrack",
                            f"x{bv}=True led to a conflict — undo and try "
                            f"x{bv} = False",
                            assign, clauses, focus_var=bv, depth=depth,
                            note="Chronological backtracking: flip the "
                                 "most recent guess")
                trial2 = dict(assign)
                trial2[bv] = False
                if self._solve(trial2, depth + 1,
                               simplify(clauses, -bv)):
                    return True
                self.record("backtrack",
                            f"x{bv}=False also failed — both values "
                            f"exhausted; backjump further up",
                            assign, clauses, focus_var=bv, depth=depth)
                return False
            break
        return False


def simplify(clauses, lit):
    out = []
    for c in clauses:
        if lit in c:
            continue
        if -lit in c:
            out.append([l for l in c if l != -lit])
        else:
            out.append(list(c))
    return out


def fmt_cl(c):
    if not c:
        return "⊥ (empty)"
    return "(" + " ∨ ".join(
        f"x{abs(l)}" if l > 0 else f"¬x{abs(l)}" for l in c) + ")"
