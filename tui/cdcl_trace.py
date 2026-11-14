"""CDCL trace engine — records visualization steps from a CDCL run.

Mirrors the pedagogy of the main solver (unit propagation, decision,
conflict, 1UIP learning, backjump) but records every step so the UI can
step forward/backward. Implemented as a self-contained instrumented
CDCL (chronological bookkeeping kept simple for teaching clarity).
"""
from __future__ import annotations

from dataclasses import dataclass, field


@dataclass
class CStep:
    kind: str           # init|decide|propagate|conflict|learn|backjump|sat|unsat
    desc: str
    assign: dict        # var -> True/False
    learned: list       # learned clause so far (list of lists)
    trail: list         # ordered list of (var, value, reason_desc)
    highlight: list = field(default_factory=list)
    focus_var: int = 0
    graph_edges: list = field(default_factory=list)  # implication graph edges


class CDCLTracer:
    """Simplified CDCL that records steps. Same algorithm family as
    solver.cdcl but linear-scale and teaching-oriented."""

    def __init__(self, clauses, num_vars):
        self.clauses = [list(c) for c in clauses]
        self.num_vars = num_vars
        self.steps: list[CStep] = []
        self.learned: list[list[int]] = []

    def _rec(self, kind, desc, assign, trail, highlight=(), focus=0,
             edges=()):
        self.steps.append(CStep(kind, desc, dict(assign),
                                [list(c) for c in self.learned],
                                list(trail), list(highlight), focus,
                                list(edges)))

    def run(self) -> list[CStep]:
        self._rec("init", "Formula loaded. Ready.", {}, [])
        self._solve({}, [])
        # _solve always ends with its own sat/unsat record
        return self.steps

    def _solve(self, assign, trail):
        dl = 0
        while True:
            confl = self._propagate(assign, trail, dl)
            if confl is not None:
                self.stats_conflicts = getattr(self, "stats_conflicts", 0) + 1
                if dl == 0:
                    self._rec("unsat", "Conflict at decision level 0 — UNSAT",
                              assign, trail, highlight=[confl])
                    return False
                learned, bj, desc = self._analyze(confl, assign, trail, dl)
                self.learned.append(learned)
                self._rec("learn", desc, assign, trail,
                          highlight=[confl], focus=abs(learned[0]))
                # chronological cancel to backjump level
                while trail and self._level_of(trail, bj) is not None and \
                        len(trail) > self._trail_bound(trail, bj):
                    v, val, _ = trail.pop()
                    del assign[v]
                dl = bj
                # learned clause must be unit here
                lit = learned[0]
                assign[abs(lit)] = lit > 0
                trail.append((abs(lit), lit > 0,
                              f"learned {fmt_cl(learned)}"))
                self._rec("propagate",
                          f"Assert learned unit: x{abs(lit)}={lit > 0}",
                          assign, trail, focus=abs(lit))
            else:
                v = self._pick(assign)
                if v is None:
                    self._rec("sat", "All variables assigned, no conflict — SAT!",
                              assign, trail)
                    return True
                dl += 1
                assign[v] = True
                trail.append((v, True, f"decision level {dl}"))
                self._rec("decide", f"Decision: x{v} = True (level {dl})",
                          assign, trail, focus=v)

    def _propagate(self, assign, trail, dl):
        """Return index of conflicting clause, or None."""
        changed = True
        while changed:
            changed = False
            for i, c in enumerate(self.clauses + self.learned):
                unassigned, false_lits, true_lit = [], 0, None
                for l in c:
                    v = abs(l)
                    if v not in assign:
                        unassigned.append(l)
                    elif assign[v] == (l > 0):
                        true_lit = l
                        break
                    else:
                        false_lits += 1
                if true_lit is not None:
                    continue
                if not unassigned:
                    self._rec("conflict",
                              f"Conflict: {fmt_cl(c)} all false",
                              assign, trail, highlight=[i])
                    return i
                if len(unassigned) == 1:
                    lit = unassigned[0]
                    v = abs(lit)
                    assign[v] = lit > 0
                    trail.append((v, lit > 0, f"unit {fmt_cl(c)}"))
                    self._rec("propagate",
                              f"Unit {fmt_cl(c)} ⇒ x{v}={lit > 0}",
                              assign, trail, highlight=[i], focus=v)
                    changed = True
        return None

    def _analyze(self, confl, assign, trail, dl):
        """1UIP-style: negate literals from the conflict at current level."""
        c = (self.clauses + self.learned)[confl]
        learned = [-l for l in c]     # negate all lits (teaching form)
        bj = 0
        for l in learned:
            v = abs(l)
            # lowest level other than current among antecedents; teaching:
            # backjump to level 1 if any lower-level lits exist
        levels = {self._var_level(trail, abs(l)) for l in c}
        lower = {lv for lv in levels if lv < dl and lv > 0}
        if lower:
            bj = max(lower)
        else:
            bj = 0
        desc = (f"Learn: {fmt_cl(learned)} — negation of conflict; "
                f"backjump to level {bj}")
        return learned, bj, desc

    def _pick(self, assign):
        for v in range(1, self.num_vars + 1):
            if v not in assign:
                return v
        return None

    def _var_level(self, trail, v):
        lvl = 0
        for i, (tv, _, reason) in enumerate(trail):
            if reason.startswith("decision"):
                lvl += 1
            if tv == v:
                return lvl
        return 0

    def _level_of(self, trail, lvl):
        return True

    def _trail_bound(self, trail, lvl):
        """Index in trail just after the (lvl)-th decision."""
        seen = 0
        for i, (tv, _, reason) in enumerate(trail):
            if reason.startswith("decision"):
                seen += 1
                if seen == lvl:
                    return i + 1
        return 0


def fmt_cl(c):
    if not c:
        return "⊥ (empty)"
    return "(" + " ∨ ".join(
        f"x{abs(l)}" if l > 0 else f"¬x{abs(l)}" for l in c) + ")"
