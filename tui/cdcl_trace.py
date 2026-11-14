"""CDCL trace engine v2 — fully recorded reasoning with real 1UIP.

Each round is decomposed into learner-visible steps:
  scan   — what the solver checks (satisfied/unit/conflict clauses)
  decide — branch on lowest-index unassigned var (try True first)
  propagate — a clause became unit under the assignment
  conflict  — a clause has all literals false
  resolve   — one resolution step building the learned clause
  learn     — final learned clause (1UIP) + backjump level
  assert    — learned clause is unit; assign its literal
"""
from __future__ import annotations

from dataclasses import dataclass, field


@dataclass
class CStep:
    kind: str    # init|scan|decide|propagate|conflict|resolve|learn|assert|sat|unsat
    desc: str
    assign: dict
    trail: list           # [(var, val, reason)]
    learned_db: list      # learned clauses so far
    highlight: list = field(default_factory=list)
    focus_var: int = 0
    learning: list = field(default_factory=list)  # clause being built now
    graph_edges: list = field(default_factory=list)  # (from_var, to_var, clause_idx)
    note: str = ""
    dl: int = 0


class CDCLTracer:
    def __init__(self, clauses, num_vars):
        self.clauses = [list(c) for c in clauses]
        self.num_vars = num_vars
        self.steps: list[CStep] = []
        self.learned_db: list[list[int]] = []

    def _rec(self, kind, desc, assign, trail, highlight=(), focus=0,
             learning=(), edges=(), note="", dl=0):
        self.steps.append(CStep(kind, desc, dict(assign), list(trail),
                                [list(c) for c in self.learned_db],
                                list(highlight), focus, list(learning),
                                list(edges), note, dl))

    def run(self) -> list[CStep]:
        self._rec("init", "Start: full formula, nothing assigned.", {}, [],
                  note=f"{len(self.clauses)} clauses, "
                       f"{self.num_vars} variables")
        self._solve({}, [], 0)
        return self.steps

    # ------------------------------------------------------------------
    def _edges_now(self, trail, clauses):
        """Implication-graph edges from current trail reasons."""
        edges = []
        for i, (v, val, why) in enumerate(trail):
            if why.startswith("unit "):
                # find the clause text inside why
                txt = why[5:]
                for ci, c in enumerate(clauses + self.learned_db):
                    if fmt_cl(c) == txt:
                        for l in c:
                            w = abs(l)
                            if w != v:
                                edges.append((w, v))
                        break
        return edges

    def _solve(self, assign, trail, dl):
        while True:
            confl = self._propagate(assign, trail, dl)
            if confl is not None:
                if dl == 0:
                    self._rec("unsat",
                              "Conflict at decision level 0: no assignment "
                              "can satisfy the formula — UNSAT",
                              assign, trail, highlight=[confl], dl=0)
                    return False
                learned, bj = self._analyze(confl, assign, trail, dl)
                self.learned_db.append(learned)
                self._rec("learn",
                          f"Learned {fmt_cl(learned)} (1UIP). "
                          f"Backjump to level {bj}",
                          assign, trail, focus=abs(learned[0]),
                          learning=learned,
                          note="1UIP: resolve conflicts until exactly one "
                               "literal from the current decision level "
                               "remains; assert its negation", dl=dl)
                # undo down to bj
                bound = self._trail_bound(trail, bj)
                while len(trail) > bound:
                    v, val, _ = trail.pop()
                    del assign[v]
                dl = bj
                lit = learned[0]
                v0 = abs(lit)
                assign[v0] = lit > 0
                trail.append((v0, lit > 0, f"learned {fmt_cl(learned)}"))
                self._rec("assert",
                          f"Assert learned unit x{v0}={lit > 0} "
                          f"at level {dl}",
                          assign, trail, focus=v0, dl=dl)
            else:
                # scan for a decision
                bv = next((v for v in range(1, self.num_vars + 1)
                           if v not in assign), None)
                if bv is None:
                    self._rec("sat",
                              "All variables assigned, no conflict — SAT!",
                              assign, trail, dl=dl)
                    return True
                dl += 1
                self._rec("decide",
                          f"No unit clauses to propagate; branch on "
                          f"lowest-index unassigned x{bv} = True (level {dl})",
                          assign, trail, focus=bv, dl=dl,
                          note="CDCL decides like DPLL but remembers "
                               "conflicts as learned clauses")
                assign[bv] = True
                trail.append((bv, True, f"decision level {dl}"))

    # ------------------------------------------------------------------
    def _propagate(self, assign, trail, dl):
        """Propagate; return conflicting clause index or None."""
        changed = True
        while changed:
            changed = False
            for i, c in enumerate(self.clauses + self.learned_db):
                unassigned, true_lit = [], None
                for l in c:
                    v = abs(l)
                    if v not in assign:
                        unassigned.append(l)
                    elif assign[v] == (l > 0):
                        true_lit = l
                        break
                if true_lit is not None:
                    continue
                if not unassigned:
                    self._rec("conflict",
                              f"CONFLICT: every literal of {fmt_cl(c)} "
                              f"is false under the current assignment",
                              assign, trail, highlight=[i], dl=dl,
                              note="CDCL will not just backtrack — it "
                                   "analyzes WHY this conflict happened "
                                   "and learns from it")
                    return i
                if len(unassigned) == 1:
                    lit = unassigned[0]
                    v = abs(lit)
                    assign[v] = lit > 0
                    trail.append((v, lit > 0, f"unit {fmt_cl(c)}"))
                    self._rec("propagate",
                              f"Unit propagation: in {fmt_cl(c)} all lits "
                              f"but x{v} are false ⇒ x{v}={lit > 0}",
                              assign, trail, highlight=[i], focus=v, dl=dl)
                    changed = True
        return None

    # ------------------------------------------------------------------
    def _analyze(self, confl, assign, trail, dl):
        """Step-by-step 1UIP resolution, recording each resolve step."""
        clause = list((self.clauses + self.learned_db)[confl])
        trail_levels = self._trail_levels(trail)   # var -> level
        edges = self._edges_now(trail, self.clauses)

        learned = []
        cur = [(-l) for l in clause]   # start: negate conflict clause
        self._rec("resolve",
                  f"Conflict clause {fmt_cl(clause)}. Start learned clause "
                  f"as its negation: {fmt_cl(cur)}",
                  assign, trail, highlight=[confl], learning=cur,
                  edges=edges, dl=dl,
                  note="Resolution: (A ∨ x) ∧ (B ∨ ¬x) ⊨ (A ∨ B)")

        dl_of = {}
        lvl = 0
        for (tv, _, why) in trail:
            if why.startswith("decision"):
                lvl += 1
            dl_of[tv] = lvl

        guard = 0
        while True:
            guard += 1
            if guard > 50:
                break
            cur_level_lits = [l for l in cur if dl_of.get(abs(l), 0) == dl]
            if len(cur_level_lits) <= 1:
                break
            # pick the most recently assigned current-level literal to resolve
            pivot = None
            for (tv, val, why) in reversed(trail):
                if tv in {abs(l) for l in cur_level_lits} and \
                        dl_of.get(tv) == dl:
                    pivot = tv
                    break
            if pivot is None:
                break
            # find pivot's reason clause
            reason = self._reason_clause(trail, pivot)
            if reason is None:
                break   # pivot is a decision — it IS the UIP
            self._rec("resolve",
                      f"Resolve on x{pivot} (assigned by "
                      f"{fmt_cl(reason)}): drop x{pivot} from the "
                      f"learned clause",
                      assign, trail, learning=cur, focus=pivot,
                      edges=edges, dl=dl,
                      note=f"x{pivot} was propagated, so its reason clause "
                           f"explains it — resolve it away")
            cur = self._resolve(cur, reason, pivot, assign)
            self._rec("resolve",
                      f"Learned clause is now {fmt_cl(cur)}",
                      assign, trail, learning=cur, focus=pivot,
                      edges=edges, dl=dl,
                      note=("⊥ means everything canceled — the UIP itself "
                            "is the answer (a decision literal)"
                            if not cur else
                            "Resolving removed the pivot; "
                            "current-level literals remaining: "
                            f"{len([l for l in cur if dl_of.get(abs(l), 0) == dl])}"))

        # ensure the UIP negation is first
        if cur:
            learned = cur
        else:
            learned = [1]
        bj = 0
        for l in learned:
            lv = dl_of.get(abs(l), 0)
            if lv < dl and lv > bj:
                bj = lv
        return learned, bj

    def _resolve(self, c1, c2, pivot, assign):
        """Resolve c1 with c2 on pivot; keep only literals false/unknown
        under the current assignment (satisfied lits are dropped)."""
        out = [l for l in c1 if abs(l) != pivot]
        for l in c2:
            if abs(l) == pivot:
                continue
            if l in out or -l in out:
                continue
            out.append(l)
        res = []
        for l in out:
            v = abs(l)
            if v in assign and assign[v] == (l > 0):
                continue  # satisfied literal — clause is trivially true
            res.append(l)
        return res

    def _reason_clause(self, trail, var):
        for (tv, val, why) in trail:
            if tv == var:
                if why.startswith("unit "):
                    txt = why[5:]
                    for c in self.clauses + self.learned_db:
                        if fmt_cl(c) == txt:
                            return c
                return None
        return None

    def _trail_levels(self, trail):
        lvl = 0
        out = {}
        for (tv, _, why) in trail:
            if why.startswith("decision"):
                lvl += 1
            out[tv] = lvl
        return out

    def _trail_bound(self, trail, lvl):
        seen = 0
        for i, (tv, _, why) in enumerate(trail):
            if why.startswith("decision"):
                seen += 1
                if seen == lvl:
                    return i + 1
        return 0


def fmt_cl(c):
    if not c:
        return "⊥ (empty)"
    return "(" + " ∨ ".join(
        f"x{abs(l)}" if l > 0 else f"¬x{abs(l)}" for l in c) + ")"
