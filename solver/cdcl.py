"""CDCL SAT solver — a MiniSat-style conflict-driven clause learner.

Architecture:
  - Two-watched-literal scheme for lazy unit propagation (BCP)
  - Implication graph with reason clauses for conflict analysis
  - 1UIP clause learning + non-chronological backjumping
  - VSIDS-like dynamic variable activity (EVSIDS decay) for branching
  - Luby-sequence restarts and LBD-based clause database reduction

Semantics: solve() returns a total model on SAT, None on UNSAT.
"""
from __future__ import annotations

import math
import random
from collections import deque

from .cnf import CNF

# Literal encoding: internal int = 2*var_index + sign_bit, var_index 0-based.
# lit_from_int(1) = 0 (var 0, positive); -1 = 1 (var 0, negative).
UNDEF = 2  # tri-state value: 0=False, 1=True, 2=undef


def _lit(l: int) -> int:
    """DIMACS literal -> internal encoding."""
    v = abs(l) - 1
    return (v << 1) | (1 if l < 0 else 0)


def _var_of(lit: int) -> int:
    return lit >> 1


def _neg(lit: int) -> int:
    return lit ^ 1


def _sign(lit: int) -> int:
    return lit & 1


class ClauseDB:
    """Clause storage with two-watched-literal support.

    Clauses 0..n_orig-1 are problem clauses; learned clauses append.
    Each clause: list of internal literals; watches index literals by
    their first two positions (maintained during propagation).
    """
    __slots__ = ("clauses", "watches", "size", "lbd", "learnt_from", "deleted")

    def __init__(self, num_vars: int):
        # 2*(num_vars+1) watch lists (one per literal encoding)
        self.watches: list[list[int]] = [[] for _ in range(2 * (num_vars + 1))]
        self.clauses: list[list[int]] = []
        self.lbd: list[int] = []
        self.learnt_from: list[int] = []  # 0 = problem clause, else conflict #
        self.deleted: list[bool] = []
        self.size = 0

    def new_clause(self, lits: list[int], learnt: bool = False, lbd: int = 0,
                   from_conflict: int = 0) -> int:
        idx = self.size
        self.clauses.append(lits)
        self.lbd.append(lbd)
        self.learnt_from.append(from_conflict if learnt else 0)
        self.deleted.append(False)
        self.size += 1
        return idx

    def watch(self, clause_idx: int, lit: int):
        self.watches[lit].append(clause_idx)

    def unwatch(self, clause_idx: int, lit: int):
        ws = self.watches[lit]
        try:
            ws.remove(clause_idx)
        except ValueError:
            pass

    def remove_clause(self, idx: int):
        if not self.deleted[idx]:
            c = self.clauses[idx]
            if len(c) >= 2:
                self.unwatch(idx, c[0])
                self.unwatch(idx, c[1])
            self.deleted[idx] = True


class SolverStats:
    __slots__ = ("decisions", "propagations", "conflicts", "learned",
                 "restarts", "reduced", "backjumps")

    def __init__(self):
        self.decisions = 0
        self.propagations = 0
        self.conflicts = 0
        self.learned = 0
        self.restarts = 0
        self.reduced = 0
        self.backjumps = 0

    def as_dict(self) -> dict:
        return {k: getattr(self, k) for k in (
            "decisions", "propagations", "conflicts", "learned",
            "restarts", "reduced", "backjumps")}


class Solver:
    """CDCL solver. Usage:

        s = Solver(cnf)
        model = s.solve()      # dict {var(1-based): bool} or None
        print(s.stats.as_dict())
    """

    def __init__(self, cnf: CNF, seed: int = 2026, max_conflicts: int = 0):
        self.n = cnf.num_vars
        self.db = ClauseDB(self.n)
        self.stats = SolverStats()
        self.rng = random.Random(seed)
        self.max_conflicts = max_conflicts  # 0 = unlimited

        # assignment state
        self.assign = bytearray([UNDEF] * (self.n + 1))
        self.level = [0] * (self.n + 1)       # decision level per var (1-based)
        self.reason = [-1] * (self.n + 1)     # clause idx that implied var
        self.activity = [0.0] * (self.n + 1)
        self.saved_phase = bytearray(self.n + 1)  # 0=false-ish, 1=true-ish
        self.var_inc = 1.0
        self.var_decay = 0.95

        # VSIDS lazy heap: entries are (-activity, var); stale entries are
        # skipped on pop (lazy deletion). order tracks heap membership.
        import heapq
        self._heapq = heapq
        self._heap = [(-1.0, v) for v in range(1, self.n + 1)]
        heapq.heapify(self._heap)
        self._in_heap = bytearray([1] * (self.n + 1))

        # trail: sequence of assigned vars; trail_lim: marks per decision level
        self.trail: list[int] = []            # list of vars (1-based)
        self.trail_lim: list[int] = []

        # queue of vars awaiting BCP (as internal literals to visit)
        self.prop_queue: deque[int] = deque()

        self.ok = True
        # load problem clauses
        self._load(cnf)
        if not self.ok:
            return

        # restart / reduce state (Luby)
        self.restart_count = 0
        self.luby_i = 1
        self.luby_k = 0
        self.conflicts_since_restart = 0
        self.restart_limit = self._luby_next() * 100
        self.reduce_limit = 2000
        self.conflict_no = 0

        self.model: dict[int, bool] | None = None

    # ------------------------------------------------------------------
    def _load(self, cnf: CNF):
        for c in cnf.clauses:
            if not self._add_clause([_lit(l) for l in c]):
                self.ok = False
                return

    def _add_clause(self, lits: list[int]) -> bool:
        """Unit-propagate trivial cases, register clause with watches."""
        if not lits:
            return False
        # dedupe + check tautology + simplify against current assignment
        seen = set()
        out = []
        for l in lits:
            v = _var_of(l)
            if v > self.n:
                return False
            if _neg(l) in seen:
                return True  # tautology
            if l not in seen:
                seen.add(l)
                out.append(l)
        lits = out
        if not lits:
            return False
        if len(lits) == 1:
            return self._enqueue(lits[0], -1)
        idx = self.db.new_clause(lits)
        self.db.watch(idx, lits[0])
        self.db.watch(idx, lits[1])
        return True

    def _enqueue(self, lit: int, reason_idx: int) -> bool:
        v = _var_of(lit) + 1  # 1-based
        val = self.assign[v]
        if val != UNDEF:
            return (val == 1) != bool(_sign(lit))  # already consistent?
        if _sign(lit):
            self.assign[v] = 0
        else:
            self.assign[v] = 1
        self.saved_phase[v] = _sign(lit)   # phase saving
        self.level[v] = self.current_level()
        self.reason[v] = reason_idx
        self.trail.append(v)
        self.prop_queue.append(lit)
        return True

    def current_level(self) -> int:
        return len(self.trail_lim)

    # ------------------------------------------------------------------
    # Two-watched-literal propagation
    # ------------------------------------------------------------------
    def _propagate(self) -> int:
        """Process propagation queue. Returns conflicting clause or -1."""
        while self.prop_queue:
            lit = self.prop_queue.popleft()
            self.stats.propagations += 1
            falsified = _neg(lit)  # clauses watching 'falsified' may fail
            ws = self.db.watches[falsified]
            i, j = 0, 0
            n = len(ws)
            while i < n:
                ci = ws[i]
                i += 1
                if self.db.deleted[ci]:
                    continue
                c = self.db.clauses[ci]
                # ensure falsified is c[1]
                if c[0] == falsified:
                    c[0], c[1] = c[1], c[0]
                first = c[0]
                v1 = _var_of(first) + 1
                # if first is true, clause satisfied; keep watch
                if self.assign[v1] == (0 if _sign(first) else 1):
                    ws[j] = ci
                    j += 1
                    continue
                # look for a new literal to watch
                moved = False
                for k in range(2, len(c)):
                    lk = c[k]
                    vk = _var_of(lk) + 1
                    val = self.assign[vk]
                    if val == UNDEF or val == (0 if _sign(lk) else 1):
                        c[1], c[k] = c[k], c[1]
                        self.db.watch(ci, c[1])
                        moved = True
                        break
                if moved:
                    continue  # old watch on falsified dropped
                # unit or conflict
                ws[j] = ci
                j += 1
                if not self._enqueue(first, ci):
                    # conflict: drop remaining watches beyond j
                    for t in range(i, n):
                        ws[t - (i - j)] = ws[t] if t - (i - j) >= j else ws[t]
                    del ws[j + (n - i):]
                    while self.prop_queue:
                        self.prop_queue.clear()
                    return ci
            del ws[j:]
        return -1

    # ------------------------------------------------------------------
    # VSIDS
    # ------------------------------------------------------------------
    def _bump_var(self, v: int):
        self.activity[v] += self.var_inc
        if self.activity[v] > 1e100:
            for i in range(1, self.n + 1):
                self.activity[i] *= 1e-100
            self.var_inc *= 1e-100
            # rebuild heap after global rescale
            self._heap = [(-self.activity[x], x) for x in range(1, self.n + 1)
                          if self.assign[x] == UNDEF]
            self._heapq.heapify(self._heap)
            for act, x in self._heap:
                self._in_heap[x] = 1
            return
        if self._in_heap[v]:
            # push updated entry (lazy: old entry becomes stale)
            self._heapq.heappush(self._heap, (-self.activity[v], v))

    def _decay_var_activity(self):
        self.var_inc /= self.var_decay

    def _pick_branch(self) -> int:
        """Pop max-activity unassigned var from the lazy heap."""
        heap = self._heap
        while heap:
            neg_act, v = self._heapq.heappop(heap)
            if self.assign[v] == UNDEF and neg_act == -self.activity[v]:
                self._in_heap[v] = 0
                return v
            # stale entry: drop
        # heap exhausted: find any unassigned var
        for v in range(1, self.n + 1):
            if self.assign[v] == UNDEF:
                return v
        return 0

    # ------------------------------------------------------------------
    # Conflict analysis (1UIP)
    # ------------------------------------------------------------------
    def _lit_of_var(self, v: int) -> int:
        val = self.assign[v]
        # internal literal representing current truth of v
        return ((v - 1) << 1) | (0 if val == 1 else 1)

    def _analyze(self, confl: int) -> tuple[list[int], int]:
        """Textbook 1UIP: walk the implication graph backwards.

        Returns (learned clause in internal lits, backjump level).
        """
        seen = bytearray(self.n + 1)
        learned: list[int] = []   # falsified lits from lower decision levels
        counter = 0               # vars at current level left to resolve
        p = -1                    # current resolution literal (as var, 1-based)
        dl = self.current_level()
        cur = confl
        trail_pos = len(self.trail)
        while True:
            c = self.db.clauses[cur]
            for k in range(len(c)):
                l = c[k]
                # skip the literal resolved on (p appears falsified in cur)
                if p > 0 and _var_of(l) + 1 == p:
                    continue
                v = _var_of(l) + 1
                if not seen[v] and self.level[v] > 0:
                    seen[v] = 1
                    self._bump_var(v)
                    if self.level[v] == dl:
                        counter += 1
                    else:
                        # l is false under the trail; keep it as-is
                        learned.append(l)
            # next resolution literal: nearest seen var on the trail
            p_next = -1
            while trail_pos > 0:
                trail_pos -= 1
                v = self.trail[trail_pos]
                if seen[v]:
                    p_next = v
                    break
            if p_next < 0:
                break
            counter -= 1
            p = p_next
            if counter <= 0:
                break  # p is the 1UIP
            seen[p] = 0
            r = self.reason[p]
            if r < 0:
                break  # p was a decision; shouldn't happen before counter hits 0
            cur = r
        # UIP negation heads the clause (it is the literal we assert)
        learned.insert(0, _neg(self._lit_of_var(p)))
        bj = 0
        for l in learned[1:]:
            v = _var_of(l) + 1
            if self.level[v] > bj:
                bj = self.level[v]
        learned = self._minimize(learned)
        return learned, bj

    def _minimize(self, learned: list[int]) -> list[int]:
        """Self-subsumption: drop literal L if some other literal's reason
        clause implies L (transitive closure over reasons, bounded)."""
        if len(learned) <= 2:
            return learned
        kept_vars = {_var_of(l) for l in learned}
        removable = set()
        for l in learned[1:]:
            v = _var_of(l) + 1
            r = self.reason[v]
            if r < 0:
                continue
            # if every other var in the reason is marked seen/kept at lower
            # level, v is redundant (implied by resolution)
            others = [ _var_of(x) + 1 for x in self.db.clauses[r]
                       if _var_of(x) + 1 != v ]
            if others and all(
                self.level[w] > 0 and (w - 1) in kept_vars or
                (self.reason[w] >= 0 and self._implied_by(w, kept_vars, depth=2))
                for w in others
            ):
                removable.add(v - 1)
        if not removable:
            return learned
        return [l for l in learned if _var_of(l) not in removable]

    def _implied_by(self, v: int, marked: set, depth: int) -> bool:
        if depth <= 0:
            return False
        r = self.reason[v]
        if r < 0:
            return False
        others = [_var_of(x) + 1 for x in self.db.clauses[r]
                  if _var_of(x) + 1 != v]
        return all((w - 1) in marked or self._implied_by(w, marked, depth - 1)
                   for w in others)

    # ------------------------------------------------------------------
    # Backtracking
    # ------------------------------------------------------------------
    def _cancel_until(self, lvl: int):
        """Undo assignments above decision level lvl."""
        if self.current_level() <= lvl:
            return
        bound = self.trail_lim[lvl]
        while len(self.trail) > bound:
            v = self.trail.pop()
            self.assign[v] = UNDEF
            self.reason[v] = -1
            # make the var eligible for the branch heap again
            if not self._in_heap[v]:
                self._in_heap[v] = 1
                self._heapq.heappush(self._heap, (-self.activity[v], v))
        del self.trail_lim[lvl:]
        self.prop_queue.clear()

    # ------------------------------------------------------------------
    # Restarts (Luby sequence)
    # ------------------------------------------------------------------
    def _luby_next(self) -> int:
        """Advance and return the next Luby number."""
        k = self.luby_k + 1
        # compute luby(k)
        def luby(i: int) -> int:
            # find smallest power of 2
            size = 1
            seq = 0
            while size < i + 1:
                seq += 1
                size = 2 * size + 1
            while size - 1 != i:
                size = (size - 1) // 2
                i = i % size
            return 2 ** seq
        self.luby_k = k
        return luby(k - 1) if k > 1 else 1

    # ------------------------------------------------------------------
    # Clause DB reduction (LBD)
    # ------------------------------------------------------------------
    def _compute_lbd(self, lits: list[int]) -> int:
        levels = {self.level[_var_of(l) + 1] for l in lits}
        return len(levels)

    def _reduce_db(self):
        """Delete half of the learnt clauses with highest LBD (worst)."""
        learnt_ids = [i for i in range(self.db.size)
                      if self.db.learnt_from[i] and not self.db.deleted[i]
                      and len(self.db.clauses[i]) > 2
                      and self.reason[_var_of(self.db.clauses[i][0]) + 1] != i
                      and self.reason[_var_of(self.db.clauses[i][1]) + 1] != i]
        learnt_ids.sort(key=lambda i: self.db.lbd[i], reverse=True)
        half = len(learnt_ids) // 2
        for i in learnt_ids[:half]:
            self.db.remove_clause(i)
        self.stats.reduced += half
        self.reduce_limit = int(self.reduce_limit * 1.3)

    # ------------------------------------------------------------------
    # Main solve loop
    # ------------------------------------------------------------------
    def solve(self) -> dict[int, bool] | None:
        if not self.ok:
            return None
        dl = 0
        while True:
            confl = self._propagate()
            if confl >= 0:
                self.stats.conflicts += 1
                self.conflict_no += 1
                self.conflicts_since_restart += 1
                if self.current_level() == 0:
                    return None  # UNSAT at level 0
                learned, bj = self._analyze(confl)
                self.stats.learned += 1
                if len(learned) == 1:
                    self._cancel_until(0)
                    self._enqueue(learned[0], -1)
                else:
                    lbd = self._compute_lbd(learned)
                    idx = self.db.new_clause(learned, learnt=True, lbd=lbd,
                                             from_conflict=self.conflict_no)
                    self.db.watch(idx, learned[0])
                    self.db.watch(idx, learned[1])
                    self._cancel_until(bj)
                    self._enqueue(learned[0], idx)
                    self.stats.backjumps += 1
                self._decay_var_activity()
                if self.max_conflicts and self.stats.conflicts >= self.max_conflicts:
                    return None  # budget exhausted (unknown)
                if self.conflicts_since_restart >= self.restart_limit:
                    self.stats.restarts += 1
                    self._cancel_until(0)
                    self.conflicts_since_restart = 0
                    self.restart_limit = self._luby_next() * 100
                if self.stats.conflicts >= self.reduce_limit:
                    self._reduce_db()
            else:
                # decide
                v = self._pick_branch()
                if v == 0:
                    self.model = {i: self.assign[i] == 1
                                  for i in range(1, self.n + 1)}
                    return self.model
                self.stats.decisions += 1
                self.trail_lim.append(len(self.trail))
                # phase saving: reuse last polarity (default positive)
                if self.saved_phase[v]:
                    lit = ((v - 1) << 1) | 1
                else:
                    lit = (v - 1) << 1
                self._enqueue(lit, -1)
