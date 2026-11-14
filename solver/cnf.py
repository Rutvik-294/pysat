"""CNF representation and DIMACS parser."""
from __future__ import annotations

class CNF:
    """A CNF formula over literals 1..n (negative = negation).

    Clauses are tuples of non-tautological literal lists. Empty clause
    means the formula is trivially UNSAT.
    """
    __slots__ = ("clauses", "num_vars")

    def __init__(self, num_vars: int = 0, clauses=None):
        self.num_vars = num_vars
        self.clauses: list[list[int]] = [list(c) for c in (clauses or [])]

    def add_clause(self, *lits: int):
        if not lits:
            self.clauses.append([])
            return
        self.num_vars = max(self.num_vars, max(abs(l) for l in lits))
        self.clauses.append(list(lits))

    def extended(self, extra_vars: int = 1) -> int:
        """Reserve extra_vars fresh variables; returns first new index."""
        first = self.num_vars + 1
        self.num_vars += extra_vars
        return first

    @property
    def num_clauses(self) -> int:
        return len(self.clauses)

    def copy(self) -> "CNF":
        return CNF(self.num_vars, [list(c) for c in self.clauses])


def parse_dimacs(text: str) -> CNF:
    """Parse DIMACS CNF format. Handles 'c' comments, 'p cnf' header,
    clauses terminated by 0, and clauses spanning multiple lines."""
    num_vars = 0
    clauses: list[list[int]] = []
    current: list[int] = []
    seen_header = False
    for raw in text.splitlines():
        line = raw.strip()
        if not line or line.startswith("c") or line.startswith("%"):
            continue
        if line.startswith("p"):
            parts = line.split()
            if len(parts) >= 4 and parts[1] == "cnf":
                num_vars = int(parts[2])
                seen_header = True
            continue
        for tok in line.split():
            lit = int(tok)
            if lit == 0:
                clauses.append(current)
                current = []
            else:
                current.append(lit)
                num_vars = max(num_vars, abs(lit))
    if current:
        clauses.append(current)  # last clause without trailing 0
    return CNF(num_vars, clauses)


def write_dimacs(cnf: CNF) -> str:
    out = [f"p cnf {cnf.num_vars} {len(cnf.clauses)}"]
    for c in cnf.clauses:
        out.append(" ".join(str(l) for l in c) + " 0")
    return "\n".join(out) + "\n"
