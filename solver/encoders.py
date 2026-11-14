"""Combinational CNF encoders — the bridge from real problems to SAT.

Each encoder adds clauses to a CNF and returns variable mappings.
Encoders: at-least-one, at-most-one, exactly-k (binomial + sequential
counter), conditional literals, and a Tseitin-style AND gate (used by
examples).
"""
from __future__ import annotations

from .cnf import CNF


def at_least_one(cnf: CNF, lits: list[int]):
    if lits:
        cnf.add_clause(*lits)


def at_most_one(cnf: CNF, lits: list[int]):
    """Naive pairwise AMO: O(n^2) clauses. Fine for small groups."""
    for i in range(len(lits)):
        for j in range(i + 1, len(lits)):
            cnf.add_clause(-lits[i], -lits[j])


def exactly_one(cnf: CNF, lits: list[int]):
    at_least_one(cnf, lits)
    at_most_one(cnf, lits)


def at_most_k(cnf: CNF, lits: list[int], k: int):
    """Sequential counter encoding (Sinz 2005): O(n*k) vars and clauses."""
    n = len(lits)
    if k <= 0:
        for l in lits:
            cnf.add_clause(-l)
        return
    if k >= n:
        return
    # s[i][j] for i in 0..n-1, j in 0..k-1
    s = [[cnf.extended() for _ in range(k)] for _ in range(n)]
    for i in range(n):
        # x_i -> s[i][0]
        cnf.add_clause(-lits[i], s[i][0])
        if i > 0:
            # s[i-1][j] -> s[i][j]
            for j in range(k):
                cnf.add_clause(-s[i - 1][j], s[i][j])
            # x_i & s[i-1][j-1] -> s[i][j]
            for j in range(1, k):
                cnf.add_clause(-lits[i], -s[i - 1][j - 1], s[i][j])
            # x_i & s[i-1][k-1] -> false  (exceeds k)
            cnf.add_clause(-lits[i], -s[i - 1][k - 1])
    # s[0][j] chain start: x_0 & s[0][j-1] -> s[0][j] is vacuous here;
    # only s[i][0] = x_i matters for row 0.


def exactly_k(cnf: CNF, lits: list[int], k: int):
    at_least_k = list(lits)
    at_most_k(cnf, at_least_k, k)
    # at least k == at most (n-k) negated
    neg = [-l for l in lits]
    at_most_k(cnf, neg, len(lits) - k)


def implies(cnf: CNF, a: int, b: int):
    cnf.add_clause(-a, b)


def iff(cnf: CNF, a: int, b: int):
    cnf.add_clause(-a, b)
    cnf.add_clause(a, -b)


def tseitin_and(cnf: CNF, a: int, b: int) -> int:
    """Fresh var c equivalent to a AND b (Tseitin)."""
    c = cnf.extended()
    cnf.add_clause(-c, a)
    cnf.add_clause(-c, b)
    cnf.add_clause(c, -a, -b)
    return c


def tseitin_or(cnf: CNF, a: int, b: int) -> int:
    c = cnf.extended()
    cnf.add_clause(c, -a)
    cnf.add_clause(c, -b)
    cnf.add_clause(-c, a, b)
    return c
