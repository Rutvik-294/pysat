#!/usr/bin/env python3
"""Graph coloring via SAT: color an edge list with k colors, or prove
that k colors are insufficient (UNSAT proof)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), ".."))

from solver import CNF, Solver
from solver.encoders import exactly_one


def coloring_cnf(edges, n_nodes: int, k: int) -> CNF:
    cnf = CNF(n_nodes * k)
    def var(node, color): return node * k + color + 1
    for v in range(n_nodes):
        exactly_one(cnf, [var(v, c) for c in range(k)])
    for (u, w) in edges:
        for c in range(k):
            cnf.add_clause(-var(u, c), -var(w, c))
    return cnf


def main():
    # Petersen graph: chromatic number 3
    edges = [(0,1),(0,3),(0,5),(0,8),(1,2),(1,4),(1,7),(2,3),(2,9),(2,6),
             (3,4),(3,8),(4,5),(4,9),(5,6),(5,7),(6,8),(6,9),(7,9),(7,8)]
    for k in (2, 3):
        model = Solver(coloring_cnf(edges, 10, k)).solve()
        if model is None:
            print(f"Petersen graph with {k} colors: UNSAT (needs more)")
        else:
            colors = [next(c for c in range(k) if model[v * k + c + 1])
                      for v in range(10)]
            print(f"Petersen graph with {k} colors: SAT — {colors}")


if __name__ == "__main__":
    main()
