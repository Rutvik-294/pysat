#!/usr/bin/env python3
"""N-Queens via SAT: encode the puzzle, solve, print the board."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), ".."))

from solver import CNF, Solver
from solver.encoders import exactly_one, at_most_one


def nqueens_cnf(n: int) -> CNF:
    cnf = CNF(n * n)
    def var(i, j): return i * n + j + 1     # queen at row i, col j
    for i in range(n):
        exactly_one(cnf, [var(i, j) for j in range(n)])
    for j in range(n):
        exactly_one(cnf, [var(i, j) for i in range(n)])
    for d in range(-(n - 1), n):
        at_most_one(cnf, [var(i, i - d) for i in range(n) if 0 <= i - d < n])
    for d in range(2 * n - 1):
        at_most_one(cnf, [var(i, d - i) for i in range(n) if 0 <= d - i < n])
    return cnf


def main():
    n = int(sys.argv[1]) if len(sys.argv) > 1 else 8
    model = Solver(nqueens_cnf(n)).solve()
    if model is None:
        print(f"{n}-queens: no solution")
        return
    print(f"{n}-queens solution:")
    for i in range(n):
        row = "".join("Q" if model[i * n + j + 1] else "." for j in range(n))
        print("  " + " ".join(row))


if __name__ == "__main__":
    main()
