#!/usr/bin/env python3
"""Sudoku via SAT: the classic Wikipedia puzzle, solved by CDCL."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), ".."))

from solver import CNF, Solver
from solver.encoders import exactly_one


def var(r, c, d):
    """Variable for 'cell (r,c) holds digit d', r,c,d in 1..9 -> 1..729."""
    return 81 * (r - 1) + 9 * (c - 1) + d


def sudoku_cnf(givens: dict) -> CNF:
    cnf = CNF(729)
    for r in range(1, 10):
        for c in range(1, 10):
            exactly_one(cnf, [var(r, c, d) for d in range(1, 10)])
    for d in range(1, 10):
        for r in range(1, 10):
            exactly_one(cnf, [var(r, c, d) for c in range(1, 10)])
        for c in range(1, 10):
            exactly_one(cnf, [var(r, c, d) for r in range(1, 10)])
        for br in (1, 4, 7):
            for bc in (1, 4, 7):
                exactly_one(cnf, [var(br + i, bc + j, d)
                                  for i in range(3) for j in range(3)])
    for (r, c), d in givens.items():
        cnf.add_clause(var(r, c, d))
    return cnf


PUZZLE = "530070000600195000098000060800060003400803001700020006060000280000419005000080079"


def main():
    givens = {}
    for i, ch in enumerate(PUZZLE):
        if ch != "0":
            r, c = divmod(i, 9)
            givens[(r + 1, c + 1)] = int(ch)
    model = Solver(sudoku_cnf(givens)).solve()
    if model is None:
        print("puzzle is unsolvable")
        return
    print("Sudoku solution:")
    for r in range(1, 10):
        row = [next(d for d in range(1, 10) if model[var(r, c, d)])
               for c in range(1, 10)]
        print("  " + " ".join(map(str, row)))


if __name__ == "__main__":
    main()
