"""NPOPS— err, pysat test suite. CDCL correctness, encoders, applications."""
from __future__ import annotations

import random
import sys
import unittest
from itertools import product

sys.path.insert(0, ".")

from solver import CNF, Solver, parse_dimacs
from solver.encoders import at_least_one, at_most_one, exactly_one, at_most_k, exactly_k


def brute_force_sat(cnf: CNF):
    """Reference: exhaustive search. Only for tiny n."""
    n = cnf.num_vars
    for bits in product([True, False], repeat=n):
        model = {i + 1: bits[i] for i in range(n)}
        if all(any(model[abs(l)] == (l > 0) for l in cl) for cl in cnf.clauses):
            return model
    return None


def check_model(cnf: CNF, model) -> bool:
    if model is None:
        return True
    return all(any(model[abs(l)] == (l > 0) for l in cl) for cl in cnf.clauses)


def random_3sat(rng: random.Random, n: int, m: int) -> CNF:
    cnf = CNF(n)
    for _ in range(m):
        vs = rng.sample(range(1, n + 1), 3)
        cnf.add_clause(*[v if rng.random() < 0.5 else -v for v in vs])
    return cnf


class TestCNFParsing(unittest.TestCase):
    def test_dimacs_parse(self):
        text = """c a comment
p cnf 4 3
1 -2 0
2 3 -4 0
-1 0
"""
        cnf = parse_dimacs(text)
        assert cnf.num_vars == 4
        assert cnf.clauses == [[1, -2], [2, 3, -4], [-1]]

    def test_clause_spanning_lines(self):
        cnf = parse_dimacs("p cnf 3 1\n1 2\n-3 0\n")
        assert cnf.clauses == [[1, 2, -3]]

    def test_no_trailing_zero(self):
        cnf = parse_dimacs("p cnf 2 1\n1 -2 0\n3\n")
        assert cnf.clauses == [[1, -2], [3]]
        assert cnf.num_vars == 3

    def test_tautology_ignored(self):
        cnf = CNF(2)
        cnf.add_clause(1, -1, 2)   # tautology -> satisfied, kept but trivial
        # solver should not crash; clause can never be falsified
        assert check_model(cnf, Solver(cnf).solve())

    def test_empty_clause_unsat(self):
        cnf = CNF(2)
        cnf.add_clause(1)
        cnf.add_clause(-1)
        assert Solver(cnf).solve() is None


class TestCDCLCorrectness(unittest.TestCase):
    def test_against_brute_force_random(self):
        rng = random.Random(42)
        for trial in range(60):
            n = 8
            ratio = rng.choice([3.0, 4.26, 5.5])
            cnf = random_3sat(rng, n, int(n * ratio))
            mine = Solver(cnf, seed=trial).solve()
            ref = brute_force_sat(cnf)
            assert (mine is None) == (ref is None), f"trial {trial}"
            if mine is not None:
                assert check_model(cnf, mine)

    def test_satisfied_models_always_valid(self):
        rng = random.Random(7)
        for trial in range(40):
            cnf = random_3sat(rng, 15, 70)
            model = Solver(cnf, seed=trial + 100).solve()
            if model is not None:
                assert check_model(cnf, model), f"invalid model trial {trial}"

    def test_unit_propagation_chain(self):
        # x1 -> x2 -> x3 -> ... -> x10
        cnf = CNF(10)
        cnf.add_clause(-1, 2)
        cnf.add_clause(-2, 3)
        cnf.add_clause(-3, 4)
        cnf.add_clause(1)
        model = Solver(cnf).solve()
        assert model is not None
        assert all(model[i] for i in range(1, 5))

    def test_forced_contradiction_at_level0(self):
        cnf = CNF(3)
        cnf.add_clause(1)
        cnf.add_clause(-1, 2)
        cnf.add_clause(-2, 3)
        cnf.add_clause(-3)      # chain forces contradiction
        assert Solver(cnf).solve() is None

    def test_deterministic_same_seed(self):
        rng = random.Random(11)
        cnf = random_3sat(rng, 20, 91)
        a = Solver(cnf, seed=5).solve()
        b = Solver(cnf, seed=5).solve()
        assert a == b

    def test_conflict_budget(self):
        cnf = random_3sat(random.Random(99), 30, 135)
        s = Solver(cnf, max_conflicts=50)
        result = s.solve()
        # with a tiny budget we may or may not finish; if unfinished, None
        if result is None:
            assert s.stats.conflicts <= 55


class TestClassicalInstances(unittest.TestCase):
    def _pigeonhole(self, n):
        cnf = CNF(n * (n + 1))
        def var(p, h): return p * n + h + 1
        for p in range(n + 1):
            cnf.add_clause(*[var(p, h) for h in range(n)])
        for h in range(n):
            for p1 in range(n + 1):
                for p2 in range(p1 + 1, n + 1):
                    cnf.add_clause(-var(p1, h), -var(p2, h))
        return cnf

    def test_pigeonhole_unsat(self):
        for n in (3, 5, 7):
            assert Solver(self._pigeonhole(n)).solve() is None, f"PHP({n+1},{n})"

    def test_nqueens(self):
        def nqueens(n):
            cnf = CNF(n * n)
            # var(i, j) = i*n + j + 1 : queen at row i, col j
            def var(i, j): return i * n + j + 1
            for i in range(n):
                exactly_one(cnf, [var(i, j) for j in range(n)])  # one per row
            for j in range(n):
                exactly_one(cnf, [var(i, j) for i in range(n)])  # one per col
            # diagonals
            for d in range(-(n - 1), n):
                diag = [var(i, i - d) for i in range(n)
                        if 0 <= i - d < n]
                at_most_one(cnf, diag)
            for d in range(2 * n - 1):
                diag = [var(i, d - i) for i in range(n)
                        if 0 <= d - i < n]
                at_most_one(cnf, diag)
            return cnf
        for n in (4, 6, 8, 10):
            model = Solver(nqueens(n)).solve()
            assert model is not None, f"{n}-queens is satisfiable"
            # verify placement
            qs = [(i, j) for i in range(n) for j in range(n)
                  if model[i * n + j + 1]]
            assert len(qs) == n
            rows = [q[0] for q in qs]
            cols = [q[1] for q in qs]
            assert len(set(rows)) == n and len(set(cols)) == n
            assert len({r - c for r, c in qs}) == n
            assert len({r + c for r, c in qs}) == n

    def test_graph_coloring(self):
        def coloring(edges, n_nodes, k):
            cnf = CNF(n_nodes * k)
            def var(node, c): return node * k + c + 1
            for v in range(n_nodes):
                exactly_one(cnf, [var(v, c) for c in range(k)])
            for (u, w) in edges:
                for c in range(k):
                    cnf.add_clause(-var(u, c), -var(w, c))
            return cnf
        # K4 needs 4 colors
        k4 = [(i, j) for i in range(4) for j in range(i + 1, 4)]
        assert Solver(coloring(k4, 4, 3)).solve() is None
        model = Solver(coloring(k4, 4, 4)).solve()
        assert model is not None
        # verify proper coloring
        assign = {}
        for v in range(4):
            cs = [c for c in range(4) if model[v * 4 + c + 1]]
            assert len(cs) == 1
            assign[v] = cs[0]
        for (u, w) in k4:
            assert assign[u] != assign[w]
        # C5 (odd cycle) needs 3 colors
        c5 = [(i, (i + 1) % 5) for i in range(5)]
        assert Solver(coloring(c5, 5, 2)).solve() is None
        assert Solver(coloring(c5, 5, 3)).solve() is not None

    def test_sudoku(self):
        def var(r, c, d): return 81 * (r - 1) + 9 * (c - 1) + d  # 1..729
        def build(puzzle):
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
            for (r, c), d in puzzle.items():
                cnf.add_clause(var(r, c, d))
            return cnf
        puzzle = {
            (1, 1): 5, (1, 2): 3, (1, 5): 7,
            (2, 1): 6, (2, 4): 1, (2, 5): 9, (2, 6): 5,
            (3, 2): 9, (3, 3): 8, (3, 8): 6,
            (4, 1): 8, (4, 5): 6, (4, 9): 3,
            (5, 1): 4, (5, 4): 8, (5, 6): 3, (5, 9): 1,
            (6, 1): 7, (6, 5): 2, (6, 9): 6,
            (7, 2): 6, (7, 7): 2, (7, 8): 8,
            (8, 4): 4, (8, 5): 1, (8, 6): 9, (8, 9): 5,
            (9, 5): 8, (9, 8): 7, (9, 9): 9,
        }
        model = Solver(build(puzzle)).solve()
        assert model is not None
        grid = [[next(d for d in range(1, 10)
                      if model[var(r, c, d)]) for c in range(1, 10)]
                for r in range(1, 10)]
        # verify solution
        for row in grid:
            assert sorted(row) == list(range(1, 10))
        for c in range(9):
            assert sorted(grid[r][c] for r in range(9)) == list(range(1, 10))
        for (r, c), d in puzzle.items():
            assert grid[r - 1][c - 1] == d


class TestEncoders(unittest.TestCase):
    def test_exactly_one(self):
        for _ in range(5):
            cnf = CNF()
            lits = [cnf.extended() for _ in range(3)]
            exactly_one(cnf, lits)
            m = Solver(cnf).solve()
            assert sum(1 for l in lits if m[l]) == 1

    def test_exactly_k(self):
        for k in (0, 1, 3, 5):
            cnf = CNF()
            lits = [cnf.extended() for _ in range(5)]
            exactly_k(cnf, lits, k)
            m = Solver(cnf).solve()
            assert sum(1 for l in lits if m[l]) == k

    def test_at_most_k_never_exceeds(self):
        rng = random.Random(4)
        for trial in range(15):
            cnf = CNF()
            lits = [cnf.extended() for _ in range(8)]
            k = rng.randint(0, 8)
            at_most_k(cnf, lits, k)
            m = Solver(cnf).solve()
            if m is not None:
                assert sum(1 for l in lits if m[l]) <= k

    def test_sequential_counter_equivalence(self):
        """at_most_k(2) of 4 must be UNSAT when 3 forced true."""
        cnf = CNF()
        lits = [cnf.extended() for _ in range(4)]
        at_most_k(cnf, lits, 2)
        cnf.add_clause(lits[0], lits[1])
        cnf.add_clause(lits[2])
        cnf.add_clause(lits[3])
        assert Solver(cnf).solve() is None


class TestSolverStats(unittest.TestCase):
    def test_stats_counted(self):
        cnf = random_3sat(random.Random(2), 25, 110)
        s = Solver(cnf)
        model = s.solve()
        st = s.stats.as_dict()
        if model is not None or st["conflicts"] > 0:
            assert st["decisions"] > 0
            assert st["propagations"] > 0

    def test_learning_happens(self):
        # a formula needing some search
        cnf = random_3sat(random.Random(123), 30, 128)
        s = Solver(cnf)
        s.solve()
        assert s.stats.learned > 0


def run_all() -> bool:
    import unittest
    loader = unittest.TestLoader()
    import test_pysat as mod
    suite = unittest.TestSuite()
    for cls in (TestCNFParsing, TestCDCLCorrectness, TestClassicalInstances,
                TestEncoders, TestSolverStats):
        suite.addTests(loader.loadTestsFromTestCase(cls))
    result = unittest.TextTestRunner(verbosity=2).run(suite)
    return result.wasSuccessful()


if __name__ == "__main__":
    sys.exit(0 if run_all() else 1)
