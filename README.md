# pysat — a CDCL SAT solver in pure Python

A conflict-driven clause-learning (CDCL) Boolean satisfiability solver
implementing the core architecture of modern solvers (MiniSat lineage)
in ~600 lines of dependency-free Python.

```
        _..._
      .'     '.      (x1 ∨ ¬x2 ∨ x3) ∧ (¬x1 ∨ x2) ∧ ...
     /  _   _  \     12,000 clauses · 729 vars
    |  (o) (o)  |    → solved in 0.7 s
```

## What's inside

| Component | Technique |
|---|---|
| Propagation | Two-watched-literal scheme (lazy BCP) |
| Conflict analysis | 1UIP clause learning + non-chronological backjumping |
| Branching | VSIDS activity with lazy max-heap + phase saving |
| Restarts | Luby sequence |
| Clause DB | LBD-based learned-clause reduction |
| Encoders | at-least-one, pairwise AMO, Sinz sequential counters, Tseitin gates |

`Solver.solve()` returns a complete model (`{var: bool}`) on SAT, `None`
on UNSAT. Every SAT answer is verified against all clauses before return.

## Quick start

```python
from solver import CNF, Solver

cnf = CNF()
cnf.add_clause(1, 2)      # (x1 ∨ x2)
cnf.add_clause(-1)        # (¬x1)
model = Solver(cnf).solve()
print(model)              # {1: False, 2: True}
```

Or from DIMACS files:

```bash
python3 -m solver formula.cnf
# s SATISFIABLE
# v 1 -2 3 0
# c conflicts=4 decisions=6 propagations=11 ... time=0.001s
# c model verified against all clauses
```

Exit codes follow the DIMACS convention: 10 = SAT, 20 = UNSAT.

## Real applications (see `examples/`)

- **N-Queens** — n=120 solved in ~8 s
- **Sudoku** — the classic Wikipedia puzzle, 12,018 clauses
- **Graph coloring** — proves the Petersen graph needs 3 colors (UNSAT
  for k=2), then produces a proper 3-coloring

Random 3-SAT at the phase transition (ratio 4.26): n=100 solves in
~18 ms, n=200 UNSAT proofs take ~14 s (pure Python; C implementations
are ~100× faster — this solver trades speed for readability and
zero-install convenience).

## Correctness

The test suite (`tests/test_pysat.py`, 21 tests) validates:

- **Against brute force**: 60 random 3-SAT instances cross-checked with
  exhaustive search at ratios 3.0 / 4.26 / 5.5 — SAT/UNSAT verdicts
  always agree
- **Pigeonhole principle**: PHP(8,7) proven UNSAT — the classic
  exponentially-hard family
- **Model validity**: every SAT model is checked clause-by-clause
- **Determinism**: same seed ⇒ same result
- **Encoders**: exactly-k groups verified by counting assignments
- **Full applications**: N-Queens solutions verified for attack-freedom;
  Sudoku solution verified row/column/box-wise

## Run tests

```bash
python3 tests/test_pysat.py
```

## Design notes

The solver stores clauses in a flat database with per-literal watch
lists. Watch invariants: positions 0 and 1 of each clause hold watched
literals; a clause is visited only when a watched literal becomes
false. Conflict analysis walks the implication graph via the trail and
`reason` pointers, counting unresolved literals at the current decision
level until exactly one (the 1UIP) remains; its negation heads the
learned clause. Backjumping restores only the learned clause's maximum
decision level, skipping intermediate levels entirely.

Learning is what makes CDCL powerful: after each conflict, a new clause
is derived by resolution that excludes the current conflict *and all
conflicts sharing its root cause* — the solver never repeats work.
