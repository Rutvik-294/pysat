"""Command-line SAT solver.

Usage:
    python -m solver file.cnf [--max-conflicts N] [--seed N]

Reads DIMACS CNF, prints SAT/UNSAT plus model and statistics.
Exit codes: 10 = SAT, 20 = UNSAT (DIMACS SAT competition convention),
1 = error / budget exhausted.
"""
from __future__ import annotations

import argparse
import sys
import time

from .cdcl import Solver
from .cnf import parse_dimacs


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(prog="pysat", description="CDCL SAT solver")
    ap.add_argument("cnf_file", help="DIMACS CNF file ('-' for stdin)")
    ap.add_argument("--seed", type=int, default=2026)
    ap.add_argument("--max-conflicts", type=int, default=0,
                    help="conflict budget; 0 = unlimited")
    ap.add_argument("--quiet", action="store_true")
    args = ap.parse_args(argv)

    text = sys.stdin.read() if args.cnf_file == "-" else open(args.cnf_file).read()
    cnf = parse_dimacs(text)

    t0 = time.perf_counter()
    solver = Solver(cnf, seed=args.seed, max_conflicts=args.max_conflicts)
    model = solver.solve()
    dt = time.perf_counter() - t0

    if model is None:
        # distinguish proven UNSAT from budget exhaustion
        exhausted = (args.max_conflicts and
                     solver.stats.conflicts >= args.max_conflicts)
        if not args.quiet:
            status = "INDETERMINATE (budget exhausted)" if exhausted else "UNSATISFIABLE"
            print(f"s {status}")
            st = solver.stats.as_dict()
            print(f"c conflicts={st['conflicts']} decisions={st['decisions']} "
                  f"propagations={st['propagations']} learned={st['learned']} "
                  f"restarts={st['restarts']} time={dt:.3f}s")
        return 20 if not exhausted else 1

    if not args.quiet:
        lits = " ".join(str(v if model[v] else -v) for v in sorted(model))
        print(f"s SATISFIABLE")
        print(f"v {lits} 0")
        st = solver.stats.as_dict()
        print(f"c conflicts={st['conflicts']} decisions={st['decisions']} "
              f"propagations={st['propagations']} learned={st['learned']} "
              f"restarts={st['restarts']} reduced={st['reduced']} time={dt:.3f}s")

        # self-check: verify the model
        for cl in cnf.clauses:
            if not any(model[abs(l)] == (l > 0) for l in cl):
                print("c INTERNAL ERROR: model does not satisfy formula",
                      file=sys.stderr)
                return 1
        print("c model verified against all clauses")
    return 10


if __name__ == "__main__":
    sys.exit(main())
