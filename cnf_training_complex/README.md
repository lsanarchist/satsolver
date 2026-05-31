# Complex CNF training pack

This pack contains **90** deterministic DIMACS CNF instances split by intended difficulty:

- `complex_cnf_moderate/` — 43 cases, designed to be clearly harder than the first extra set.
- `complex_cnf_hard/` — 35 cases, larger or structurally harder.
- `complex_cnf_stress/` — 12 cases, deliberately heavy; run with a per-case timeout.

Each CNF has a `c known_status:` comment. The same status is listed in `manifest.csv`.
For SAT cases with a constructive witness, solver-style witness files are in `known_sat_solutions/`.

## Families included

- Balanced planted near-threshold 3-SAT
- Sparse XOR/parity systems encoded as CNF, including inconsistent systems
- Tseitin parity formulas on regular graphs
- Pigeonhole principle PHP
- Ordering-principle formulas
- Ramsey and Van der Waerden coloring formulas
- Mycielski and planted graph-coloring formulas
- N-Queens
- Sudoku-style encodings
- Orthogonal Latin squares, including order-6 Euler/36-officers UNSAT

## Suggested commands inside the project root

```bash
python benchmark_suite.py satsolver /tmp/bench_complex_moderate.txt complex_cnf_moderate --bruteforce-var-limit 16 --cli-script satsolver.py
python benchmark_suite.py satsolver /tmp/bench_complex_hard.txt complex_cnf_hard --bruteforce-var-limit 16 --cli-script satsolver.py
```

For `complex_cnf_stress`, prefer the known-status runner with a timeout:

```bash
python run_complex_known_status.py complex_cnf_stress --timeout 60 --solver satsolver.py
```

The stock `tools/checker.py` validates SAT assignments directly. For UNSAT cases above 16 variables, it can only format-check `UNSAT`; the included runner additionally compares the solver output against the generated `manifest.csv`.
