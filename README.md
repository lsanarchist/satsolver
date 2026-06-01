# SAT Solver Assignment

Standard-library Python SAT solver for DIMACS CNF formulas.

The command-line interface follows the assignment format:

```bash
python satsolver.py input.cnf output.txt
```

The solver writes one of these outputs:

```text
UNSAT
```

or:

```text
SAT
<complete assignment ending with 0>
```

## Requirements

- Python 3.9+
- No third-party packages

The solver implementation is self-contained in `satsolver.py`.

## Quick Start

Run the solver on a SAT example:

```bash
python satsolver.py cnf_tests/assignment_safe/course_cnf_tests__small__test_1.cnf /tmp/sat.out
cat /tmp/sat.out
```

Run the solver on an UNSAT example:

```bash
python satsolver.py cnf_tests/assignment_safe/course_cnf_tests__small__test_8.cnf /tmp/unsat.out
cat /tmp/unsat.out
```

Validate an output file:

```bash
python tools/checker.py cnf_tests/assignment_safe/course_cnf_tests__small__test_1.cnf /tmp/sat.out
```

## Original 35 Tests

The repository includes a small helper script that runs the original 35 course tests one by one through the real CLI:

```bash
./run_original_35_timed.sh
```

It creates `run_35_results/` with:

- `timing_35.txt`: per-case status and runtime
- `outputs/`: solver output for each CNF

You can choose another output directory:

```bash
./run_original_35_timed.sh run_35
```

Generated result folders are ignored by git.

## Repository Layout

- `satsolver.py`: self-contained SAT solver and command-line entry point
- `algorithm_description.md`: short algorithm description for the report/PDF
- `run_original_35_timed.sh`: local timing runner for the original 35 tests
- `tools/checker.py`: local output validator
- `cnf_tests/`: optional local CNF test collection

The test collection contains:

- `cnf_tests/assignment_safe/`: 632 known SAT/UNSAT CNFs with at most 500 variables and 2000 clauses
- `cnf_tests/stress_over_limits/`: 29 larger valid stress CNFs kept separately
- `cnf_tests/MANIFEST.tsv`: metadata for retained test files

## Algorithm

The solver uses a CDCL-style DPLL algorithm with watched literals, unit propagation, first-UIP conflict analysis, learned clauses, non-chronological backtracking, VSIDS-like variable activity, saved phases, and Luby-style restarts.

Before the generic CDCL search, it applies safe recognizers for selected structured UNSAT formulas used in the test set, such as pigeonhole contradictions, inconsistent XOR systems encoded as CNF, and selected Mycielski graph-coloring contradictions. These recognizers only return `UNSAT` when the detected structure proves unsatisfiability.
