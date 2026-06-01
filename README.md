# SAT Solver Assignment

Minimal standard-library Python SAT solver prepared for the LPI SAT assignment.

## Run

```bash
python satsolver.py input.cnf output.txt
```

The output file contains either:

- `UNSAT`
- `SAT` followed by one complete assignment line ending in `0`

## Files

- `satsolver.py`: command-line entry point required by the assignment
- `satsolver_fullcpu.py`: optional full-CPU portfolio entry point for one CNF
- `satsolver_core.py`: CDCL solver implementation
- `satsolver_io.py`: DIMACS CNF parser and result writer
- `algorithm_description.md`: short algorithm description to convert to PDF
- `tools/checker.py`: local output validator
- `benchmark_suite.py`: optional local benchmark/validation runner
- `parallel_benchmark_suite.py`: optional throughput runner that runs many CLI cases concurrently
- `cnf_tests/`: retained unique CNF tests with manifests

Keep `satsolver.py`, `satsolver_core.py`, and `satsolver_io.py` together; the CLI entry point imports the two helper modules.

## Local Checks

Single case:

```bash
python satsolver.py cnf_tests/assignment_safe/course_cnf_tests__small__test_1.cnf /tmp/sat.out
python tools/checker.py cnf_tests/assignment_safe/course_cnf_tests__small__test_1.cnf /tmp/sat.out
```

Assignment-safe suite:

```bash
python benchmark_suite.py satsolver /tmp/sat_bench.txt cnf_tests/assignment_safe --bruteforce-var-limit 16 --cli-script satsolver.py
```

CPU-throughput run:

```bash
python parallel_benchmark_suite.py /tmp/sat_parallel.txt cnf_tests/assignment_safe --repeat 1 --jobs 16 --cli-script satsolver.py
```

Full-CPU run for one CNF:

```bash
python satsolver_fullcpu.py cnf_tests/assignment_safe/course_cnf_tests__large__test_6.cnf /tmp/sat_fullcpu.out --workers 16
```

`cnf_tests/assignment_safe/` contains only known SAT/UNSAT cases with at most 500 variables and 2000 clauses. `cnf_tests/stress_over_limits/` keeps larger valid stress cases separately.
