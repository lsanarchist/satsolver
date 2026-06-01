# CNF Tests

This folder contains 661 parseable unique DIMACS CNF files with known SAT/UNSAT status.
Duplicates were removed by SHA-256 over file bytes.

- `assignment_safe/`: 632 files with at most 500 variables and 2000 clauses.
- `stress_over_limits/`: 29 valid stress files above the assignment limits.
- SAT/UNSAT split: 437 SAT, 224 UNSAT.
- `MANIFEST.tsv`: retained filename, bucket, expected status, size, hash, source count, and original source paths.
- `REMOVED_INVALID.tsv`: parser-edge `.cnf` files removed because they are not valid DIMACS.
- `REMOVED_UNKNOWN.tsv`: 7 valid CNFs removed because they did not have a known SAT/UNSAT oracle.
