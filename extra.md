# Extended Benchmark Notes

Goal: expand the local benchmark with more SATLIB instances while keeping the full run for both solvers comfortably below 5 minutes.

Source:
- SATLIB benchmark index: https://www.cs.ubc.ca/~hoos/SATLIB/benchm.html

Added SATLIB folders:

`satlib_subset/`:
- `uf100-01.cnf`
- `uf100-010.cnf`
- `uuf100-01.cnf`
- `uuf100-010.cnf`
- `flat50-1.cnf`
- `flat50-10.cnf`
- `hole8.cnf`
- `hole10.cnf`
- `dubois20.cnf`
- `dubois21.cnf`

`satlib_more/`:
- `aim-100-1_6-no-1.cnf`
- `aim-100-1_6-no-2.cnf`
- `aim-100-1_6-yes1-1.cnf`
- `aim-100-1_6-yes1-2.cnf`
- `flat75-1.cnf`
- `flat75-10.cnf`
- `jnh1.cnf`
- `jnh10.cnf`
- `uf125-01.cnf`
- `uf125-010.cnf`
- `uuf125-01.cnf`
- `uuf125-010.cnf`
- `uf150-01.cnf`
- `uuf150-01.cnf`

Why this mix:
- Covers both SAT and UNSAT instances
- Adds more families beyond the original local set: random 3-SAT, graph colouring, AIM, JNH, pigeonhole, and Dubois
- Introduces slightly larger random instances without pushing runtime anywhere close to the 5 minute limit

Benchmark commands:

```bash
python benchmark_suite.py satsolver out_extended.txt small medium large special satlib_subset satlib_more
python benchmark_suite.py satsolver_blaze out_blaze_extended.txt small medium large special satlib_subset satlib_more
```

Measured results on the updated 59-case suite:

| Solver | `satlib_subset` total | `satlib_more` total | Full suite total | Wall clock | Worst single case |
| --- | ---: | ---: | ---: | ---: | ---: |
| `satsolver.py` | `0.1334s` | `1.0455s` | `50.2815s` | `50.3255s` | `16.7170s` |
| `satsolver_blaze.py` | `0.1056s` | `0.9395s` | `41.0408s` | `41.0849s` | `17.1070s` |

Combined sequential wall clock for both solvers:
- `91.4104s`

This is still well below the requested 5 minute cap.

Generated reports:
- `out_extended.txt`
- `out_blaze_extended.txt`

Notes:
- Both parsers stop cleanly at the SATLIB `%` terminator used in some DIMACS files.
- The slowest added SATLIB case is `satlib_more/uuf150-01.cnf`, and it stays under 1 second on both solvers.
- `satsolver_blaze.py` remains the faster solver on the enlarged benchmark.
