# Extended Benchmark Notes

Goal: expand the local benchmark with a small SATLIB subset while keeping the full benchmark under 5 minutes.

Source:
- SATLIB benchmark index: https://www.cs.ubc.ca/~hoos/SATLIB/benchm.html

Added SATLIB subset in `satlib_subset/`:
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

Reason for this subset:
- Mix of SAT and UNSAT instances
- Mix of random 3-SAT, graph colouring, pigeonhole, and Dubois families
- Very small added runtime, so the benchmark stays comfortably below the 5 minute limit

Benchmark script:

```bash
python benchmark_suite.py satsolver out_extended.txt small medium large special satlib_subset
python benchmark_suite.py satsolver_blaze out_blaze_extended.txt small medium large special satlib_subset
```

Measured results on the expanded 45-case suite:

| Solver | SATLIB subset total | Expanded suite total | Wall clock | Worst single case |
| --- | ---: | ---: | ---: | ---: |
| `satsolver.py` | `0.1248s` | `51.8339s` | `51.8677s` | `18.3538s` |
| `satsolver_blaze.py` | `0.1178s` | `45.1377s` | `45.1770s` | `19.8348s` |

Combined sequential wall clock for both solvers:
- `97.0447s`

This is well below the requested 5 minute cap.

Generated reports:
- `out_extended.txt`
- `out_blaze_extended.txt`

Notes:
- Both parsers were updated to stop cleanly at the SATLIB `%` terminator used in some DIMACS files.
- `satsolver_blaze.py` still has the best overall expanded-suite total.
