# Generated CNF Smoke Report

Date: 2026-06-01

Command:

```bash
python tests/scripts/run_regression_smoke.py --solver ./satsolver.py --suite tests/generated --timeout 60
```

Result:

- Return code: `0`
- Wall time: `8.3531s`
- Rows: `140`
- Passed: `140`
- Failed: `0`
- Max per-case time: `0.1281s`

## Per-Suite Summary

| Suite | Cases | Passed | Modes | Statuses | Avg Time | Max Time |
| --- | ---: | ---: | --- | --- | ---: | ---: |
| `graph_coloring` | 8 | 8 | solve: 8 | SAT: 4, UNSAT: 4 | `0.0319s` | `0.0394s` |
| `mutated_mycielski` | 11 | 11 | solve: 3, detector: 8 | SAT: 2, UNSAT: 1, OK: 8 | `0.0127s` | `0.0503s` |
| `mycielski` | 6 | 6 | solve: 6 | SAT: 3, UNSAT: 3 | `0.0365s` | `0.0489s` |
| `parser_edge_cases` | 19 | 19 | solve: 12, invalid: 7 | SAT: 9, UNSAT: 3, OK: 7 | `0.0286s` | `0.0470s` |
| `portfolio_density` | 90 | 90 | solve: 90 | SAT: 90 | `0.0664s` | `0.1281s` |
| `random_near_limit` | 6 | 6 | solve: 6 | SAT: 4, UNSAT: 2 | `0.0806s` | `0.1151s` |

## Slowest Cases

| Time | Case | Status |
| ---: | --- | --- |
| `0.1281s` | `tests/generated/portfolio_density/planted3sat_n400_d4.30_seed2.cnf` | SAT |
| `0.1166s` | `tests/generated/portfolio_density/planted3sat_n400_d4.25_seed4.cnf` | SAT |
| `0.1151s` | `tests/generated/random_near_limit/random3sat_n500_m2000_seed1.cnf` | SAT |
| `0.1132s` | `tests/generated/random_near_limit/random3sat_n500_m2000_seed2.cnf` | SAT |
| `0.1126s` | `tests/generated/portfolio_density/planted3sat_n400_d4.25_seed3.cnf` | SAT |
| `0.1084s` | `tests/generated/portfolio_density/planted3sat_n400_d4.25_seed5.cnf` | SAT |
| `0.1073s` | `tests/generated/portfolio_density/planted3sat_n400_d4.30_seed1.cnf` | SAT |
| `0.1023s` | `tests/generated/portfolio_density/planted3sat_n320_d4.30_seed4.cnf` | SAT |
| `0.0998s` | `tests/generated/portfolio_density/planted3sat_n400_d4.20_seed5.cnf` | SAT |
| `0.0998s` | `tests/generated/portfolio_density/planted3sat_n320_d4.25_seed4.cnf` | SAT |

## Notes

- All generated solver-output cases were validated through `tools/checker.py` via the smoke harness.
- Detector-only rows were used for mutated Mycielski false-positive guards.
- Invalid parser rows passed by returning a non-zero CLI exit without producing a nonempty output file.
- The generated suite is currently very fast; none of the new cases approaches the `60s` timeout.
