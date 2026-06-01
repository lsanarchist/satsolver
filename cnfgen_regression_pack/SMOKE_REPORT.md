# CNFgen regression pack smoke report

Date: 2026-06-01

Command:

```bash
PYTHONUNBUFFERED=1 python tests/scripts/run_regression_smoke.py --solver ./satsolver.py --suite cnfgen_regression_pack --timeout 60
```

Result:

- Rows: `228`
- Passed: `228`
- Failed: `0`
- SAT: `152`
- UNSAT: `76`
- Families: `30`
- Max variables: `500`
- Max clauses: `2000`
- Timeout per case: `60s`
- Max observed solver time: `35.4312s`

## Slowest Cases

| Time | Case | Status |
| ---: | --- | --- |
| `35.4312s` | `cnfgen_cases/cliquecoloring_n10_k4_c3_unsat.cnf` | UNSAT |
| `11.0688s` | `cnfgen_cases/planted_rand4cnf_v180_m1440_s3_sat.cnf` | SAT |
| `8.2687s` | `cnfgen_cases/rphp_p10_r12_h12_sat.cnf` | SAT |
| `5.4998s` | `cnfgen_cases/subsetcard_n16_unsat.cnf` | UNSAT |
| `5.4825s` | `cnfgen_cases/parity_n13_unsat.cnf` | UNSAT |
| `3.7015s` | `cnfgen_cases/rphp_p8_r14_h12_sat.cnf` | SAT |
| `3.0742s` | `cnfgen_cases/php_p16_h16_sat.cnf` | SAT |
| `2.8951s` | `cnfgen_cases/rphp_p8_r12_h10_sat.cnf` | SAT |
| `2.4534s` | `cnfgen_cases/planted_rand4cnf_v180_m1440_s1_sat.cnf` | SAT |
| `2.0102s` | `cnfgen_cases/cliquecoloring_n6_k5_c4_unsat.cnf` | UNSAT |

## Notes

- CNFgen was used only as a generation tool from a temporary external environment.
- CNFgen is not a submission-path dependency.
- The retained corpus excludes generated cases that exceeded the requested limits or timed out under the current solver.
- Every retained row has a known `SAT` or `UNSAT` status in `MANIFEST.tsv` and `manifest.csv`.
