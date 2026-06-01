# CNFgen regression pack avg-5 benchmark

Date: 2026-06-01

Command, run from `cnfgen_regression_pack/`:

```bash
python ../benchmark_suite.py satsolver /tmp/cnfgen_regression_pack_avg5.txt cnfgen_cases --bruteforce-var-limit 16 --repeat 5 --cli-script ../satsolver.py
```

Result:

- Cases: `228`
- Correct: `228`
- SAT: `152`
- UNSAT: `76`
- Errors: `0`
- Repeat count: `5`
- Representative total: `80.1684s`
- Representative average: `0.3516s`
- Representative median: `0.0319s`
- Representative max: `27.1334s`
- Measured total across all repeats: `402.7179s`
- Wall clock: `410.3343s`

## Slowest Cases

| Median Time | Case | Status | Samples |
| ---: | --- | --- | --- |
| `27.1334s` | `cliquecoloring_n10_k4_c3_unsat.cnf` | UNSAT | `[27.0083, 27.6487, 27.1334, 26.9931, 27.6356]` |
| `9.2324s` | `planted_rand4cnf_v180_m1440_s3_sat.cnf` | SAT | `[9.2324, 9.2951, 9.2263, 9.1508, 9.2494]` |
| `6.9045s` | `rphp_p10_r12_h12_sat.cnf` | SAT | `[6.9045, 6.7844, 7.1105, 6.7870, 7.2365]` |
| `4.8584s` | `parity_n13_unsat.cnf` | UNSAT | `[4.9523, 4.8411, 4.7778, 4.8900, 4.8584]` |
| `4.7310s` | `subsetcard_n16_unsat.cnf` | UNSAT | `[4.7310, 4.8927, 4.8825, 4.6814, 4.6744]` |
| `3.1422s` | `rphp_p8_r14_h12_sat.cnf` | SAT | `[3.3357, 3.1422, 3.0263, 3.0350, 3.1677]` |
| `2.7488s` | `php_p16_h16_sat.cnf` | SAT | `[2.5357, 2.7727, 2.6431, 2.7488, 2.7537]` |
| `2.5454s` | `rphp_p8_r12_h10_sat.cnf` | SAT | `[2.6083, 2.5454, 2.4843, 2.5864, 2.5421]` |
| `2.2455s` | `planted_rand4cnf_v180_m1440_s1_sat.cnf` | SAT | `[2.4497, 2.3268, 2.2455, 2.1481, 2.1789]` |
| `1.6253s` | `cliquecoloring_n6_k5_c4_unsat.cnf` | UNSAT | `[1.5677, 1.6429, 1.6253, 1.6580, 1.5681]` |

Full raw benchmark output: `/tmp/cnfgen_regression_pack_avg5.txt`.
