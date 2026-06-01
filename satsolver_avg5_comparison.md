# SAT Solver Avg5 Old Vs Current Comparison

Generated: 2026-05-31T22:49:39

This file exists because the refreshed avg5 run should have been written beside the old artifacts, not over them.

## Course CNF Tests

Old is the original 278-case avg5 artifact excluding the previous Mycielski timeout case. New is the 279-case avg5 run including that case after the structural detector.

| metric | old | new | delta | delta % |
|---|---:|---:|---:|---:|
| cases | 278 | 279 | +1 | n/a |
| solved | 278 | 279 | +1 | n/a |
| errors | 0 | 0 | +0 | n/a |
| avg5 total s | 26.7588 | 26.4364 | -0.3223 | -1.20% |
| median total s | 26.3869 | 26.2183 | -0.1686 | -0.64% |
| common-case avg5 sum s | 26.7584 | 26.3982 | -0.3602 | -1.35% |

New-only cases: `1`
- `cnf_training_complex__complex_cnf_hard__mycielski_iter4_color5_unsat.cnf`: UNSAT, avg5 `0.0374s`, median `0.0409s`

### Biggest Common-Case Avg5 Movements

| case | old avg5 s | new avg5 s | delta s | delta % | old status | new status |
|---|---:|---:|---:|---:|---|---|
| `cnf_training_complex__complex_cnf_moderate__mycielski_iter3_color4_unsat.cnf` | 0.2624 | 0.0300 | -0.2324 | -88.57% | UNSAT | UNSAT |
| `special__hard.cnf` | 2.6175 | 2.5014 | -0.1161 | -4.44% | UNSAT | UNSAT |
| `cnf_training_complex__complex_cnf_hard__planted3sat_balanced_n320_m1363_seed1.cnf` | 0.8874 | 0.8428 | -0.0446 | -5.03% | SAT | SAT |
| `cnf_training_complex__complex_cnf_moderate__ramsey_R3_4_n10_unsat.cnf` | 1.1343 | 1.0947 | -0.0396 | -3.49% | UNSAT | UNSAT |
| `medium__test_4.cnf` | 0.8882 | 0.8544 | -0.0338 | -3.81% | UNSAT | UNSAT |
| `satlib_more__uuf150-01.cnf` | 0.3745 | 0.3439 | -0.0306 | -8.17% | UNSAT | UNSAT |
| `cnf_training_complex__complex_cnf_hard__ramsey_R3_4_n11_unsat.cnf` | 1.1462 | 1.1767 | +0.0305 | +2.66% | UNSAT | UNSAT |
| `cnf_training_complex__complex_cnf_hard__planted3sat_balanced_n260_m1108_seed1.cnf` | 1.4830 | 1.5073 | +0.0243 | +1.64% | SAT | SAT |
| `large__test_6.cnf` | 3.4833 | 3.4607 | -0.0226 | -0.65% | UNSAT | UNSAT |
| `cnf_training_complex__complex_cnf_moderate__planted3sat_balanced_n200_m852_seed1.cnf` | 0.4726 | 0.4515 | -0.0211 | -4.46% | SAT | SAT |
| `cnf_training_complex__complex_cnf_moderate__ramsey_R3_4_n9_unsat.cnf` | 1.1314 | 1.1118 | -0.0196 | -1.73% | UNSAT | UNSAT |
| `cnf_training_complex__complex_cnf_moderate__planted3sat_balanced_n200_m852_seed2.cnf` | 0.9317 | 0.9474 | +0.0157 | +1.69% | SAT | SAT |
| `medium__test_3.cnf` | 0.5169 | 0.5012 | -0.0157 | -3.04% | UNSAT | UNSAT |
| `large__test_10.cnf` | 0.8546 | 0.8393 | -0.0153 | -1.79% | UNSAT | UNSAT |
| `satlib_subset__flat50-1.cnf` | 0.0340 | 0.0484 | +0.0144 | +42.35% | SAT | SAT |

## Formulae

Old is a regenerated pre-detector baseline from git HEAD. New is the current solver. This dataset does not contain the Mycielski hard case, so differences here are mostly normal benchmark noise plus any generic overhead effects.

| metric | old | new | delta | delta % |
|---|---:|---:|---:|---:|
| cases | 35 | 35 | +0 | n/a |
| solved | 35 | 35 | +0 | n/a |
| errors | 0 | 0 | +0 | n/a |
| avg5 total s | 11.1095 | 10.0218 | -1.0877 | -9.79% |
| median total s | 11.1369 | 9.9223 | -1.2146 | -10.91% |
| common-case avg5 sum s | 11.1095 | 10.0221 | -1.0874 | -9.79% |

### Biggest Common-Case Avg5 Movements

| case | old avg5 s | new avg5 s | delta s | delta % | old status | new status |
|---|---:|---:|---:|---:|---|---|
| `large/test_6.cnf` | 3.8848 | 3.5338 | -0.3510 | -9.04% | UNSAT | UNSAT |
| `large/test_10.cnf` | 1.0196 | 0.8642 | -0.1554 | -15.24% | UNSAT | UNSAT |
| `medium/test_4.cnf` | 1.0160 | 0.8800 | -0.1360 | -13.39% | UNSAT | UNSAT |
| `special/hard.cnf` | 2.7312 | 2.5972 | -0.1340 | -4.91% | UNSAT | UNSAT |
| `medium/test_3.cnf` | 0.5769 | 0.4964 | -0.0805 | -13.95% | UNSAT | UNSAT |
| `large/test_3.cnf` | 0.3427 | 0.2937 | -0.0490 | -14.30% | UNSAT | UNSAT |
| `large/test_4.cnf` | 0.2848 | 0.2498 | -0.0350 | -12.29% | UNSAT | UNSAT |
| `special/dense.cnf` | 0.1362 | 0.1214 | -0.0148 | -10.87% | UNSAT | UNSAT |
| `large/test_8.cnf` | 0.1402 | 0.1265 | -0.0137 | -9.77% | SAT | SAT |
| `large/test_5.cnf` | 0.0451 | 0.0317 | -0.0134 | -29.71% | SAT | SAT |
| `medium/test_2.cnf` | 0.0465 | 0.0340 | -0.0125 | -26.88% | UNSAT | UNSAT |
| `small/test_10.cnf` | 0.0368 | 0.0276 | -0.0092 | -25.00% | UNSAT | UNSAT |
| `large/test_7.cnf` | 0.0471 | 0.0390 | -0.0081 | -17.20% | SAT | SAT |
| `small/test_6.cnf` | 0.0357 | 0.0279 | -0.0078 | -21.85% | SAT | SAT |
| `small/test_1.cnf` | 0.0358 | 0.0281 | -0.0077 | -21.51% | SAT | SAT |

