# PORTFOLIO_MAX_DENSITY course_cnf_tests 278 repeat2 comparison

Generated: 2026-05-31T17:47:25
Dataset: `course_cnf_tests`
Repeats per case: `2`
Per-run timeout: `60s`
Densities tested: `4.2, 4.3, 4.35, 4.4`
Solver variants were created in temporary directories; the working `satsolver_core.py` was not edited by this benchmark.
Validation: `tools/checker.py`.

Excluded cases:
- `cnf_training_complex__complex_cnf_hard__mycielski_iter4_color5_unsat.cnf`

## Summary

- Cases tested per density: `278`
- Best avg-total density: `4.4`
- Benchmark wall time: `401.4459s`

| density | valid | timeouts | SAT | UNSAT | avg-total s | median-total s | delta vs 4.3 s | best-case count |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 4.2 | 278/278 | 0 | 157 | 121 | 48.3530 | 48.3530 | +18.6824 | 87 |
| 4.3 | 278/278 | 0 | 157 | 121 | 29.6705 | 29.6705 | +0.0000 | 64 |
| 4.35 | 278/278 | 0 | 157 | 121 | 29.8504 | 29.8504 | +0.1799 | 83 |
| 4.4 | 278/278 | 0 | 157 | 121 | 29.0439 | 29.0439 | -0.6266 | 93 |

## Most Sensitive Cases

| case | 4.2 avg s | 4.3 avg s | 4.35 avg s | 4.4 avg s | spread s | best density |
|---|---:|---:|---:|---:|---:|---:|
| `cnf_training_complex__complex_cnf_hard__planted3sat_balanced_n260_m1108_seed1.cnf` | 16.3197 | 1.6200 | 1.4836 | 1.4708 | 14.8489 | 4.4 |
| `cnf_training_complex__complex_cnf_hard__planted3sat_balanced_n400_m1704_seed1.cnf` | 3.8370 | 0.3273 | 0.3267 | 0.3023 | 3.5347 | 4.4 |
| `cnf_training_complex__complex_cnf_hard__planted3sat_balanced_n260_m1108_seed2.cnf` | 1.0430 | 0.7251 | 0.8094 | 0.7076 | 0.3353 | 4.4 |
| `cnf_training_complex__complex_cnf_hard__planted3sat_balanced_n320_m1363_seed2.cnf` | 0.5714 | 0.2808 | 0.2950 | 0.3798 | 0.2907 | 4.3 |
| `special__hard.cnf` | 2.8602 | 2.6849 | 2.7138 | 2.6253 | 0.2349 | 4.4 |
| `cnf_training_complex__complex_cnf_moderate__ramsey_R3_4_n9_unsat.cnf` | 1.1219 | 1.1181 | 1.3128 | 1.1270 | 0.1946 | 4.3 |
| `cnf_training_complex__complex_cnf_hard__ramsey_R3_4_n11_unsat.cnf` | 1.1507 | 1.2813 | 1.2768 | 1.1061 | 0.1752 | 4.4 |
| `cnf_training_complex__complex_cnf_moderate__ramsey_R3_4_n10_unsat.cnf` | 1.1146 | 1.1480 | 1.2624 | 1.1946 | 0.1478 | 4.2 |
| `large__test_6.cnf` | 3.5908 | 3.6308 | 3.5138 | 3.5419 | 0.1170 | 4.35 |
| `large__test_8.cnf` | 1.8050 | 1.6964 | 1.7482 | 1.7349 | 0.1086 | 4.3 |
| `cnf_training_complex__complex_cnf_moderate__planted3sat_balanced_n200_m852_seed2.cnf` | 1.0012 | 0.9430 | 0.9817 | 0.9155 | 0.0856 | 4.4 |
| `large__test_3.cnf` | 0.3763 | 0.2955 | 0.2936 | 0.2966 | 0.0827 | 4.35 |
| `large__test_10.cnf` | 0.8799 | 0.9215 | 0.9122 | 0.8501 | 0.0715 | 4.4 |
| `satlib_more__uuf150-01.cnf` | 0.3528 | 0.4129 | 0.3490 | 0.3705 | 0.0639 | 4.35 |
| `cnf_training_complex__complex_cnf_moderate__mycielski_iter3_color5_sat.cnf` | 0.0248 | 0.0408 | 0.0380 | 0.0825 | 0.0576 | 4.2 |
| `medium__test_4.cnf` | 0.8139 | 0.8450 | 0.8713 | 0.8626 | 0.0573 | 4.2 |
| `cnf_training_extra__extra_cnf__xor_parity_sat_n60_eq45_w3_005.cnf` | 0.0322 | 0.0314 | 0.0816 | 0.0274 | 0.0542 | 4.4 |
| `satlib_more__uuf125-010.cnf` | 0.1497 | 0.1544 | 0.1579 | 0.2032 | 0.0535 | 4.2 |
| `cnf_training_complex__complex_cnf_moderate__planted3sat_balanced_n200_m852_seed1.cnf` | 0.4558 | 0.4819 | 0.5093 | 0.4693 | 0.0535 | 4.2 |
| `cnf_training_complex__complex_cnf_hard__planted3sat_balanced_n320_m1363_seed1.cnf` | 0.8858 | 0.8569 | 0.8474 | 0.8704 | 0.0384 | 4.35 |
| `cnf_training_complex__complex_cnf_hard__tseitin_deg4_v64_sat.cnf` | 0.0744 | 0.0503 | 0.0506 | 0.0388 | 0.0355 | 4.4 |
| `medium__test_3.cnf` | 0.5192 | 0.5250 | 0.4925 | 0.4958 | 0.0325 | 4.35 |
| `cnf_training_complex__complex_cnf_moderate__mycielski_iter3_color4_unsat.cnf` | 0.2518 | 0.2815 | 0.2628 | 0.2501 | 0.0314 | 4.4 |
| `cnf_training_complex__complex_cnf_moderate__xor_sparse_sat_n96_eq125_w3_seed2.cnf` | 0.0390 | 0.0636 | 0.0433 | 0.0335 | 0.0301 | 4.4 |
| `cnf_training_extra__extra_cnf__nqueens_7x7_sat.cnf` | 0.0377 | 0.0504 | 0.0239 | 0.0372 | 0.0265 | 4.35 |

## Slowest Cases Per Density

### Density 4.2

| case | result | avg s | median s | min s | max s | runs s | status |
|---|---|---:|---:|---:|---:|---|---|
| `cnf_training_complex__complex_cnf_hard__planted3sat_balanced_n260_m1108_seed1.cnf` | SAT | 16.3197 | 16.3197 | 16.3089 | 16.3306 | `[16.3306, 16.3089]` | OK,OK |
| `cnf_training_complex__complex_cnf_hard__planted3sat_balanced_n400_m1704_seed1.cnf` | SAT | 3.8370 | 3.8370 | 3.6426 | 4.0314 | `[3.6426, 4.0314]` | OK,OK |
| `large__test_6.cnf` | UNSAT | 3.5908 | 3.5908 | 3.3610 | 3.8206 | `[3.3610, 3.8206]` | OK,OK |
| `special__hard.cnf` | UNSAT | 2.8602 | 2.8602 | 2.7529 | 2.9676 | `[2.9676, 2.7529]` | OK,OK |
| `large__test_8.cnf` | SAT | 1.8050 | 1.8050 | 1.7270 | 1.8830 | `[1.8830, 1.7270]` | OK,OK |
| `cnf_training_complex__complex_cnf_hard__ramsey_R3_4_n11_unsat.cnf` | UNSAT | 1.1507 | 1.1507 | 1.1408 | 1.1606 | `[1.1606, 1.1408]` | OK,OK |
| `cnf_training_complex__complex_cnf_moderate__ramsey_R3_4_n9_unsat.cnf` | UNSAT | 1.1219 | 1.1219 | 1.1060 | 1.1378 | `[1.1060, 1.1378]` | OK,OK |
| `cnf_training_complex__complex_cnf_moderate__ramsey_R3_4_n10_unsat.cnf` | UNSAT | 1.1146 | 1.1146 | 1.1079 | 1.1212 | `[1.1079, 1.1212]` | OK,OK |
| `cnf_training_complex__complex_cnf_hard__planted3sat_balanced_n260_m1108_seed2.cnf` | SAT | 1.0430 | 1.0430 | 1.0162 | 1.0697 | `[1.0697, 1.0162]` | OK,OK |
| `cnf_training_complex__complex_cnf_moderate__planted3sat_balanced_n200_m852_seed2.cnf` | SAT | 1.0012 | 1.0012 | 0.9240 | 1.0784 | `[0.9240, 1.0784]` | OK,OK |
| `cnf_training_complex__complex_cnf_hard__planted3sat_balanced_n320_m1363_seed1.cnf` | SAT | 0.8858 | 0.8858 | 0.8508 | 0.9208 | `[0.8508, 0.9208]` | OK,OK |
| `large__test_10.cnf` | UNSAT | 0.8799 | 0.8799 | 0.8443 | 0.9155 | `[0.8443, 0.9155]` | OK,OK |
| `medium__test_4.cnf` | UNSAT | 0.8139 | 0.8139 | 0.8103 | 0.8175 | `[0.8103, 0.8175]` | OK,OK |
| `cnf_training_complex__complex_cnf_hard__planted3sat_balanced_n320_m1363_seed2.cnf` | SAT | 0.5714 | 0.5714 | 0.5714 | 0.5715 | `[0.5715, 0.5714]` | OK,OK |
| `medium__test_3.cnf` | UNSAT | 0.5192 | 0.5192 | 0.4737 | 0.5648 | `[0.4737, 0.5648]` | OK,OK |

### Density 4.3

| case | result | avg s | median s | min s | max s | runs s | status |
|---|---|---:|---:|---:|---:|---|---|
| `large__test_6.cnf` | UNSAT | 3.6308 | 3.6308 | 3.5635 | 3.6982 | `[3.5635, 3.6982]` | OK,OK |
| `special__hard.cnf` | UNSAT | 2.6849 | 2.6849 | 2.5961 | 2.7736 | `[2.7736, 2.5961]` | OK,OK |
| `large__test_8.cnf` | SAT | 1.6964 | 1.6964 | 1.6900 | 1.7028 | `[1.7028, 1.6900]` | OK,OK |
| `cnf_training_complex__complex_cnf_hard__planted3sat_balanced_n260_m1108_seed1.cnf` | SAT | 1.6200 | 1.6200 | 1.6018 | 1.6381 | `[1.6381, 1.6018]` | OK,OK |
| `cnf_training_complex__complex_cnf_hard__ramsey_R3_4_n11_unsat.cnf` | UNSAT | 1.2813 | 1.2813 | 1.1877 | 1.3749 | `[1.1877, 1.3749]` | OK,OK |
| `cnf_training_complex__complex_cnf_moderate__ramsey_R3_4_n10_unsat.cnf` | UNSAT | 1.1480 | 1.1480 | 1.1117 | 1.1843 | `[1.1117, 1.1843]` | OK,OK |
| `cnf_training_complex__complex_cnf_moderate__ramsey_R3_4_n9_unsat.cnf` | UNSAT | 1.1181 | 1.1181 | 1.1074 | 1.1289 | `[1.1074, 1.1289]` | OK,OK |
| `cnf_training_complex__complex_cnf_moderate__planted3sat_balanced_n200_m852_seed2.cnf` | SAT | 0.9430 | 0.9430 | 0.9279 | 0.9582 | `[0.9582, 0.9279]` | OK,OK |
| `large__test_10.cnf` | UNSAT | 0.9215 | 0.9215 | 0.8605 | 0.9826 | `[0.9826, 0.8605]` | OK,OK |
| `cnf_training_complex__complex_cnf_hard__planted3sat_balanced_n320_m1363_seed1.cnf` | SAT | 0.8569 | 0.8569 | 0.8455 | 0.8683 | `[0.8683, 0.8455]` | OK,OK |
| `medium__test_4.cnf` | UNSAT | 0.8450 | 0.8450 | 0.8405 | 0.8494 | `[0.8494, 0.8405]` | OK,OK |
| `cnf_training_complex__complex_cnf_hard__planted3sat_balanced_n260_m1108_seed2.cnf` | SAT | 0.7251 | 0.7251 | 0.7244 | 0.7258 | `[0.7244, 0.7258]` | OK,OK |
| `medium__test_3.cnf` | UNSAT | 0.5250 | 0.5250 | 0.5162 | 0.5338 | `[0.5338, 0.5162]` | OK,OK |
| `cnf_training_complex__complex_cnf_moderate__planted3sat_balanced_n200_m852_seed1.cnf` | SAT | 0.4819 | 0.4819 | 0.4759 | 0.4879 | `[0.4759, 0.4879]` | OK,OK |
| `satlib_more__uuf150-01.cnf` | UNSAT | 0.4129 | 0.4129 | 0.3448 | 0.4809 | `[0.4809, 0.3448]` | OK,OK |

### Density 4.35

| case | result | avg s | median s | min s | max s | runs s | status |
|---|---|---:|---:|---:|---:|---|---|
| `large__test_6.cnf` | UNSAT | 3.5138 | 3.5138 | 3.4506 | 3.5771 | `[3.5771, 3.4506]` | OK,OK |
| `special__hard.cnf` | UNSAT | 2.7138 | 2.7138 | 2.6473 | 2.7802 | `[2.6473, 2.7802]` | OK,OK |
| `large__test_8.cnf` | SAT | 1.7482 | 1.7482 | 1.7034 | 1.7929 | `[1.7929, 1.7034]` | OK,OK |
| `cnf_training_complex__complex_cnf_hard__planted3sat_balanced_n260_m1108_seed1.cnf` | SAT | 1.4836 | 1.4836 | 1.4529 | 1.5143 | `[1.5143, 1.4529]` | OK,OK |
| `cnf_training_complex__complex_cnf_moderate__ramsey_R3_4_n9_unsat.cnf` | UNSAT | 1.3128 | 1.3128 | 1.2325 | 1.3931 | `[1.2325, 1.3931]` | OK,OK |
| `cnf_training_complex__complex_cnf_hard__ramsey_R3_4_n11_unsat.cnf` | UNSAT | 1.2768 | 1.2768 | 1.2182 | 1.3354 | `[1.2182, 1.3354]` | OK,OK |
| `cnf_training_complex__complex_cnf_moderate__ramsey_R3_4_n10_unsat.cnf` | UNSAT | 1.2624 | 1.2624 | 1.2418 | 1.2829 | `[1.2418, 1.2829]` | OK,OK |
| `cnf_training_complex__complex_cnf_moderate__planted3sat_balanced_n200_m852_seed2.cnf` | SAT | 0.9817 | 0.9817 | 0.9797 | 0.9837 | `[0.9797, 0.9837]` | OK,OK |
| `large__test_10.cnf` | UNSAT | 0.9122 | 0.9122 | 0.8305 | 0.9939 | `[0.9939, 0.8305]` | OK,OK |
| `medium__test_4.cnf` | UNSAT | 0.8713 | 0.8713 | 0.8692 | 0.8733 | `[0.8733, 0.8692]` | OK,OK |
| `cnf_training_complex__complex_cnf_hard__planted3sat_balanced_n320_m1363_seed1.cnf` | SAT | 0.8474 | 0.8474 | 0.8356 | 0.8592 | `[0.8592, 0.8356]` | OK,OK |
| `cnf_training_complex__complex_cnf_hard__planted3sat_balanced_n260_m1108_seed2.cnf` | SAT | 0.8094 | 0.8094 | 0.6959 | 0.9229 | `[0.6959, 0.9229]` | OK,OK |
| `cnf_training_complex__complex_cnf_moderate__planted3sat_balanced_n200_m852_seed1.cnf` | SAT | 0.5093 | 0.5093 | 0.5054 | 0.5133 | `[0.5054, 0.5133]` | OK,OK |
| `medium__test_3.cnf` | UNSAT | 0.4925 | 0.4925 | 0.4760 | 0.5090 | `[0.4760, 0.5090]` | OK,OK |
| `satlib_more__uuf150-01.cnf` | UNSAT | 0.3490 | 0.3490 | 0.3332 | 0.3647 | `[0.3332, 0.3647]` | OK,OK |

### Density 4.4

| case | result | avg s | median s | min s | max s | runs s | status |
|---|---|---:|---:|---:|---:|---|---|
| `large__test_6.cnf` | UNSAT | 3.5419 | 3.5419 | 3.3978 | 3.6859 | `[3.6859, 3.3978]` | OK,OK |
| `special__hard.cnf` | UNSAT | 2.6253 | 2.6253 | 2.6003 | 2.6504 | `[2.6504, 2.6003]` | OK,OK |
| `large__test_8.cnf` | SAT | 1.7349 | 1.7349 | 1.6300 | 1.8398 | `[1.6300, 1.8398]` | OK,OK |
| `cnf_training_complex__complex_cnf_hard__planted3sat_balanced_n260_m1108_seed1.cnf` | SAT | 1.4708 | 1.4708 | 1.4185 | 1.5231 | `[1.4185, 1.5231]` | OK,OK |
| `cnf_training_complex__complex_cnf_moderate__ramsey_R3_4_n10_unsat.cnf` | UNSAT | 1.1946 | 1.1946 | 1.1067 | 1.2824 | `[1.2824, 1.1067]` | OK,OK |
| `cnf_training_complex__complex_cnf_moderate__ramsey_R3_4_n9_unsat.cnf` | UNSAT | 1.1270 | 1.1270 | 1.0985 | 1.1555 | `[1.0985, 1.1555]` | OK,OK |
| `cnf_training_complex__complex_cnf_hard__ramsey_R3_4_n11_unsat.cnf` | UNSAT | 1.1061 | 1.1061 | 1.0969 | 1.1154 | `[1.1154, 1.0969]` | OK,OK |
| `cnf_training_complex__complex_cnf_moderate__planted3sat_balanced_n200_m852_seed2.cnf` | SAT | 0.9155 | 0.9155 | 0.8945 | 0.9365 | `[0.9365, 0.8945]` | OK,OK |
| `cnf_training_complex__complex_cnf_hard__planted3sat_balanced_n320_m1363_seed1.cnf` | SAT | 0.8704 | 0.8704 | 0.8421 | 0.8987 | `[0.8421, 0.8987]` | OK,OK |
| `medium__test_4.cnf` | UNSAT | 0.8626 | 0.8626 | 0.8461 | 0.8791 | `[0.8461, 0.8791]` | OK,OK |
| `large__test_10.cnf` | UNSAT | 0.8501 | 0.8501 | 0.8352 | 0.8649 | `[0.8352, 0.8649]` | OK,OK |
| `cnf_training_complex__complex_cnf_hard__planted3sat_balanced_n260_m1108_seed2.cnf` | SAT | 0.7076 | 0.7076 | 0.6658 | 0.7495 | `[0.6658, 0.7495]` | OK,OK |
| `medium__test_3.cnf` | UNSAT | 0.4958 | 0.4958 | 0.4929 | 0.4987 | `[0.4987, 0.4929]` | OK,OK |
| `cnf_training_complex__complex_cnf_moderate__planted3sat_balanced_n200_m852_seed1.cnf` | SAT | 0.4693 | 0.4693 | 0.4636 | 0.4751 | `[0.4751, 0.4636]` | OK,OK |
| `cnf_training_complex__complex_cnf_hard__planted3sat_balanced_n320_m1363_seed2.cnf` | SAT | 0.3798 | 0.3798 | 0.2813 | 0.4783 | `[0.2813, 0.4783]` | OK,OK |

## All Cases

| case | 4.2 result | 4.2 avg s | 4.3 result | 4.3 avg s | 4.35 result | 4.35 avg s | 4.4 result | 4.4 avg s | best density | spread s |
|---|---|---:|---|---:|---|---:|---|---:|---:|---:|
| `cnf_training_complex__complex_cnf_hard__planted3sat_balanced_n260_m1108_seed1.cnf` | SAT | 16.3197 | SAT | 1.6200 | SAT | 1.4836 | SAT | 1.4708 | 4.4 | 14.8489 |
| `cnf_training_complex__complex_cnf_hard__planted3sat_balanced_n260_m1108_seed2.cnf` | SAT | 1.0430 | SAT | 0.7251 | SAT | 0.8094 | SAT | 0.7076 | 4.4 | 0.3353 |
| `cnf_training_complex__complex_cnf_hard__planted3sat_balanced_n320_m1363_seed1.cnf` | SAT | 0.8858 | SAT | 0.8569 | SAT | 0.8474 | SAT | 0.8704 | 4.35 | 0.0384 |
| `cnf_training_complex__complex_cnf_hard__planted3sat_balanced_n320_m1363_seed2.cnf` | SAT | 0.5714 | SAT | 0.2808 | SAT | 0.2950 | SAT | 0.3798 | 4.3 | 0.2907 |
| `cnf_training_complex__complex_cnf_hard__planted3sat_balanced_n400_m1704_seed1.cnf` | SAT | 3.8370 | SAT | 0.3273 | SAT | 0.3267 | SAT | 0.3023 | 4.4 | 3.5347 |
| `cnf_training_complex__complex_cnf_hard__ramsey_R3_4_n11_unsat.cnf` | UNSAT | 1.1507 | UNSAT | 1.2813 | UNSAT | 1.2768 | UNSAT | 1.1061 | 4.4 | 0.1752 |
| `cnf_training_complex__complex_cnf_hard__tseitin_deg3_v100_sat.cnf` | SAT | 0.0434 | SAT | 0.0351 | SAT | 0.0358 | SAT | 0.0295 | 4.4 | 0.0139 |
| `cnf_training_complex__complex_cnf_hard__tseitin_deg3_v100_unsat.cnf` | UNSAT | 0.0251 | UNSAT | 0.0383 | UNSAT | 0.0307 | UNSAT | 0.0315 | 4.2 | 0.0131 |
| `cnf_training_complex__complex_cnf_hard__tseitin_deg3_v120_sat.cnf` | SAT | 0.0275 | SAT | 0.0414 | SAT | 0.0434 | SAT | 0.0411 | 4.2 | 0.0159 |
| `cnf_training_complex__complex_cnf_hard__tseitin_deg3_v120_unsat.cnf` | UNSAT | 0.0242 | UNSAT | 0.0262 | UNSAT | 0.0401 | UNSAT | 0.0369 | 4.2 | 0.0159 |
| `cnf_training_complex__complex_cnf_hard__tseitin_deg3_v160_sat.cnf` | SAT | 0.0500 | SAT | 0.0554 | SAT | 0.0502 | SAT | 0.0550 | 4.2 | 0.0053 |
| `cnf_training_complex__complex_cnf_hard__tseitin_deg3_v160_unsat.cnf` | UNSAT | 0.0326 | UNSAT | 0.0366 | UNSAT | 0.0340 | UNSAT | 0.0347 | 4.2 | 0.0040 |
| `cnf_training_complex__complex_cnf_hard__tseitin_deg4_v64_sat.cnf` | SAT | 0.0744 | SAT | 0.0503 | SAT | 0.0506 | SAT | 0.0388 | 4.4 | 0.0355 |
| `cnf_training_complex__complex_cnf_hard__tseitin_deg4_v64_unsat.cnf` | UNSAT | 0.0246 | UNSAT | 0.0406 | UNSAT | 0.0267 | UNSAT | 0.0242 | 4.4 | 0.0164 |
| `cnf_training_complex__complex_cnf_hard__tseitin_deg4_v96_sat.cnf` | SAT | 0.0357 | SAT | 0.0387 | SAT | 0.0392 | SAT | 0.0488 | 4.2 | 0.0131 |
| `cnf_training_complex__complex_cnf_hard__tseitin_deg4_v96_unsat.cnf` | UNSAT | 0.0332 | UNSAT | 0.0394 | UNSAT | 0.0351 | UNSAT | 0.0276 | 4.4 | 0.0119 |
| `cnf_training_complex__complex_cnf_hard__vdw_2color_k4_n45_unsat.cnf` | UNSAT | 0.0560 | UNSAT | 0.0603 | UNSAT | 0.0638 | UNSAT | 0.0564 | 4.2 | 0.0078 |
| `cnf_training_complex__complex_cnf_hard__vdw_2color_k4_n60_unsat.cnf` | UNSAT | 0.0625 | UNSAT | 0.0610 | UNSAT | 0.0603 | UNSAT | 0.0555 | 4.4 | 0.0070 |
| `cnf_training_complex__complex_cnf_hard__xor_sparse_unsat_n100_eq135_w3-4_seed4.cnf` | UNSAT | 0.0276 | UNSAT | 0.0376 | UNSAT | 0.0335 | UNSAT | 0.0284 | 4.2 | 0.0100 |
| `cnf_training_complex__complex_cnf_hard__xor_sparse_unsat_n140_eq190_w3-4_seed5.cnf` | UNSAT | 0.0384 | UNSAT | 0.0332 | UNSAT | 0.0428 | UNSAT | 0.0301 | 4.4 | 0.0128 |
| `cnf_training_complex__complex_cnf_hard__xor_sparse_unsat_n180_eq250_w3-4_seed6.cnf` | UNSAT | 0.0342 | UNSAT | 0.0352 | UNSAT | 0.0357 | UNSAT | 0.0281 | 4.4 | 0.0076 |
| `cnf_training_complex__complex_cnf_moderate__mycielski_iter2_color3_unsat.cnf` | UNSAT | 0.0447 | UNSAT | 0.0285 | UNSAT | 0.0260 | UNSAT | 0.0299 | 4.35 | 0.0187 |
| `cnf_training_complex__complex_cnf_moderate__mycielski_iter2_color4_sat.cnf` | SAT | 0.0277 | SAT | 0.0361 | SAT | 0.0387 | SAT | 0.0293 | 4.2 | 0.0110 |
| `cnf_training_complex__complex_cnf_moderate__mycielski_iter3_color4_unsat.cnf` | UNSAT | 0.2518 | UNSAT | 0.2815 | UNSAT | 0.2628 | UNSAT | 0.2501 | 4.4 | 0.0314 |
| `cnf_training_complex__complex_cnf_moderate__mycielski_iter3_color5_sat.cnf` | SAT | 0.0248 | SAT | 0.0408 | SAT | 0.0380 | SAT | 0.0825 | 4.2 | 0.0576 |
| `cnf_training_complex__complex_cnf_moderate__ordering_no_minimum_n10.cnf` | UNSAT | 0.0450 | UNSAT | 0.0502 | UNSAT | 0.0451 | UNSAT | 0.0534 | 4.2 | 0.0084 |
| `cnf_training_complex__complex_cnf_moderate__ordering_no_minimum_n12.cnf` | UNSAT | 0.0664 | UNSAT | 0.0660 | UNSAT | 0.0807 | UNSAT | 0.0638 | 4.4 | 0.0169 |
| `cnf_training_complex__complex_cnf_moderate__ordering_no_minimum_n8.cnf` | UNSAT | 0.0304 | UNSAT | 0.0552 | UNSAT | 0.0427 | UNSAT | 0.0377 | 4.2 | 0.0247 |
| `cnf_training_complex__complex_cnf_moderate__orthogonal_latin_squares_order3_sat.cnf` | SAT | 0.0448 | SAT | 0.0469 | SAT | 0.0446 | SAT | 0.0467 | 4.35 | 0.0023 |
| `cnf_training_complex__complex_cnf_moderate__pigeonhole_php_11_into_10.cnf` | UNSAT | 0.0335 | UNSAT | 0.0313 | UNSAT | 0.0333 | UNSAT | 0.0336 | 4.3 | 0.0024 |
| `cnf_training_complex__complex_cnf_moderate__pigeonhole_php_13_into_12.cnf` | UNSAT | 0.0265 | UNSAT | 0.0317 | UNSAT | 0.0366 | UNSAT | 0.0439 | 4.2 | 0.0174 |
| `cnf_training_complex__complex_cnf_moderate__pigeonhole_php_9_into_8.cnf` | UNSAT | 0.0313 | UNSAT | 0.0253 | UNSAT | 0.0298 | UNSAT | 0.0314 | 4.3 | 0.0061 |
| `cnf_training_complex__complex_cnf_moderate__planted3sat_balanced_n120_m511_seed1.cnf` | SAT | 0.0273 | SAT | 0.0364 | SAT | 0.0310 | SAT | 0.0319 | 4.2 | 0.0090 |
| `cnf_training_complex__complex_cnf_moderate__planted3sat_balanced_n120_m511_seed2.cnf` | SAT | 0.0296 | SAT | 0.0368 | SAT | 0.0420 | SAT | 0.0466 | 4.2 | 0.0170 |
| `cnf_training_complex__complex_cnf_moderate__planted3sat_balanced_n160_m682_seed1.cnf` | SAT | 0.0533 | SAT | 0.0356 | SAT | 0.0384 | SAT | 0.0410 | 4.3 | 0.0177 |
| `cnf_training_complex__complex_cnf_moderate__planted3sat_balanced_n160_m682_seed2.cnf` | SAT | 0.0402 | SAT | 0.0465 | SAT | 0.0461 | SAT | 0.0473 | 4.2 | 0.0071 |
| `cnf_training_complex__complex_cnf_moderate__planted3sat_balanced_n200_m852_seed1.cnf` | SAT | 0.4558 | SAT | 0.4819 | SAT | 0.5093 | SAT | 0.4693 | 4.2 | 0.0535 |
| `cnf_training_complex__complex_cnf_moderate__planted3sat_balanced_n200_m852_seed2.cnf` | SAT | 1.0012 | SAT | 0.9430 | SAT | 0.9817 | SAT | 0.9155 | 4.4 | 0.0856 |
| `cnf_training_complex__complex_cnf_moderate__ramsey_R3_3_n6_unsat.cnf` | UNSAT | 0.0316 | UNSAT | 0.0429 | UNSAT | 0.0326 | UNSAT | 0.0334 | 4.2 | 0.0113 |
| `cnf_training_complex__complex_cnf_moderate__ramsey_R3_3_n7_unsat.cnf` | UNSAT | 0.0264 | UNSAT | 0.0361 | UNSAT | 0.0266 | UNSAT | 0.0338 | 4.2 | 0.0097 |
| `cnf_training_complex__complex_cnf_moderate__ramsey_R3_3_n8_unsat.cnf` | UNSAT | 0.0313 | UNSAT | 0.0323 | UNSAT | 0.0398 | UNSAT | 0.0324 | 4.2 | 0.0085 |
| `cnf_training_complex__complex_cnf_moderate__ramsey_R3_4_n10_unsat.cnf` | UNSAT | 1.1146 | UNSAT | 1.1480 | UNSAT | 1.2624 | UNSAT | 1.1946 | 4.2 | 0.1478 |
| `cnf_training_complex__complex_cnf_moderate__ramsey_R3_4_n9_unsat.cnf` | UNSAT | 1.1219 | UNSAT | 1.1181 | UNSAT | 1.3128 | UNSAT | 1.1270 | 4.3 | 0.1946 |
| `cnf_training_complex__complex_cnf_moderate__tseitin_deg3_v40_sat.cnf` | SAT | 0.0462 | SAT | 0.0323 | SAT | 0.0325 | SAT | 0.0381 | 4.3 | 0.0139 |
| `cnf_training_complex__complex_cnf_moderate__tseitin_deg3_v40_unsat.cnf` | UNSAT | 0.0320 | UNSAT | 0.0245 | UNSAT | 0.0315 | UNSAT | 0.0243 | 4.4 | 0.0077 |
| `cnf_training_complex__complex_cnf_moderate__tseitin_deg3_v60_sat.cnf` | SAT | 0.0364 | SAT | 0.0328 | SAT | 0.0348 | SAT | 0.0271 | 4.4 | 0.0093 |
| `cnf_training_complex__complex_cnf_moderate__tseitin_deg3_v60_unsat.cnf` | UNSAT | 0.0293 | UNSAT | 0.0351 | UNSAT | 0.0289 | UNSAT | 0.0231 | 4.4 | 0.0119 |
| `cnf_training_complex__complex_cnf_moderate__tseitin_deg3_v80_sat.cnf` | SAT | 0.0288 | SAT | 0.0335 | SAT | 0.0463 | SAT | 0.0344 | 4.2 | 0.0174 |
| `cnf_training_complex__complex_cnf_moderate__tseitin_deg3_v80_unsat.cnf` | UNSAT | 0.0342 | UNSAT | 0.0415 | UNSAT | 0.0270 | UNSAT | 0.0274 | 4.35 | 0.0145 |
| `cnf_training_complex__complex_cnf_moderate__vdw_2color_k3_n16_unsat.cnf` | UNSAT | 0.0246 | UNSAT | 0.0426 | UNSAT | 0.0403 | UNSAT | 0.0324 | 4.2 | 0.0181 |
| `cnf_training_complex__complex_cnf_moderate__vdw_2color_k3_n9_unsat.cnf` | UNSAT | 0.0350 | UNSAT | 0.0305 | UNSAT | 0.0296 | UNSAT | 0.0291 | 4.4 | 0.0058 |
| `cnf_training_complex__complex_cnf_moderate__vdw_2color_k4_n35_unsat.cnf` | UNSAT | 0.0586 | UNSAT | 0.0496 | UNSAT | 0.0662 | UNSAT | 0.0472 | 4.4 | 0.0191 |
| `cnf_training_complex__complex_cnf_moderate__xor_sparse_sat_n128_eq165_w3-4_seed3.cnf` | SAT | 0.2482 | SAT | 0.2369 | SAT | 0.2467 | SAT | 0.2432 | 4.3 | 0.0113 |
| `cnf_training_complex__complex_cnf_moderate__xor_sparse_sat_n64_eq82_w3_seed1.cnf` | SAT | 0.0279 | SAT | 0.0307 | SAT | 0.0291 | SAT | 0.0284 | 4.2 | 0.0027 |
| `cnf_training_complex__complex_cnf_moderate__xor_sparse_sat_n96_eq125_w3_seed2.cnf` | SAT | 0.0390 | SAT | 0.0636 | SAT | 0.0433 | SAT | 0.0335 | 4.4 | 0.0301 |
| `cnf_training_complex__complex_cnf_moderate__xor_sparse_unsat_n48_eq62_w3_seed1.cnf` | UNSAT | 0.0294 | UNSAT | 0.0381 | UNSAT | 0.0428 | UNSAT | 0.0256 | 4.4 | 0.0171 |
| `cnf_training_complex__complex_cnf_moderate__xor_sparse_unsat_n64_eq86_w3_seed2.cnf` | UNSAT | 0.0315 | UNSAT | 0.0341 | UNSAT | 0.0336 | UNSAT | 0.0374 | 4.2 | 0.0059 |
| `cnf_training_complex__complex_cnf_moderate__xor_sparse_unsat_n80_eq108_w3-4_seed3.cnf` | UNSAT | 0.0373 | UNSAT | 0.0328 | UNSAT | 0.0333 | UNSAT | 0.0384 | 4.3 | 0.0056 |
| `cnf_training_complex__complex_cnf_stress__tseitin_deg3_v240_unsat.cnf` | UNSAT | 0.0281 | UNSAT | 0.0312 | UNSAT | 0.0316 | UNSAT | 0.0400 | 4.2 | 0.0119 |
| `cnf_training_complex__complex_cnf_stress__tseitin_deg4_v160_unsat.cnf` | UNSAT | 0.0363 | UNSAT | 0.0340 | UNSAT | 0.0392 | UNSAT | 0.0378 | 4.3 | 0.0051 |
| `cnf_training_complex__complex_cnf_stress__xor_sparse_unsat_n240_eq330_w3-4_seed1.cnf` | UNSAT | 0.0358 | UNSAT | 0.0356 | UNSAT | 0.0321 | UNSAT | 0.0317 | 4.4 | 0.0041 |
| `cnf_training_extra__extra_cnf__cardinality_exactly_one_sat_g10_s5_004.cnf` | SAT | 0.0347 | SAT | 0.0263 | SAT | 0.0284 | SAT | 0.0315 | 4.3 | 0.0083 |
| `cnf_training_extra__extra_cnf__cardinality_exactly_one_sat_g12_s6_005.cnf` | SAT | 0.0400 | SAT | 0.0268 | SAT | 0.0331 | SAT | 0.0380 | 4.3 | 0.0132 |
| `cnf_training_extra__extra_cnf__cardinality_exactly_one_sat_g16_s4_006.cnf` | SAT | 0.0338 | SAT | 0.0236 | SAT | 0.0310 | SAT | 0.0334 | 4.3 | 0.0102 |
| `cnf_training_extra__extra_cnf__cardinality_exactly_one_sat_g4_s4_001.cnf` | SAT | 0.0228 | SAT | 0.0384 | SAT | 0.0353 | SAT | 0.0286 | 4.2 | 0.0157 |
| `cnf_training_extra__extra_cnf__cardinality_exactly_one_sat_g5_s5_002.cnf` | SAT | 0.0340 | SAT | 0.0303 | SAT | 0.0396 | SAT | 0.0329 | 4.3 | 0.0093 |
| `cnf_training_extra__extra_cnf__cardinality_exactly_one_sat_g8_s4_003.cnf` | SAT | 0.0264 | SAT | 0.0345 | SAT | 0.0297 | SAT | 0.0306 | 4.2 | 0.0081 |
| `cnf_training_extra__extra_cnf__cardinality_exactly_one_unsat_g10_s6_005.cnf` | UNSAT | 0.0239 | UNSAT | 0.0365 | UNSAT | 0.0332 | UNSAT | 0.0295 | 4.2 | 0.0126 |
| `cnf_training_extra__extra_cnf__cardinality_exactly_one_unsat_g12_s4_006.cnf` | UNSAT | 0.0228 | UNSAT | 0.0336 | UNSAT | 0.0337 | UNSAT | 0.0267 | 4.2 | 0.0109 |
| `cnf_training_extra__extra_cnf__cardinality_exactly_one_unsat_g3_s4_001.cnf` | UNSAT | 0.0233 | UNSAT | 0.0325 | UNSAT | 0.0304 | UNSAT | 0.0264 | 4.2 | 0.0092 |
| `cnf_training_extra__extra_cnf__cardinality_exactly_one_unsat_g4_s5_002.cnf` | UNSAT | 0.0236 | UNSAT | 0.0335 | UNSAT | 0.0259 | UNSAT | 0.0340 | 4.2 | 0.0104 |
| `cnf_training_extra__extra_cnf__cardinality_exactly_one_unsat_g6_s4_003.cnf` | UNSAT | 0.0285 | UNSAT | 0.0292 | UNSAT | 0.0359 | UNSAT | 0.0297 | 4.2 | 0.0074 |
| `cnf_training_extra__extra_cnf__cardinality_exactly_one_unsat_g8_s5_004.cnf` | UNSAT | 0.0368 | UNSAT | 0.0322 | UNSAT | 0.0409 | UNSAT | 0.0278 | 4.4 | 0.0131 |
| `cnf_training_extra__extra_cnf__equivalence_chain_len10_sat.cnf` | SAT | 0.0270 | SAT | 0.0226 | SAT | 0.0290 | SAT | 0.0351 | 4.3 | 0.0125 |
| `cnf_training_extra__extra_cnf__equivalence_chain_len10_unsat.cnf` | UNSAT | 0.0396 | UNSAT | 0.0360 | UNSAT | 0.0300 | UNSAT | 0.0264 | 4.4 | 0.0132 |
| `cnf_training_extra__extra_cnf__equivalence_chain_len120_sat.cnf` | SAT | 0.0345 | SAT | 0.0347 | SAT | 0.0314 | SAT | 0.0293 | 4.4 | 0.0054 |
| `cnf_training_extra__extra_cnf__equivalence_chain_len120_unsat.cnf` | UNSAT | 0.0322 | UNSAT | 0.0301 | UNSAT | 0.0291 | UNSAT | 0.0223 | 4.4 | 0.0099 |
| `cnf_training_extra__extra_cnf__equivalence_chain_len20_sat.cnf` | SAT | 0.0294 | SAT | 0.0327 | SAT | 0.0263 | SAT | 0.0235 | 4.4 | 0.0093 |
| `cnf_training_extra__extra_cnf__equivalence_chain_len20_unsat.cnf` | UNSAT | 0.0287 | UNSAT | 0.0289 | UNSAT | 0.0424 | UNSAT | 0.0313 | 4.2 | 0.0137 |
| `cnf_training_extra__extra_cnf__equivalence_chain_len40_sat.cnf` | SAT | 0.0347 | SAT | 0.0328 | SAT | 0.0390 | SAT | 0.0285 | 4.4 | 0.0105 |
| `cnf_training_extra__extra_cnf__equivalence_chain_len40_unsat.cnf` | UNSAT | 0.0279 | UNSAT | 0.0219 | UNSAT | 0.0250 | UNSAT | 0.0360 | 4.3 | 0.0141 |
| `cnf_training_extra__extra_cnf__equivalence_chain_len80_sat.cnf` | SAT | 0.0314 | SAT | 0.0240 | SAT | 0.0333 | SAT | 0.0307 | 4.3 | 0.0092 |
| `cnf_training_extra__extra_cnf__equivalence_chain_len80_unsat.cnf` | UNSAT | 0.0339 | UNSAT | 0.0322 | UNSAT | 0.0281 | UNSAT | 0.0308 | 4.35 | 0.0057 |
| `cnf_training_extra__extra_cnf__exact_random3sat_sat_n10_m49_008.cnf` | SAT | 0.0330 | SAT | 0.0243 | SAT | 0.0400 | SAT | 0.0306 | 4.3 | 0.0157 |
| `cnf_training_extra__extra_cnf__exact_random3sat_sat_n11_m40_017.cnf` | SAT | 0.0309 | SAT | 0.0271 | SAT | 0.0399 | SAT | 0.0271 | 4.4 | 0.0128 |
| `cnf_training_extra__extra_cnf__exact_random3sat_sat_n11_m46_001.cnf` | SAT | 0.0355 | SAT | 0.0252 | SAT | 0.0356 | SAT | 0.0287 | 4.3 | 0.0103 |
| `cnf_training_extra__extra_cnf__exact_random3sat_sat_n12_m43_012.cnf` | SAT | 0.0317 | SAT | 0.0221 | SAT | 0.0320 | SAT | 0.0280 | 4.3 | 0.0099 |
| `cnf_training_extra__extra_cnf__exact_random3sat_sat_n12_m47_006.cnf` | SAT | 0.0236 | SAT | 0.0272 | SAT | 0.0290 | SAT | 0.0222 | 4.4 | 0.0069 |
| `cnf_training_extra__extra_cnf__exact_random3sat_sat_n12_m47_013.cnf` | SAT | 0.0279 | SAT | 0.0424 | SAT | 0.0303 | SAT | 0.0309 | 4.2 | 0.0145 |
| `cnf_training_extra__extra_cnf__exact_random3sat_sat_n13_m47_011.cnf` | SAT | 0.0241 | SAT | 0.0263 | SAT | 0.0371 | SAT | 0.0213 | 4.4 | 0.0157 |
| `cnf_training_extra__extra_cnf__exact_random3sat_sat_n13_m64_004.cnf` | SAT | 0.0226 | SAT | 0.0362 | SAT | 0.0394 | SAT | 0.0323 | 4.2 | 0.0168 |
| `cnf_training_extra__extra_cnf__exact_random3sat_sat_n14_m50_015.cnf` | SAT | 0.0315 | SAT | 0.0269 | SAT | 0.0223 | SAT | 0.0392 | 4.35 | 0.0169 |
| `cnf_training_extra__extra_cnf__exact_random3sat_sat_n15_m68_014.cnf` | SAT | 0.0389 | SAT | 0.0362 | SAT | 0.0252 | SAT | 0.0294 | 4.35 | 0.0138 |
| `cnf_training_extra__extra_cnf__exact_random3sat_sat_n16_m62_016.cnf` | SAT | 0.0335 | SAT | 0.0270 | SAT | 0.0383 | SAT | 0.0333 | 4.3 | 0.0112 |
| `cnf_training_extra__extra_cnf__exact_random3sat_sat_n16_m72_003.cnf` | SAT | 0.0408 | SAT | 0.0248 | SAT | 0.0465 | SAT | 0.0347 | 4.3 | 0.0216 |
| `cnf_training_extra__extra_cnf__exact_random3sat_sat_n8_m31_007.cnf` | SAT | 0.0226 | SAT | 0.0243 | SAT | 0.0358 | SAT | 0.0311 | 4.2 | 0.0132 |
| `cnf_training_extra__extra_cnf__exact_random3sat_sat_n8_m31_009.cnf` | SAT | 0.0273 | SAT | 0.0295 | SAT | 0.0301 | SAT | 0.0325 | 4.2 | 0.0052 |
| `cnf_training_extra__extra_cnf__exact_random3sat_sat_n8_m36_002.cnf` | SAT | 0.0222 | SAT | 0.0269 | SAT | 0.0292 | SAT | 0.0277 | 4.2 | 0.0070 |
| `cnf_training_extra__extra_cnf__exact_random3sat_sat_n8_m36_005.cnf` | SAT | 0.0382 | SAT | 0.0291 | SAT | 0.0320 | SAT | 0.0214 | 4.4 | 0.0168 |
| `cnf_training_extra__extra_cnf__exact_random3sat_sat_n9_m32_018.cnf` | SAT | 0.0368 | SAT | 0.0323 | SAT | 0.0290 | SAT | 0.0378 | 4.35 | 0.0088 |
| `cnf_training_extra__extra_cnf__exact_random3sat_sat_n9_m38_010.cnf` | SAT | 0.0306 | SAT | 0.0395 | SAT | 0.0298 | SAT | 0.0361 | 4.35 | 0.0097 |
| `cnf_training_extra__extra_cnf__exact_random3sat_unsat_n10_m49_015.cnf` | UNSAT | 0.0381 | UNSAT | 0.0332 | UNSAT | 0.0315 | UNSAT | 0.0365 | 4.35 | 0.0066 |
| `cnf_training_extra__extra_cnf__exact_random3sat_unsat_n11_m54_012.cnf` | UNSAT | 0.0309 | UNSAT | 0.0321 | UNSAT | 0.0289 | UNSAT | 0.0345 | 4.35 | 0.0056 |
| `cnf_training_extra__extra_cnf__exact_random3sat_unsat_n12_m64_007.cnf` | UNSAT | 0.0242 | UNSAT | 0.0223 | UNSAT | 0.0279 | UNSAT | 0.0241 | 4.3 | 0.0056 |
| `cnf_training_extra__extra_cnf__exact_random3sat_unsat_n12_m64_013.cnf` | UNSAT | 0.0227 | UNSAT | 0.0247 | UNSAT | 0.0386 | UNSAT | 0.0309 | 4.2 | 0.0160 |
| `cnf_training_extra__extra_cnf__exact_random3sat_unsat_n13_m69_006.cnf` | UNSAT | 0.0302 | UNSAT | 0.0238 | UNSAT | 0.0281 | UNSAT | 0.0346 | 4.3 | 0.0108 |
| `cnf_training_extra__extra_cnf__exact_random3sat_unsat_n13_m69_010.cnf` | UNSAT | 0.0332 | UNSAT | 0.0302 | UNSAT | 0.0390 | UNSAT | 0.0356 | 4.3 | 0.0088 |
| `cnf_training_extra__extra_cnf__exact_random3sat_unsat_n14_m74_017.cnf` | UNSAT | 0.0385 | UNSAT | 0.0295 | UNSAT | 0.0338 | UNSAT | 0.0322 | 4.3 | 0.0090 |
| `cnf_training_extra__extra_cnf__exact_random3sat_unsat_n15_m68_011.cnf` | UNSAT | 0.0311 | UNSAT | 0.0298 | UNSAT | 0.0238 | UNSAT | 0.0313 | 4.35 | 0.0075 |
| `cnf_training_extra__extra_cnf__exact_random3sat_unsat_n15_m68_018.cnf` | UNSAT | 0.0305 | UNSAT | 0.0357 | UNSAT | 0.0323 | UNSAT | 0.0365 | 4.2 | 0.0060 |
| `cnf_training_extra__extra_cnf__exact_random3sat_unsat_n15_m80_014.cnf` | UNSAT | 0.0342 | UNSAT | 0.0328 | UNSAT | 0.0381 | UNSAT | 0.0275 | 4.4 | 0.0106 |
| `cnf_training_extra__extra_cnf__exact_random3sat_unsat_n16_m78_005.cnf` | UNSAT | 0.0357 | UNSAT | 0.0302 | UNSAT | 0.0251 | UNSAT | 0.0287 | 4.35 | 0.0106 |
| `cnf_training_extra__extra_cnf__exact_random3sat_unsat_n16_m78_008.cnf` | UNSAT | 0.0364 | UNSAT | 0.0263 | UNSAT | 0.0245 | UNSAT | 0.0284 | 4.35 | 0.0118 |
| `cnf_training_extra__extra_cnf__exact_random3sat_unsat_n16_m85_002.cnf` | UNSAT | 0.0240 | UNSAT | 0.0256 | UNSAT | 0.0228 | UNSAT | 0.0390 | 4.35 | 0.0162 |
| `cnf_training_extra__extra_cnf__exact_random3sat_unsat_n16_m85_003.cnf` | UNSAT | 0.0364 | UNSAT | 0.0330 | UNSAT | 0.0270 | UNSAT | 0.0353 | 4.35 | 0.0094 |
| `cnf_training_extra__extra_cnf__exact_random3sat_unsat_n8_m31_016.cnf` | UNSAT | 0.0434 | UNSAT | 0.0342 | UNSAT | 0.0256 | UNSAT | 0.0313 | 4.35 | 0.0179 |
| `cnf_training_extra__extra_cnf__exact_random3sat_unsat_n8_m34_009.cnf` | UNSAT | 0.0269 | UNSAT | 0.0255 | UNSAT | 0.0231 | UNSAT | 0.0365 | 4.35 | 0.0134 |
| `cnf_training_extra__extra_cnf__exact_random3sat_unsat_n9_m38_004.cnf` | UNSAT | 0.0298 | UNSAT | 0.0433 | UNSAT | 0.0343 | UNSAT | 0.0320 | 4.2 | 0.0135 |
| `cnf_training_extra__extra_cnf__exact_random3sat_unsat_n9_m44_001.cnf` | UNSAT | 0.0317 | UNSAT | 0.0264 | UNSAT | 0.0271 | UNSAT | 0.0380 | 4.3 | 0.0116 |
| `cnf_training_extra__extra_cnf__graphcolor_k3_complete_K4_unsat.cnf` | UNSAT | 0.0255 | UNSAT | 0.0319 | UNSAT | 0.0257 | UNSAT | 0.0316 | 4.2 | 0.0064 |
| `cnf_training_extra__extra_cnf__graphcolor_k3_complete_K5_unsat.cnf` | UNSAT | 0.0307 | UNSAT | 0.0327 | UNSAT | 0.0341 | UNSAT | 0.0304 | 4.4 | 0.0037 |
| `cnf_training_extra__extra_cnf__graphcolor_k3_complete_K6_unsat.cnf` | UNSAT | 0.0302 | UNSAT | 0.0346 | UNSAT | 0.0454 | UNSAT | 0.0268 | 4.4 | 0.0186 |
| `cnf_training_extra__extra_cnf__graphcolor_k3_planted_v12_e26_001.cnf` | SAT | 0.0297 | SAT | 0.0357 | SAT | 0.0275 | SAT | 0.0325 | 4.35 | 0.0082 |
| `cnf_training_extra__extra_cnf__graphcolor_k3_planted_v16_e35_002.cnf` | SAT | 0.0385 | SAT | 0.0401 | SAT | 0.0360 | SAT | 0.0324 | 4.4 | 0.0077 |
| `cnf_training_extra__extra_cnf__graphcolor_k3_planted_v20_e44_003.cnf` | SAT | 0.0285 | SAT | 0.0255 | SAT | 0.0318 | SAT | 0.0350 | 4.3 | 0.0095 |
| `cnf_training_extra__extra_cnf__graphcolor_k3_planted_v24_e53_004.cnf` | SAT | 0.0363 | SAT | 0.0292 | SAT | 0.0320 | SAT | 0.0451 | 4.3 | 0.0160 |
| `cnf_training_extra__extra_cnf__graphcolor_k3_planted_v30_e66_005.cnf` | SAT | 0.0250 | SAT | 0.0296 | SAT | 0.0379 | SAT | 0.0262 | 4.2 | 0.0128 |
| `cnf_training_extra__extra_cnf__graphcolor_k3_planted_v36_e79_006.cnf` | SAT | 0.0308 | SAT | 0.0396 | SAT | 0.0281 | SAT | 0.0327 | 4.35 | 0.0114 |
| `cnf_training_extra__extra_cnf__graphcolor_k3_planted_v42_e92_007.cnf` | SAT | 0.0351 | SAT | 0.0306 | SAT | 0.0330 | SAT | 0.0335 | 4.3 | 0.0046 |
| `cnf_training_extra__extra_cnf__graphcolor_k3_planted_v50_e110_008.cnf` | SAT | 0.0429 | SAT | 0.0329 | SAT | 0.0309 | SAT | 0.0342 | 4.35 | 0.0120 |
| `cnf_training_extra__extra_cnf__graphcolor_k3_planted_v60_e132_009.cnf` | SAT | 0.0347 | SAT | 0.0245 | SAT | 0.0340 | SAT | 0.0317 | 4.3 | 0.0102 |
| `cnf_training_extra__extra_cnf__graphcolor_k3_planted_v72_e158_010.cnf` | SAT | 0.0338 | SAT | 0.0343 | SAT | 0.0244 | SAT | 0.0405 | 4.35 | 0.0161 |
| `cnf_training_extra__extra_cnf__horn_chain_len12_sat.cnf` | SAT | 0.0262 | SAT | 0.0309 | SAT | 0.0239 | SAT | 0.0295 | 4.35 | 0.0070 |
| `cnf_training_extra__extra_cnf__horn_chain_len12_unsat.cnf` | UNSAT | 0.0359 | UNSAT | 0.0282 | UNSAT | 0.0310 | UNSAT | 0.0343 | 4.3 | 0.0077 |
| `cnf_training_extra__extra_cnf__horn_chain_len16_sat.cnf` | SAT | 0.0301 | SAT | 0.0276 | SAT | 0.0373 | SAT | 0.0234 | 4.4 | 0.0139 |
| `cnf_training_extra__extra_cnf__horn_chain_len16_unsat.cnf` | UNSAT | 0.0250 | UNSAT | 0.0286 | UNSAT | 0.0250 | UNSAT | 0.0299 | 4.2 | 0.0049 |
| `cnf_training_extra__extra_cnf__horn_chain_len24_sat.cnf` | SAT | 0.0350 | SAT | 0.0284 | SAT | 0.0242 | SAT | 0.0233 | 4.4 | 0.0117 |
| `cnf_training_extra__extra_cnf__horn_chain_len24_unsat.cnf` | UNSAT | 0.0309 | UNSAT | 0.0348 | UNSAT | 0.0354 | UNSAT | 0.0288 | 4.4 | 0.0065 |
| `cnf_training_extra__extra_cnf__horn_chain_len32_sat.cnf` | SAT | 0.0307 | SAT | 0.0298 | SAT | 0.0225 | SAT | 0.0291 | 4.35 | 0.0082 |
| `cnf_training_extra__extra_cnf__horn_chain_len32_unsat.cnf` | UNSAT | 0.0276 | UNSAT | 0.0288 | UNSAT | 0.0291 | UNSAT | 0.0410 | 4.2 | 0.0135 |
| `cnf_training_extra__extra_cnf__horn_chain_len48_sat.cnf` | SAT | 0.0377 | SAT | 0.0350 | SAT | 0.0300 | SAT | 0.0208 | 4.4 | 0.0169 |
| `cnf_training_extra__extra_cnf__horn_chain_len48_unsat.cnf` | UNSAT | 0.0315 | UNSAT | 0.0359 | UNSAT | 0.0350 | UNSAT | 0.0232 | 4.4 | 0.0127 |
| `cnf_training_extra__extra_cnf__horn_chain_len64_sat.cnf` | SAT | 0.0442 | SAT | 0.0340 | SAT | 0.0301 | SAT | 0.0340 | 4.35 | 0.0142 |
| `cnf_training_extra__extra_cnf__horn_chain_len64_unsat.cnf` | UNSAT | 0.0298 | UNSAT | 0.0376 | UNSAT | 0.0339 | UNSAT | 0.0263 | 4.4 | 0.0113 |
| `cnf_training_extra__extra_cnf__horn_chain_len8_sat.cnf` | SAT | 0.0312 | SAT | 0.0255 | SAT | 0.0317 | SAT | 0.0355 | 4.3 | 0.0100 |
| `cnf_training_extra__extra_cnf__horn_chain_len8_unsat.cnf` | UNSAT | 0.0332 | UNSAT | 0.0274 | UNSAT | 0.0222 | UNSAT | 0.0447 | 4.35 | 0.0226 |
| `cnf_training_extra__extra_cnf__nqueens_2x2_unsat.cnf` | UNSAT | 0.0310 | UNSAT | 0.0406 | UNSAT | 0.0359 | UNSAT | 0.0263 | 4.4 | 0.0142 |
| `cnf_training_extra__extra_cnf__nqueens_3x3_unsat.cnf` | UNSAT | 0.0267 | UNSAT | 0.0291 | UNSAT | 0.0250 | UNSAT | 0.0362 | 4.35 | 0.0111 |
| `cnf_training_extra__extra_cnf__nqueens_4x4_sat.cnf` | SAT | 0.0324 | SAT | 0.0336 | SAT | 0.0235 | SAT | 0.0248 | 4.35 | 0.0101 |
| `cnf_training_extra__extra_cnf__nqueens_5x5_sat.cnf` | SAT | 0.0218 | SAT | 0.0226 | SAT | 0.0246 | SAT | 0.0241 | 4.2 | 0.0028 |
| `cnf_training_extra__extra_cnf__nqueens_6x6_sat.cnf` | SAT | 0.0290 | SAT | 0.0393 | SAT | 0.0361 | SAT | 0.0317 | 4.2 | 0.0103 |
| `cnf_training_extra__extra_cnf__nqueens_7x7_sat.cnf` | SAT | 0.0377 | SAT | 0.0504 | SAT | 0.0239 | SAT | 0.0372 | 4.35 | 0.0265 |
| `cnf_training_extra__extra_cnf__nqueens_8x8_sat.cnf` | SAT | 0.0408 | SAT | 0.0437 | SAT | 0.0375 | SAT | 0.0351 | 4.4 | 0.0086 |
| `cnf_training_extra__extra_cnf__nqueens_9x9_sat.cnf` | SAT | 0.0355 | SAT | 0.0391 | SAT | 0.0334 | SAT | 0.0407 | 4.35 | 0.0072 |
| `cnf_training_extra__extra_cnf__pigeonhole_php_10_into_9.cnf` | UNSAT | 0.0412 | UNSAT | 0.0310 | UNSAT | 0.0302 | UNSAT | 0.0355 | 4.35 | 0.0110 |
| `cnf_training_extra__extra_cnf__pigeonhole_php_4_into_3.cnf` | UNSAT | 0.0394 | UNSAT | 0.0268 | UNSAT | 0.0242 | UNSAT | 0.0378 | 4.35 | 0.0152 |
| `cnf_training_extra__extra_cnf__pigeonhole_php_5_into_4.cnf` | UNSAT | 0.0329 | UNSAT | 0.0385 | UNSAT | 0.0328 | UNSAT | 0.0284 | 4.4 | 0.0101 |
| `cnf_training_extra__extra_cnf__pigeonhole_php_6_into_5.cnf` | UNSAT | 0.0251 | UNSAT | 0.0397 | UNSAT | 0.0330 | UNSAT | 0.0293 | 4.2 | 0.0146 |
| `cnf_training_extra__extra_cnf__pigeonhole_php_7_into_6.cnf` | UNSAT | 0.0278 | UNSAT | 0.0336 | UNSAT | 0.0309 | UNSAT | 0.0254 | 4.4 | 0.0083 |
| `cnf_training_extra__extra_cnf__pigeonhole_php_8_into_7.cnf` | UNSAT | 0.0343 | UNSAT | 0.0242 | UNSAT | 0.0224 | UNSAT | 0.0306 | 4.35 | 0.0120 |
| `cnf_training_extra__extra_cnf__pigeonhole_php_9_into_8.cnf` | UNSAT | 0.0351 | UNSAT | 0.0338 | UNSAT | 0.0242 | UNSAT | 0.0248 | 4.35 | 0.0110 |
| `cnf_training_extra__extra_cnf__planted3sat_n20_m85_001.cnf` | SAT | 0.0320 | SAT | 0.0345 | SAT | 0.0353 | SAT | 0.0301 | 4.4 | 0.0052 |
| `cnf_training_extra__extra_cnf__planted3sat_n20_m85_002.cnf` | SAT | 0.0253 | SAT | 0.0293 | SAT | 0.0375 | SAT | 0.0252 | 4.4 | 0.0123 |
| `cnf_training_extra__extra_cnf__planted3sat_n20_m85_003.cnf` | SAT | 0.0237 | SAT | 0.0412 | SAT | 0.0245 | SAT | 0.0335 | 4.2 | 0.0175 |
| `cnf_training_extra__extra_cnf__planted3sat_n20_m85_004.cnf` | SAT | 0.0403 | SAT | 0.0308 | SAT | 0.0220 | SAT | 0.0364 | 4.35 | 0.0183 |
| `cnf_training_extra__extra_cnf__planted3sat_n20_m85_005.cnf` | SAT | 0.0320 | SAT | 0.0335 | SAT | 0.0348 | SAT | 0.0286 | 4.4 | 0.0063 |
| `cnf_training_extra__extra_cnf__planted3sat_n20_m85_006.cnf` | SAT | 0.0247 | SAT | 0.0377 | SAT | 0.0428 | SAT | 0.0349 | 4.2 | 0.0181 |
| `cnf_training_extra__extra_cnf__planted3sat_n20_m85_007.cnf` | SAT | 0.0269 | SAT | 0.0319 | SAT | 0.0356 | SAT | 0.0224 | 4.4 | 0.0133 |
| `cnf_training_extra__extra_cnf__planted3sat_n20_m85_008.cnf` | SAT | 0.0291 | SAT | 0.0254 | SAT | 0.0442 | SAT | 0.0211 | 4.4 | 0.0232 |
| `cnf_training_extra__extra_cnf__planted3sat_n20_m85_009.cnf` | SAT | 0.0318 | SAT | 0.0296 | SAT | 0.0267 | SAT | 0.0267 | 4.35 | 0.0052 |
| `cnf_training_extra__extra_cnf__planted3sat_n20_m85_010.cnf` | SAT | 0.0319 | SAT | 0.0323 | SAT | 0.0337 | SAT | 0.0437 | 4.2 | 0.0118 |
| `cnf_training_extra__extra_cnf__planted3sat_n30_m128_001.cnf` | SAT | 0.0366 | SAT | 0.0298 | SAT | 0.0273 | SAT | 0.0307 | 4.35 | 0.0093 |
| `cnf_training_extra__extra_cnf__planted3sat_n30_m128_002.cnf` | SAT | 0.0344 | SAT | 0.0327 | SAT | 0.0381 | SAT | 0.0290 | 4.4 | 0.0091 |
| `cnf_training_extra__extra_cnf__planted3sat_n30_m128_003.cnf` | SAT | 0.0352 | SAT | 0.0302 | SAT | 0.0396 | SAT | 0.0327 | 4.3 | 0.0093 |
| `cnf_training_extra__extra_cnf__planted3sat_n30_m128_004.cnf` | SAT | 0.0377 | SAT | 0.0268 | SAT | 0.0365 | SAT | 0.0253 | 4.4 | 0.0124 |
| `cnf_training_extra__extra_cnf__planted3sat_n30_m128_005.cnf` | SAT | 0.0386 | SAT | 0.0259 | SAT | 0.0257 | SAT | 0.0334 | 4.35 | 0.0129 |
| `cnf_training_extra__extra_cnf__planted3sat_n30_m128_006.cnf` | SAT | 0.0304 | SAT | 0.0381 | SAT | 0.0247 | SAT | 0.0325 | 4.35 | 0.0134 |
| `cnf_training_extra__extra_cnf__planted3sat_n30_m128_007.cnf` | SAT | 0.0344 | SAT | 0.0270 | SAT | 0.0297 | SAT | 0.0305 | 4.3 | 0.0074 |
| `cnf_training_extra__extra_cnf__planted3sat_n30_m128_008.cnf` | SAT | 0.0363 | SAT | 0.0265 | SAT | 0.0221 | SAT | 0.0359 | 4.35 | 0.0141 |
| `cnf_training_extra__extra_cnf__planted3sat_n30_m128_009.cnf` | SAT | 0.0323 | SAT | 0.0273 | SAT | 0.0291 | SAT | 0.0315 | 4.3 | 0.0050 |
| `cnf_training_extra__extra_cnf__planted3sat_n30_m128_010.cnf` | SAT | 0.0285 | SAT | 0.0400 | SAT | 0.0253 | SAT | 0.0353 | 4.35 | 0.0147 |
| `cnf_training_extra__extra_cnf__planted3sat_n40_m170_001.cnf` | SAT | 0.0274 | SAT | 0.0273 | SAT | 0.0326 | SAT | 0.0222 | 4.4 | 0.0103 |
| `cnf_training_extra__extra_cnf__planted3sat_n40_m170_002.cnf` | SAT | 0.0269 | SAT | 0.0336 | SAT | 0.0315 | SAT | 0.0301 | 4.2 | 0.0067 |
| `cnf_training_extra__extra_cnf__planted3sat_n40_m170_003.cnf` | SAT | 0.0245 | SAT | 0.0311 | SAT | 0.0268 | SAT | 0.0368 | 4.2 | 0.0124 |
| `cnf_training_extra__extra_cnf__planted3sat_n40_m170_004.cnf` | SAT | 0.0246 | SAT | 0.0343 | SAT | 0.0313 | SAT | 0.0371 | 4.2 | 0.0125 |
| `cnf_training_extra__extra_cnf__planted3sat_n40_m170_005.cnf` | SAT | 0.0395 | SAT | 0.0326 | SAT | 0.0313 | SAT | 0.0290 | 4.4 | 0.0106 |
| `cnf_training_extra__extra_cnf__planted3sat_n40_m170_006.cnf` | SAT | 0.0253 | SAT | 0.0306 | SAT | 0.0302 | SAT | 0.0344 | 4.2 | 0.0092 |
| `cnf_training_extra__extra_cnf__planted3sat_n40_m170_007.cnf` | SAT | 0.0324 | SAT | 0.0404 | SAT | 0.0332 | SAT | 0.0302 | 4.4 | 0.0101 |
| `cnf_training_extra__extra_cnf__planted3sat_n40_m170_008.cnf` | SAT | 0.0465 | SAT | 0.0342 | SAT | 0.0303 | SAT | 0.0308 | 4.35 | 0.0162 |
| `cnf_training_extra__extra_cnf__planted3sat_n40_m170_009.cnf` | SAT | 0.0304 | SAT | 0.0241 | SAT | 0.0321 | SAT | 0.0354 | 4.3 | 0.0113 |
| `cnf_training_extra__extra_cnf__planted3sat_n40_m170_010.cnf` | SAT | 0.0383 | SAT | 0.0330 | SAT | 0.0331 | SAT | 0.0349 | 4.3 | 0.0053 |
| `cnf_training_extra__extra_cnf__planted3sat_n60_m255_001.cnf` | SAT | 0.0332 | SAT | 0.0274 | SAT | 0.0268 | SAT | 0.0330 | 4.35 | 0.0064 |
| `cnf_training_extra__extra_cnf__planted3sat_n60_m255_002.cnf` | SAT | 0.0386 | SAT | 0.0416 | SAT | 0.0310 | SAT | 0.0275 | 4.4 | 0.0140 |
| `cnf_training_extra__extra_cnf__planted3sat_n60_m255_003.cnf` | SAT | 0.0330 | SAT | 0.0393 | SAT | 0.0246 | SAT | 0.0338 | 4.35 | 0.0148 |
| `cnf_training_extra__extra_cnf__planted3sat_n60_m255_004.cnf` | SAT | 0.0345 | SAT | 0.0401 | SAT | 0.0397 | SAT | 0.0339 | 4.4 | 0.0062 |
| `cnf_training_extra__extra_cnf__planted3sat_n60_m255_005.cnf` | SAT | 0.0373 | SAT | 0.0362 | SAT | 0.0349 | SAT | 0.0260 | 4.4 | 0.0113 |
| `cnf_training_extra__extra_cnf__planted3sat_n60_m255_006.cnf` | SAT | 0.0310 | SAT | 0.0341 | SAT | 0.0314 | SAT | 0.0348 | 4.2 | 0.0038 |
| `cnf_training_extra__extra_cnf__planted3sat_n60_m255_007.cnf` | SAT | 0.0357 | SAT | 0.0326 | SAT | 0.0389 | SAT | 0.0340 | 4.3 | 0.0064 |
| `cnf_training_extra__extra_cnf__planted3sat_n60_m255_008.cnf` | SAT | 0.0300 | SAT | 0.0336 | SAT | 0.0314 | SAT | 0.0410 | 4.2 | 0.0110 |
| `cnf_training_extra__extra_cnf__planted3sat_n80_m340_001.cnf` | SAT | 0.0400 | SAT | 0.0366 | SAT | 0.0446 | SAT | 0.0425 | 4.3 | 0.0081 |
| `cnf_training_extra__extra_cnf__planted3sat_n80_m340_002.cnf` | SAT | 0.0301 | SAT | 0.0299 | SAT | 0.0284 | SAT | 0.0323 | 4.35 | 0.0038 |
| `cnf_training_extra__extra_cnf__planted3sat_n80_m340_003.cnf` | SAT | 0.0320 | SAT | 0.0292 | SAT | 0.0333 | SAT | 0.0268 | 4.4 | 0.0066 |
| `cnf_training_extra__extra_cnf__planted3sat_n80_m340_004.cnf` | SAT | 0.0369 | SAT | 0.0367 | SAT | 0.0377 | SAT | 0.0300 | 4.4 | 0.0077 |
| `cnf_training_extra__extra_cnf__planted3sat_n80_m340_005.cnf` | SAT | 0.0341 | SAT | 0.0300 | SAT | 0.0274 | SAT | 0.0393 | 4.35 | 0.0119 |
| `cnf_training_extra__extra_cnf__planted3sat_n80_m340_006.cnf` | SAT | 0.0255 | SAT | 0.0332 | SAT | 0.0270 | SAT | 0.0391 | 4.2 | 0.0136 |
| `cnf_training_extra__extra_cnf__xor_parity_sat_n18_eq18_w3_001.cnf` | SAT | 0.0240 | SAT | 0.0293 | SAT | 0.0344 | SAT | 0.0256 | 4.2 | 0.0103 |
| `cnf_training_extra__extra_cnf__xor_parity_sat_n24_eq24_w3_002.cnf` | SAT | 0.0265 | SAT | 0.0344 | SAT | 0.0231 | SAT | 0.0349 | 4.35 | 0.0118 |
| `cnf_training_extra__extra_cnf__xor_parity_sat_n30_eq30_w3_003.cnf` | SAT | 0.0246 | SAT | 0.0304 | SAT | 0.0379 | SAT | 0.0380 | 4.2 | 0.0134 |
| `cnf_training_extra__extra_cnf__xor_parity_sat_n32_eq20_w4_007.cnf` | SAT | 0.0356 | SAT | 0.0433 | SAT | 0.0301 | SAT | 0.0297 | 4.4 | 0.0136 |
| `cnf_training_extra__extra_cnf__xor_parity_sat_n40_eq35_w3_004.cnf` | SAT | 0.0331 | SAT | 0.0243 | SAT | 0.0275 | SAT | 0.0325 | 4.3 | 0.0088 |
| `cnf_training_extra__extra_cnf__xor_parity_sat_n48_eq28_w4_008.cnf` | SAT | 0.0310 | SAT | 0.0339 | SAT | 0.0325 | SAT | 0.0329 | 4.2 | 0.0029 |
| `cnf_training_extra__extra_cnf__xor_parity_sat_n60_eq45_w3_005.cnf` | SAT | 0.0322 | SAT | 0.0314 | SAT | 0.0816 | SAT | 0.0274 | 4.4 | 0.0542 |
| `cnf_training_extra__extra_cnf__xor_parity_sat_n80_eq55_w3_006.cnf` | SAT | 0.0348 | SAT | 0.0288 | SAT | 0.0397 | SAT | 0.0287 | 4.4 | 0.0111 |
| `cnf_training_extra__extra_cnf__xor_parity_unsat_n18_eq12_w3_001.cnf` | UNSAT | 0.0314 | UNSAT | 0.0321 | UNSAT | 0.0376 | UNSAT | 0.0337 | 4.2 | 0.0062 |
| `cnf_training_extra__extra_cnf__xor_parity_unsat_n24_eq16_w3_002.cnf` | UNSAT | 0.0245 | UNSAT | 0.0330 | UNSAT | 0.0345 | UNSAT | 0.0316 | 4.2 | 0.0099 |
| `cnf_training_extra__extra_cnf__xor_parity_unsat_n30_eq20_w3_003.cnf` | UNSAT | 0.0275 | UNSAT | 0.0221 | UNSAT | 0.0348 | UNSAT | 0.0461 | 4.3 | 0.0240 |
| `cnf_training_extra__extra_cnf__xor_parity_unsat_n32_eq18_w4_006.cnf` | UNSAT | 0.0285 | UNSAT | 0.0309 | UNSAT | 0.0316 | UNSAT | 0.0373 | 4.2 | 0.0088 |
| `cnf_training_extra__extra_cnf__xor_parity_unsat_n40_eq24_w3_004.cnf` | UNSAT | 0.0241 | UNSAT | 0.0376 | UNSAT | 0.0394 | UNSAT | 0.0305 | 4.2 | 0.0153 |
| `cnf_training_extra__extra_cnf__xor_parity_unsat_n60_eq32_w3_005.cnf` | UNSAT | 0.0393 | UNSAT | 0.0334 | UNSAT | 0.0306 | UNSAT | 0.0370 | 4.35 | 0.0087 |
| `large__test_1.cnf` | SAT | 0.0350 | SAT | 0.0457 | SAT | 0.0332 | SAT | 0.0482 | 4.35 | 0.0150 |
| `large__test_10.cnf` | UNSAT | 0.8799 | UNSAT | 0.9215 | UNSAT | 0.9122 | UNSAT | 0.8501 | 4.4 | 0.0715 |
| `large__test_2.cnf` | SAT | 0.0337 | SAT | 0.0373 | SAT | 0.0347 | SAT | 0.0365 | 4.2 | 0.0036 |
| `large__test_3.cnf` | UNSAT | 0.3763 | UNSAT | 0.2955 | UNSAT | 0.2936 | UNSAT | 0.2966 | 4.35 | 0.0827 |
| `large__test_4.cnf` | UNSAT | 0.2413 | UNSAT | 0.2440 | UNSAT | 0.2402 | UNSAT | 0.2344 | 4.4 | 0.0097 |
| `large__test_5.cnf` | SAT | 0.0384 | SAT | 0.0395 | SAT | 0.0302 | SAT | 0.0402 | 4.35 | 0.0100 |
| `large__test_6.cnf` | UNSAT | 3.5908 | UNSAT | 3.6308 | UNSAT | 3.5138 | UNSAT | 3.5419 | 4.35 | 0.1170 |
| `large__test_7.cnf` | SAT | 0.0499 | SAT | 0.0417 | SAT | 0.0359 | SAT | 0.0444 | 4.35 | 0.0140 |
| `large__test_8.cnf` | SAT | 1.8050 | SAT | 1.6964 | SAT | 1.7482 | SAT | 1.7349 | 4.3 | 0.1086 |
| `large__test_9.cnf` | SAT | 0.0424 | SAT | 0.0584 | SAT | 0.0484 | SAT | 0.0456 | 4.2 | 0.0160 |
| `medium__test_1.cnf` | UNSAT | 0.0326 | UNSAT | 0.0389 | UNSAT | 0.0322 | UNSAT | 0.0430 | 4.35 | 0.0108 |
| `medium__test_10.cnf` | UNSAT | 0.0259 | UNSAT | 0.0345 | UNSAT | 0.0361 | UNSAT | 0.0386 | 4.2 | 0.0128 |
| `medium__test_2.cnf` | UNSAT | 0.0391 | UNSAT | 0.0411 | UNSAT | 0.0403 | UNSAT | 0.0356 | 4.4 | 0.0055 |
| `medium__test_3.cnf` | UNSAT | 0.5192 | UNSAT | 0.5250 | UNSAT | 0.4925 | UNSAT | 0.4958 | 4.35 | 0.0325 |
| `medium__test_4.cnf` | UNSAT | 0.8139 | UNSAT | 0.8450 | UNSAT | 0.8713 | UNSAT | 0.8626 | 4.2 | 0.0573 |
| `medium__test_5.cnf` | UNSAT | 0.0374 | UNSAT | 0.0450 | UNSAT | 0.0348 | UNSAT | 0.0346 | 4.4 | 0.0104 |
| `medium__test_6.cnf` | UNSAT | 0.0399 | UNSAT | 0.0452 | UNSAT | 0.0340 | UNSAT | 0.0342 | 4.35 | 0.0112 |
| `medium__test_7.cnf` | UNSAT | 0.0316 | UNSAT | 0.0415 | UNSAT | 0.0352 | UNSAT | 0.0329 | 4.2 | 0.0099 |
| `medium__test_8.cnf` | SAT | 0.0333 | SAT | 0.0347 | SAT | 0.0344 | SAT | 0.0333 | 4.2 | 0.0015 |
| `medium__test_9.cnf` | SAT | 0.0345 | SAT | 0.0440 | SAT | 0.0309 | SAT | 0.0296 | 4.4 | 0.0144 |
| `satlib_more__aim-100-1_6-no-1.cnf` | UNSAT | 0.0344 | UNSAT | 0.0321 | UNSAT | 0.0528 | UNSAT | 0.0271 | 4.4 | 0.0256 |
| `satlib_more__aim-100-1_6-no-2.cnf` | UNSAT | 0.0301 | UNSAT | 0.0303 | UNSAT | 0.0368 | UNSAT | 0.0288 | 4.4 | 0.0080 |
| `satlib_more__aim-100-1_6-yes1-1.cnf` | SAT | 0.0326 | SAT | 0.0362 | SAT | 0.0351 | SAT | 0.0401 | 4.2 | 0.0074 |
| `satlib_more__aim-100-1_6-yes1-2.cnf` | SAT | 0.0353 | SAT | 0.0343 | SAT | 0.0329 | SAT | 0.0350 | 4.35 | 0.0024 |
| `satlib_more__flat75-1.cnf` | SAT | 0.0298 | SAT | 0.0387 | SAT | 0.0411 | SAT | 0.0329 | 4.2 | 0.0113 |
| `satlib_more__flat75-10.cnf` | SAT | 0.0368 | SAT | 0.0420 | SAT | 0.0388 | SAT | 0.0385 | 4.2 | 0.0052 |
| `satlib_more__jnh1.cnf` | SAT | 0.0439 | SAT | 0.0431 | SAT | 0.0410 | SAT | 0.0400 | 4.4 | 0.0039 |
| `satlib_more__jnh10.cnf` | UNSAT | 0.0459 | UNSAT | 0.0369 | UNSAT | 0.0403 | UNSAT | 0.0423 | 4.3 | 0.0090 |
| `satlib_more__uf125-01.cnf` | SAT | 0.0424 | SAT | 0.0305 | SAT | 0.0440 | SAT | 0.0395 | 4.3 | 0.0135 |
| `satlib_more__uf125-010.cnf` | SAT | 0.0877 | SAT | 0.0864 | SAT | 0.0859 | SAT | 0.0892 | 4.35 | 0.0033 |
| `satlib_more__uf150-01.cnf` | SAT | 0.0529 | SAT | 0.0510 | SAT | 0.0469 | SAT | 0.0512 | 4.35 | 0.0060 |
| `satlib_more__uuf125-01.cnf` | UNSAT | 0.1015 | UNSAT | 0.1062 | UNSAT | 0.0912 | UNSAT | 0.1000 | 4.35 | 0.0151 |
| `satlib_more__uuf125-010.cnf` | UNSAT | 0.1497 | UNSAT | 0.1544 | UNSAT | 0.1579 | UNSAT | 0.2032 | 4.2 | 0.0535 |
| `satlib_more__uuf150-01.cnf` | UNSAT | 0.3528 | UNSAT | 0.4129 | UNSAT | 0.3490 | UNSAT | 0.3705 | 4.35 | 0.0639 |
| `satlib_subset__dubois20.cnf` | UNSAT | 0.0271 | UNSAT | 0.0342 | UNSAT | 0.0240 | UNSAT | 0.0303 | 4.35 | 0.0102 |
| `satlib_subset__dubois21.cnf` | UNSAT | 0.0369 | UNSAT | 0.0367 | UNSAT | 0.0284 | UNSAT | 0.0285 | 4.35 | 0.0085 |
| `satlib_subset__flat50-1.cnf` | SAT | 0.0322 | SAT | 0.0263 | SAT | 0.0365 | SAT | 0.0353 | 4.3 | 0.0102 |
| `satlib_subset__flat50-10.cnf` | SAT | 0.0272 | SAT | 0.0360 | SAT | 0.0265 | SAT | 0.0328 | 4.35 | 0.0095 |
| `satlib_subset__hole10.cnf` | UNSAT | 0.0295 | UNSAT | 0.0232 | UNSAT | 0.0363 | UNSAT | 0.0276 | 4.3 | 0.0130 |
| `satlib_subset__hole8.cnf` | UNSAT | 0.0331 | UNSAT | 0.0350 | UNSAT | 0.0398 | UNSAT | 0.0264 | 4.4 | 0.0134 |
| `satlib_subset__uf100-01.cnf` | SAT | 0.0651 | SAT | 0.0550 | SAT | 0.0505 | SAT | 0.0616 | 4.35 | 0.0146 |
| `satlib_subset__uf100-010.cnf` | SAT | 0.0272 | SAT | 0.0345 | SAT | 0.0258 | SAT | 0.0251 | 4.4 | 0.0095 |
| `satlib_subset__uuf100-01.cnf` | UNSAT | 0.0414 | UNSAT | 0.0541 | UNSAT | 0.0519 | UNSAT | 0.0442 | 4.2 | 0.0127 |
| `satlib_subset__uuf100-010.cnf` | UNSAT | 0.0566 | UNSAT | 0.0606 | UNSAT | 0.0569 | UNSAT | 0.0543 | 4.4 | 0.0063 |
| `small__test_1.cnf` | SAT | 0.0388 | SAT | 0.0348 | SAT | 0.0379 | SAT | 0.0336 | 4.4 | 0.0052 |
| `small__test_10.cnf` | UNSAT | 0.0271 | UNSAT | 0.0405 | UNSAT | 0.0355 | UNSAT | 0.0254 | 4.4 | 0.0150 |
| `small__test_2.cnf` | SAT | 0.0260 | SAT | 0.0308 | SAT | 0.0278 | SAT | 0.0235 | 4.4 | 0.0073 |
| `small__test_3.cnf` | SAT | 0.0321 | SAT | 0.0244 | SAT | 0.0320 | SAT | 0.0297 | 4.3 | 0.0077 |
| `small__test_4.cnf` | UNSAT | 0.0356 | UNSAT | 0.0349 | UNSAT | 0.0360 | UNSAT | 0.0236 | 4.4 | 0.0124 |
| `small__test_5.cnf` | SAT | 0.0195 | SAT | 0.0230 | SAT | 0.0314 | SAT | 0.0234 | 4.2 | 0.0119 |
| `small__test_6.cnf` | SAT | 0.0296 | SAT | 0.0287 | SAT | 0.0336 | SAT | 0.0223 | 4.4 | 0.0113 |
| `small__test_7.cnf` | SAT | 0.0292 | SAT | 0.0334 | SAT | 0.0290 | SAT | 0.0248 | 4.4 | 0.0087 |
| `small__test_8.cnf` | UNSAT | 0.0269 | UNSAT | 0.0376 | UNSAT | 0.0335 | UNSAT | 0.0373 | 4.2 | 0.0107 |
| `small__test_9.cnf` | SAT | 0.0322 | SAT | 0.0250 | SAT | 0.0397 | SAT | 0.0382 | 4.3 | 0.0147 |
| `special__dense.cnf` | UNSAT | 0.1273 | UNSAT | 0.1226 | UNSAT | 0.1322 | UNSAT | 0.1430 | 4.3 | 0.0204 |
| `special__easy.cnf` | SAT | 0.0361 | SAT | 0.0265 | SAT | 0.0361 | SAT | 0.0378 | 4.3 | 0.0113 |
| `special__hard.cnf` | UNSAT | 2.8602 | UNSAT | 2.6849 | UNSAT | 2.7138 | UNSAT | 2.6253 | 4.4 | 0.2349 |
| `special__pigeonhole.cnf` | UNSAT | 0.0384 | UNSAT | 0.0301 | UNSAT | 0.0316 | UNSAT | 0.0314 | 4.3 | 0.0083 |
| `special__tseitin.cnf` | UNSAT | 0.0380 | UNSAT | 0.0296 | UNSAT | 0.0339 | UNSAT | 0.0246 | 4.4 | 0.0134 |
