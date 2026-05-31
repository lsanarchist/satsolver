# oldsatsolver.py vs satsolver.py avg5, timeout cases removed

Generated: 2026-05-31T15:34:23
Old solver command: `python odlsatsover.py <input.cnf> <output.txt>`
New solver command: `python satsolver.py <input.cnf> <output.txt>`
Dataset: `course_cnf_tests`
Repeats per solver per case: `5`
Per-run timeout: `60s`

Excluded timeout cases:
- `cnf_training_complex__complex_cnf_hard__mycielski_iter4_color5_unsat.cnf`
- `cnf_training_complex__complex_cnf_hard__planted3sat_balanced_n400_m1704_seed1.cnf`

## Summary

- Cases tested: `277`
- Old ok: `277/277`
- New ok: `277/277`
- Old avg-total: `55.3984s`
- New avg-total: `42.6502s`
- Delta new-old: `-12.7482s`
- Improved valid cases: `242`
- Regressed valid cases: `21`
- Tied valid cases: `14`
- Benchmark wall time: `641.3241s`

## Largest Improvements

| case | old avg s | new avg s | delta s | old result | new result |
|---|---:|---:|---:|---|---|
| `large__test_6.cnf` | 11.6822 | 3.3346 | -8.3476 | UNSAT | UNSAT |
| `special__hard.cnf` | 7.8371 | 2.5353 | -5.3018 | UNSAT | UNSAT |
| `cnf_training_complex__complex_cnf_moderate__ramsey_R3_4_n10_unsat.cnf` | 4.8028 | 1.0746 | -3.7282 | UNSAT | UNSAT |
| `cnf_training_complex__complex_cnf_moderate__ramsey_R3_4_n9_unsat.cnf` | 4.4500 | 1.1497 | -3.3003 | UNSAT | UNSAT |
| `cnf_training_complex__complex_cnf_hard__ramsey_R3_4_n11_unsat.cnf` | 3.3089 | 1.1366 | -2.1723 | UNSAT | UNSAT |
| `cnf_training_complex__complex_cnf_hard__planted3sat_balanced_n320_m1363_seed2.cnf` | 1.9677 | 0.5680 | -1.3997 | SAT | SAT |
| `medium__test_4.cnf` | 1.6447 | 0.8491 | -0.7956 | UNSAT | UNSAT |
| `large__test_10.cnf` | 1.5866 | 0.8534 | -0.7332 | UNSAT | UNSAT |
| `cnf_training_complex__complex_cnf_moderate__mycielski_iter3_color4_unsat.cnf` | 0.6145 | 0.2506 | -0.3639 | UNSAT | UNSAT |
| `medium__test_3.cnf` | 0.6682 | 0.4754 | -0.1928 | UNSAT | UNSAT |
| `cnf_training_complex__complex_cnf_moderate__ordering_no_minimum_n12.cnf` | 0.1494 | 0.0748 | -0.0746 | UNSAT | UNSAT |
| `satlib_more__uuf150-01.cnf` | 0.4193 | 0.3498 | -0.0695 | UNSAT | UNSAT |
| `satlib_more__uuf125-010.cnf` | 0.1684 | 0.1438 | -0.0246 | UNSAT | UNSAT |
| `satlib_more__uuf125-01.cnf` | 0.1197 | 0.0972 | -0.0226 | UNSAT | UNSAT |
| `cnf_training_complex__complex_cnf_moderate__ramsey_R3_3_n7_unsat.cnf` | 0.0517 | 0.0316 | -0.0201 | UNSAT | UNSAT |

## Largest Regressions

| case | old avg s | new avg s | delta s | old result | new result |
|---|---:|---:|---:|---|---|
| `cnf_training_complex__complex_cnf_hard__planted3sat_balanced_n260_m1108_seed1.cnf` | 2.1119 | 15.5114 | +13.3995 | SAT | SAT |
| `large__test_8.cnf` | 0.3017 | 1.6169 | +1.3152 | SAT | SAT |
| `cnf_training_complex__complex_cnf_moderate__planted3sat_balanced_n200_m852_seed2.cnf` | 0.4937 | 0.9498 | +0.4561 | SAT | SAT |
| `cnf_training_complex__complex_cnf_moderate__xor_sparse_sat_n128_eq165_w3-4_seed3.cnf` | 0.1046 | 0.2393 | +0.1347 | SAT | SAT |
| `cnf_training_complex__complex_cnf_hard__planted3sat_balanced_n320_m1363_seed1.cnf` | 0.6761 | 0.8029 | +0.1269 | SAT | SAT |
| `cnf_training_complex__complex_cnf_moderate__planted3sat_balanced_n200_m852_seed1.cnf` | 0.4078 | 0.4627 | +0.0549 | SAT | SAT |
| `cnf_training_complex__complex_cnf_hard__planted3sat_balanced_n260_m1108_seed2.cnf` | 0.9930 | 1.0306 | +0.0376 | SAT | SAT |
| `satlib_more__uf125-010.cnf` | 0.0557 | 0.0877 | +0.0320 | SAT | SAT |
| `cnf_training_extra__extra_cnf__equivalence_chain_len40_unsat.cnf` | 0.0298 | 0.0370 | +0.0072 | UNSAT | UNSAT |
| `cnf_training_extra__extra_cnf__exact_random3sat_unsat_n8_m31_016.cnf` | 0.0329 | 0.0392 | +0.0063 | UNSAT | UNSAT |
| `cnf_training_complex__complex_cnf_moderate__ramsey_R3_3_n8_unsat.cnf` | 0.0336 | 0.0369 | +0.0033 | UNSAT | UNSAT |
| `satlib_subset__flat50-10.cnf` | 0.0343 | 0.0376 | +0.0032 | SAT | SAT |
| `cnf_training_extra__extra_cnf__exact_random3sat_sat_n12_m47_013.cnf` | 0.0337 | 0.0365 | +0.0028 | SAT | SAT |
| `cnf_training_complex__complex_cnf_moderate__tseitin_deg3_v80_unsat.cnf` | 0.0329 | 0.0349 | +0.0020 | UNSAT | UNSAT |
| `cnf_training_extra__extra_cnf__exact_random3sat_unsat_n16_m85_003.cnf` | 0.0394 | 0.0412 | +0.0019 | UNSAT | UNSAT |

## All Cases

| case | old avg s | old median s | old min s | old max s | new avg s | new median s | new min s | new max s | delta s | old status | new status |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---|---|
| `cnf_training_complex__complex_cnf_hard__planted3sat_balanced_n260_m1108_seed1.cnf` | 2.1119 | 2.0811 | 2.0093 | 2.2660 | 15.5114 | 15.5168 | 15.2883 | 15.7660 | +13.3995 | SAT | SAT |
| `cnf_training_complex__complex_cnf_hard__planted3sat_balanced_n260_m1108_seed2.cnf` | 0.9930 | 0.9862 | 0.9706 | 1.0151 | 1.0306 | 1.0292 | 0.9885 | 1.0585 | +0.0376 | SAT | SAT |
| `cnf_training_complex__complex_cnf_hard__planted3sat_balanced_n320_m1363_seed1.cnf` | 0.6761 | 0.6823 | 0.6563 | 0.6983 | 0.8029 | 0.8084 | 0.7766 | 0.8377 | +0.1269 | SAT | SAT |
| `cnf_training_complex__complex_cnf_hard__planted3sat_balanced_n320_m1363_seed2.cnf` | 1.9677 | 1.9855 | 1.9105 | 2.0052 | 0.5680 | 0.5689 | 0.5239 | 0.6124 | -1.3997 | SAT | SAT |
| `cnf_training_complex__complex_cnf_hard__ramsey_R3_4_n11_unsat.cnf` | 3.3089 | 3.3085 | 3.2047 | 3.3749 | 1.1366 | 1.1321 | 1.1110 | 1.1896 | -2.1723 | UNSAT | UNSAT |
| `cnf_training_complex__complex_cnf_hard__tseitin_deg3_v100_sat.cnf` | 0.0418 | 0.0381 | 0.0356 | 0.0525 | 0.0361 | 0.0377 | 0.0281 | 0.0401 | -0.0058 | SAT | SAT |
| `cnf_training_complex__complex_cnf_hard__tseitin_deg3_v100_unsat.cnf` | 0.0351 | 0.0343 | 0.0294 | 0.0431 | 0.0304 | 0.0241 | 0.0211 | 0.0452 | -0.0047 | UNSAT | UNSAT |
| `cnf_training_complex__complex_cnf_hard__tseitin_deg3_v120_sat.cnf` | 0.0419 | 0.0419 | 0.0348 | 0.0476 | 0.0409 | 0.0422 | 0.0293 | 0.0471 | -0.0011 | SAT | SAT |
| `cnf_training_complex__complex_cnf_hard__tseitin_deg3_v120_unsat.cnf` | 0.0326 | 0.0330 | 0.0300 | 0.0345 | 0.0332 | 0.0339 | 0.0228 | 0.0464 | +0.0006 | UNSAT | UNSAT |
| `cnf_training_complex__complex_cnf_hard__tseitin_deg3_v160_sat.cnf` | 0.0650 | 0.0677 | 0.0527 | 0.0698 | 0.0497 | 0.0479 | 0.0418 | 0.0604 | -0.0153 | SAT | SAT |
| `cnf_training_complex__complex_cnf_hard__tseitin_deg3_v160_unsat.cnf` | 0.0391 | 0.0399 | 0.0303 | 0.0488 | 0.0329 | 0.0337 | 0.0237 | 0.0410 | -0.0061 | UNSAT | UNSAT |
| `cnf_training_complex__complex_cnf_hard__tseitin_deg4_v64_sat.cnf` | 0.0490 | 0.0477 | 0.0457 | 0.0558 | 0.0410 | 0.0417 | 0.0376 | 0.0440 | -0.0080 | SAT | SAT |
| `cnf_training_complex__complex_cnf_hard__tseitin_deg4_v64_unsat.cnf` | 0.0382 | 0.0336 | 0.0333 | 0.0466 | 0.0288 | 0.0251 | 0.0230 | 0.0372 | -0.0093 | UNSAT | UNSAT |
| `cnf_training_complex__complex_cnf_hard__tseitin_deg4_v96_sat.cnf` | 0.0491 | 0.0500 | 0.0408 | 0.0538 | 0.0421 | 0.0454 | 0.0287 | 0.0569 | -0.0069 | SAT | SAT |
| `cnf_training_complex__complex_cnf_hard__tseitin_deg4_v96_unsat.cnf` | 0.0364 | 0.0379 | 0.0300 | 0.0417 | 0.0282 | 0.0263 | 0.0223 | 0.0343 | -0.0081 | UNSAT | UNSAT |
| `cnf_training_complex__complex_cnf_hard__vdw_2color_k4_n45_unsat.cnf` | 0.0627 | 0.0632 | 0.0600 | 0.0652 | 0.0597 | 0.0588 | 0.0511 | 0.0755 | -0.0030 | UNSAT | UNSAT |
| `cnf_training_complex__complex_cnf_hard__vdw_2color_k4_n60_unsat.cnf` | 0.0711 | 0.0702 | 0.0625 | 0.0770 | 0.0592 | 0.0630 | 0.0515 | 0.0649 | -0.0119 | UNSAT | UNSAT |
| `cnf_training_complex__complex_cnf_hard__xor_sparse_unsat_n100_eq135_w3-4_seed4.cnf` | 0.0387 | 0.0394 | 0.0324 | 0.0428 | 0.0350 | 0.0379 | 0.0247 | 0.0383 | -0.0037 | UNSAT | UNSAT |
| `cnf_training_complex__complex_cnf_hard__xor_sparse_unsat_n140_eq190_w3-4_seed5.cnf` | 0.0441 | 0.0451 | 0.0325 | 0.0524 | 0.0336 | 0.0353 | 0.0244 | 0.0374 | -0.0105 | UNSAT | UNSAT |
| `cnf_training_complex__complex_cnf_hard__xor_sparse_unsat_n180_eq250_w3-4_seed6.cnf` | 0.0444 | 0.0449 | 0.0420 | 0.0469 | 0.0374 | 0.0359 | 0.0311 | 0.0465 | -0.0070 | UNSAT | UNSAT |
| `cnf_training_complex__complex_cnf_moderate__mycielski_iter2_color3_unsat.cnf` | 0.0392 | 0.0413 | 0.0337 | 0.0449 | 0.0312 | 0.0336 | 0.0205 | 0.0386 | -0.0080 | UNSAT | UNSAT |
| `cnf_training_complex__complex_cnf_moderate__mycielski_iter2_color4_sat.cnf` | 0.0476 | 0.0485 | 0.0394 | 0.0537 | 0.0280 | 0.0237 | 0.0216 | 0.0378 | -0.0196 | SAT | SAT |
| `cnf_training_complex__complex_cnf_moderate__mycielski_iter3_color4_unsat.cnf` | 0.6145 | 0.6167 | 0.5993 | 0.6264 | 0.2506 | 0.2444 | 0.2417 | 0.2695 | -0.3639 | UNSAT | UNSAT |
| `cnf_training_complex__complex_cnf_moderate__mycielski_iter3_color5_sat.cnf` | 0.0423 | 0.0444 | 0.0333 | 0.0465 | 0.0345 | 0.0362 | 0.0259 | 0.0447 | -0.0077 | SAT | SAT |
| `cnf_training_complex__complex_cnf_moderate__ordering_no_minimum_n10.cnf` | 0.0536 | 0.0536 | 0.0466 | 0.0612 | 0.0502 | 0.0514 | 0.0432 | 0.0567 | -0.0034 | UNSAT | UNSAT |
| `cnf_training_complex__complex_cnf_moderate__ordering_no_minimum_n12.cnf` | 0.1494 | 0.1490 | 0.1373 | 0.1589 | 0.0748 | 0.0745 | 0.0679 | 0.0830 | -0.0746 | UNSAT | UNSAT |
| `cnf_training_complex__complex_cnf_moderate__ordering_no_minimum_n8.cnf` | 0.0439 | 0.0434 | 0.0362 | 0.0519 | 0.0341 | 0.0303 | 0.0259 | 0.0440 | -0.0098 | UNSAT | UNSAT |
| `cnf_training_complex__complex_cnf_moderate__orthogonal_latin_squares_order3_sat.cnf` | 0.0555 | 0.0545 | 0.0489 | 0.0662 | 0.0464 | 0.0465 | 0.0414 | 0.0528 | -0.0091 | SAT | SAT |
| `cnf_training_complex__complex_cnf_moderate__pigeonhole_php_11_into_10.cnf` | 0.0381 | 0.0387 | 0.0301 | 0.0496 | 0.0347 | 0.0347 | 0.0222 | 0.0443 | -0.0034 | UNSAT | UNSAT |
| `cnf_training_complex__complex_cnf_moderate__pigeonhole_php_13_into_12.cnf` | 0.0369 | 0.0344 | 0.0312 | 0.0434 | 0.0342 | 0.0374 | 0.0239 | 0.0436 | -0.0028 | UNSAT | UNSAT |
| `cnf_training_complex__complex_cnf_moderate__pigeonhole_php_9_into_8.cnf` | 0.0405 | 0.0424 | 0.0299 | 0.0514 | 0.0358 | 0.0362 | 0.0268 | 0.0452 | -0.0046 | UNSAT | UNSAT |
| `cnf_training_complex__complex_cnf_moderate__planted3sat_balanced_n120_m511_seed1.cnf` | 0.0480 | 0.0460 | 0.0378 | 0.0586 | 0.0374 | 0.0373 | 0.0357 | 0.0404 | -0.0106 | SAT | SAT |
| `cnf_training_complex__complex_cnf_moderate__planted3sat_balanced_n120_m511_seed2.cnf` | 0.0442 | 0.0465 | 0.0343 | 0.0508 | 0.0342 | 0.0358 | 0.0256 | 0.0436 | -0.0100 | SAT | SAT |
| `cnf_training_complex__complex_cnf_moderate__planted3sat_balanced_n160_m682_seed1.cnf` | 0.0514 | 0.0559 | 0.0419 | 0.0586 | 0.0407 | 0.0374 | 0.0322 | 0.0533 | -0.0107 | SAT | SAT |
| `cnf_training_complex__complex_cnf_moderate__planted3sat_balanced_n160_m682_seed2.cnf` | 0.0513 | 0.0504 | 0.0442 | 0.0575 | 0.0422 | 0.0433 | 0.0347 | 0.0479 | -0.0091 | SAT | SAT |
| `cnf_training_complex__complex_cnf_moderate__planted3sat_balanced_n200_m852_seed1.cnf` | 0.4078 | 0.4069 | 0.3850 | 0.4249 | 0.4627 | 0.4622 | 0.4502 | 0.4745 | +0.0549 | SAT | SAT |
| `cnf_training_complex__complex_cnf_moderate__planted3sat_balanced_n200_m852_seed2.cnf` | 0.4937 | 0.4948 | 0.4651 | 0.5184 | 0.9498 | 0.9296 | 0.8807 | 1.0887 | +0.4561 | SAT | SAT |
| `cnf_training_complex__complex_cnf_moderate__ramsey_R3_3_n6_unsat.cnf` | 0.0364 | 0.0356 | 0.0282 | 0.0450 | 0.0284 | 0.0276 | 0.0215 | 0.0377 | -0.0079 | UNSAT | UNSAT |
| `cnf_training_complex__complex_cnf_moderate__ramsey_R3_3_n7_unsat.cnf` | 0.0517 | 0.0474 | 0.0393 | 0.0723 | 0.0316 | 0.0318 | 0.0271 | 0.0369 | -0.0201 | UNSAT | UNSAT |
| `cnf_training_complex__complex_cnf_moderate__ramsey_R3_3_n8_unsat.cnf` | 0.0336 | 0.0327 | 0.0283 | 0.0409 | 0.0369 | 0.0388 | 0.0257 | 0.0434 | +0.0033 | UNSAT | UNSAT |
| `cnf_training_complex__complex_cnf_moderate__ramsey_R3_4_n10_unsat.cnf` | 4.8028 | 4.7898 | 4.6475 | 4.9729 | 1.0746 | 1.0775 | 1.0594 | 1.0828 | -3.7282 | UNSAT | UNSAT |
| `cnf_training_complex__complex_cnf_moderate__ramsey_R3_4_n9_unsat.cnf` | 4.4500 | 4.4291 | 4.2985 | 4.6075 | 1.1497 | 1.1513 | 1.0909 | 1.2090 | -3.3003 | UNSAT | UNSAT |
| `cnf_training_complex__complex_cnf_moderate__tseitin_deg3_v40_sat.cnf` | 0.0433 | 0.0477 | 0.0308 | 0.0488 | 0.0343 | 0.0349 | 0.0310 | 0.0378 | -0.0091 | SAT | SAT |
| `cnf_training_complex__complex_cnf_moderate__tseitin_deg3_v40_unsat.cnf` | 0.0354 | 0.0323 | 0.0296 | 0.0446 | 0.0308 | 0.0317 | 0.0222 | 0.0424 | -0.0047 | UNSAT | UNSAT |
| `cnf_training_complex__complex_cnf_moderate__tseitin_deg3_v60_sat.cnf` | 0.0434 | 0.0431 | 0.0392 | 0.0486 | 0.0318 | 0.0354 | 0.0236 | 0.0370 | -0.0116 | SAT | SAT |
| `cnf_training_complex__complex_cnf_moderate__tseitin_deg3_v60_unsat.cnf` | 0.0394 | 0.0410 | 0.0286 | 0.0530 | 0.0311 | 0.0324 | 0.0203 | 0.0404 | -0.0083 | UNSAT | UNSAT |
| `cnf_training_complex__complex_cnf_moderate__tseitin_deg3_v80_sat.cnf` | 0.0362 | 0.0353 | 0.0299 | 0.0414 | 0.0344 | 0.0363 | 0.0294 | 0.0403 | -0.0018 | SAT | SAT |
| `cnf_training_complex__complex_cnf_moderate__tseitin_deg3_v80_unsat.cnf` | 0.0329 | 0.0324 | 0.0272 | 0.0415 | 0.0349 | 0.0379 | 0.0263 | 0.0393 | +0.0020 | UNSAT | UNSAT |
| `cnf_training_complex__complex_cnf_moderate__vdw_2color_k3_n16_unsat.cnf` | 0.0459 | 0.0462 | 0.0398 | 0.0530 | 0.0274 | 0.0257 | 0.0208 | 0.0352 | -0.0185 | UNSAT | UNSAT |
| `cnf_training_complex__complex_cnf_moderate__vdw_2color_k3_n9_unsat.cnf` | 0.0428 | 0.0428 | 0.0391 | 0.0482 | 0.0308 | 0.0284 | 0.0215 | 0.0412 | -0.0120 | UNSAT | UNSAT |
| `cnf_training_complex__complex_cnf_moderate__vdw_2color_k4_n35_unsat.cnf` | 0.0568 | 0.0587 | 0.0500 | 0.0607 | 0.0497 | 0.0447 | 0.0429 | 0.0624 | -0.0071 | UNSAT | UNSAT |
| `cnf_training_complex__complex_cnf_moderate__xor_sparse_sat_n128_eq165_w3-4_seed3.cnf` | 0.1046 | 0.1066 | 0.0904 | 0.1134 | 0.2393 | 0.2376 | 0.2259 | 0.2576 | +0.1347 | SAT | SAT |
| `cnf_training_complex__complex_cnf_moderate__xor_sparse_sat_n64_eq82_w3_seed1.cnf` | 0.0423 | 0.0435 | 0.0307 | 0.0500 | 0.0327 | 0.0354 | 0.0235 | 0.0426 | -0.0096 | SAT | SAT |
| `cnf_training_complex__complex_cnf_moderate__xor_sparse_sat_n96_eq125_w3_seed2.cnf` | 0.0434 | 0.0474 | 0.0332 | 0.0501 | 0.0385 | 0.0401 | 0.0286 | 0.0445 | -0.0049 | SAT | SAT |
| `cnf_training_complex__complex_cnf_moderate__xor_sparse_unsat_n48_eq62_w3_seed1.cnf` | 0.0335 | 0.0328 | 0.0270 | 0.0443 | 0.0319 | 0.0332 | 0.0226 | 0.0361 | -0.0016 | UNSAT | UNSAT |
| `cnf_training_complex__complex_cnf_moderate__xor_sparse_unsat_n64_eq86_w3_seed2.cnf` | 0.0364 | 0.0335 | 0.0329 | 0.0420 | 0.0309 | 0.0325 | 0.0207 | 0.0398 | -0.0055 | UNSAT | UNSAT |
| `cnf_training_complex__complex_cnf_moderate__xor_sparse_unsat_n80_eq108_w3-4_seed3.cnf` | 0.0400 | 0.0408 | 0.0318 | 0.0454 | 0.0294 | 0.0227 | 0.0211 | 0.0461 | -0.0106 | UNSAT | UNSAT |
| `cnf_training_complex__complex_cnf_stress__tseitin_deg3_v240_unsat.cnf` | 0.0365 | 0.0365 | 0.0295 | 0.0444 | 0.0311 | 0.0309 | 0.0270 | 0.0351 | -0.0053 | UNSAT | UNSAT |
| `cnf_training_complex__complex_cnf_stress__tseitin_deg4_v160_unsat.cnf` | 0.0366 | 0.0338 | 0.0307 | 0.0479 | 0.0384 | 0.0406 | 0.0268 | 0.0463 | +0.0018 | UNSAT | UNSAT |
| `cnf_training_complex__complex_cnf_stress__xor_sparse_unsat_n240_eq330_w3-4_seed1.cnf` | 0.0515 | 0.0498 | 0.0471 | 0.0582 | 0.0388 | 0.0396 | 0.0315 | 0.0438 | -0.0127 | UNSAT | UNSAT |
| `cnf_training_extra__extra_cnf__cardinality_exactly_one_sat_g10_s5_004.cnf` | 0.0364 | 0.0322 | 0.0320 | 0.0528 | 0.0331 | 0.0344 | 0.0239 | 0.0375 | -0.0032 | SAT | SAT |
| `cnf_training_extra__extra_cnf__cardinality_exactly_one_sat_g12_s6_005.cnf` | 0.0377 | 0.0404 | 0.0297 | 0.0445 | 0.0257 | 0.0225 | 0.0218 | 0.0338 | -0.0120 | SAT | SAT |
| `cnf_training_extra__extra_cnf__cardinality_exactly_one_sat_g16_s4_006.cnf` | 0.0362 | 0.0302 | 0.0276 | 0.0522 | 0.0321 | 0.0338 | 0.0256 | 0.0347 | -0.0041 | SAT | SAT |
| `cnf_training_extra__extra_cnf__cardinality_exactly_one_sat_g4_s4_001.cnf` | 0.0304 | 0.0282 | 0.0261 | 0.0396 | 0.0219 | 0.0214 | 0.0199 | 0.0246 | -0.0085 | SAT | SAT |
| `cnf_training_extra__extra_cnf__cardinality_exactly_one_sat_g5_s5_002.cnf` | 0.0404 | 0.0404 | 0.0292 | 0.0522 | 0.0358 | 0.0344 | 0.0333 | 0.0424 | -0.0046 | SAT | SAT |
| `cnf_training_extra__extra_cnf__cardinality_exactly_one_sat_g8_s4_003.cnf` | 0.0400 | 0.0430 | 0.0321 | 0.0470 | 0.0272 | 0.0236 | 0.0215 | 0.0354 | -0.0128 | SAT | SAT |
| `cnf_training_extra__extra_cnf__cardinality_exactly_one_unsat_g10_s6_005.cnf` | 0.0358 | 0.0384 | 0.0264 | 0.0420 | 0.0310 | 0.0308 | 0.0256 | 0.0371 | -0.0048 | UNSAT | UNSAT |
| `cnf_training_extra__extra_cnf__cardinality_exactly_one_unsat_g12_s4_006.cnf` | 0.0346 | 0.0320 | 0.0289 | 0.0453 | 0.0268 | 0.0240 | 0.0215 | 0.0334 | -0.0078 | UNSAT | UNSAT |
| `cnf_training_extra__extra_cnf__cardinality_exactly_one_unsat_g3_s4_001.cnf` | 0.0385 | 0.0413 | 0.0331 | 0.0431 | 0.0287 | 0.0319 | 0.0227 | 0.0334 | -0.0099 | UNSAT | UNSAT |
| `cnf_training_extra__extra_cnf__cardinality_exactly_one_unsat_g4_s5_002.cnf` | 0.0373 | 0.0409 | 0.0263 | 0.0485 | 0.0296 | 0.0327 | 0.0225 | 0.0368 | -0.0076 | UNSAT | UNSAT |
| `cnf_training_extra__extra_cnf__cardinality_exactly_one_unsat_g6_s4_003.cnf` | 0.0413 | 0.0421 | 0.0269 | 0.0590 | 0.0343 | 0.0262 | 0.0225 | 0.0520 | -0.0070 | UNSAT | UNSAT |
| `cnf_training_extra__extra_cnf__cardinality_exactly_one_unsat_g8_s5_004.cnf` | 0.0326 | 0.0302 | 0.0265 | 0.0444 | 0.0318 | 0.0328 | 0.0245 | 0.0371 | -0.0008 | UNSAT | UNSAT |
| `cnf_training_extra__extra_cnf__equivalence_chain_len10_sat.cnf` | 0.0365 | 0.0349 | 0.0283 | 0.0460 | 0.0308 | 0.0278 | 0.0211 | 0.0481 | -0.0056 | SAT | SAT |
| `cnf_training_extra__extra_cnf__equivalence_chain_len10_unsat.cnf` | 0.0411 | 0.0415 | 0.0329 | 0.0490 | 0.0346 | 0.0334 | 0.0216 | 0.0442 | -0.0066 | UNSAT | UNSAT |
| `cnf_training_extra__extra_cnf__equivalence_chain_len120_sat.cnf` | 0.0419 | 0.0404 | 0.0349 | 0.0520 | 0.0333 | 0.0362 | 0.0260 | 0.0404 | -0.0086 | SAT | SAT |
| `cnf_training_extra__extra_cnf__equivalence_chain_len120_unsat.cnf` | 0.0402 | 0.0418 | 0.0313 | 0.0502 | 0.0364 | 0.0391 | 0.0267 | 0.0426 | -0.0039 | UNSAT | UNSAT |
| `cnf_training_extra__extra_cnf__equivalence_chain_len20_sat.cnf` | 0.0395 | 0.0389 | 0.0303 | 0.0527 | 0.0321 | 0.0338 | 0.0231 | 0.0375 | -0.0074 | SAT | SAT |
| `cnf_training_extra__extra_cnf__equivalence_chain_len20_unsat.cnf` | 0.0360 | 0.0391 | 0.0259 | 0.0461 | 0.0359 | 0.0349 | 0.0319 | 0.0440 | -0.0001 | UNSAT | UNSAT |
| `cnf_training_extra__extra_cnf__equivalence_chain_len40_sat.cnf` | 0.0367 | 0.0369 | 0.0265 | 0.0530 | 0.0326 | 0.0327 | 0.0193 | 0.0441 | -0.0040 | SAT | SAT |
| `cnf_training_extra__extra_cnf__equivalence_chain_len40_unsat.cnf` | 0.0298 | 0.0289 | 0.0261 | 0.0359 | 0.0370 | 0.0379 | 0.0296 | 0.0417 | +0.0072 | UNSAT | UNSAT |
| `cnf_training_extra__extra_cnf__equivalence_chain_len80_sat.cnf` | 0.0413 | 0.0436 | 0.0289 | 0.0487 | 0.0359 | 0.0356 | 0.0329 | 0.0387 | -0.0054 | SAT | SAT |
| `cnf_training_extra__extra_cnf__equivalence_chain_len80_unsat.cnf` | 0.0409 | 0.0425 | 0.0310 | 0.0495 | 0.0288 | 0.0299 | 0.0216 | 0.0377 | -0.0121 | UNSAT | UNSAT |
| `cnf_training_extra__extra_cnf__exact_random3sat_sat_n10_m49_008.cnf` | 0.0384 | 0.0415 | 0.0310 | 0.0439 | 0.0277 | 0.0251 | 0.0211 | 0.0367 | -0.0107 | SAT | SAT |
| `cnf_training_extra__extra_cnf__exact_random3sat_sat_n11_m40_017.cnf` | 0.0380 | 0.0421 | 0.0297 | 0.0434 | 0.0332 | 0.0351 | 0.0221 | 0.0374 | -0.0048 | SAT | SAT |
| `cnf_training_extra__extra_cnf__exact_random3sat_sat_n11_m46_001.cnf` | 0.0421 | 0.0427 | 0.0337 | 0.0467 | 0.0305 | 0.0299 | 0.0247 | 0.0388 | -0.0116 | SAT | SAT |
| `cnf_training_extra__extra_cnf__exact_random3sat_sat_n12_m43_012.cnf` | 0.0334 | 0.0308 | 0.0270 | 0.0399 | 0.0307 | 0.0337 | 0.0217 | 0.0384 | -0.0027 | SAT | SAT |
| `cnf_training_extra__extra_cnf__exact_random3sat_sat_n12_m47_006.cnf` | 0.0352 | 0.0294 | 0.0286 | 0.0482 | 0.0371 | 0.0357 | 0.0337 | 0.0428 | +0.0018 | SAT | SAT |
| `cnf_training_extra__extra_cnf__exact_random3sat_sat_n12_m47_013.cnf` | 0.0337 | 0.0305 | 0.0259 | 0.0424 | 0.0365 | 0.0351 | 0.0336 | 0.0399 | +0.0028 | SAT | SAT |
| `cnf_training_extra__extra_cnf__exact_random3sat_sat_n13_m47_011.cnf` | 0.0332 | 0.0303 | 0.0267 | 0.0409 | 0.0279 | 0.0314 | 0.0212 | 0.0340 | -0.0054 | SAT | SAT |
| `cnf_training_extra__extra_cnf__exact_random3sat_sat_n13_m64_004.cnf` | 0.0389 | 0.0423 | 0.0294 | 0.0428 | 0.0284 | 0.0224 | 0.0214 | 0.0420 | -0.0105 | SAT | SAT |
| `cnf_training_extra__extra_cnf__exact_random3sat_sat_n14_m50_015.cnf` | 0.0349 | 0.0361 | 0.0276 | 0.0444 | 0.0292 | 0.0328 | 0.0219 | 0.0358 | -0.0057 | SAT | SAT |
| `cnf_training_extra__extra_cnf__exact_random3sat_sat_n15_m68_014.cnf` | 0.0393 | 0.0411 | 0.0285 | 0.0470 | 0.0309 | 0.0334 | 0.0225 | 0.0420 | -0.0084 | SAT | SAT |
| `cnf_training_extra__extra_cnf__exact_random3sat_sat_n16_m62_016.cnf` | 0.0372 | 0.0387 | 0.0311 | 0.0450 | 0.0280 | 0.0237 | 0.0212 | 0.0454 | -0.0092 | SAT | SAT |
| `cnf_training_extra__extra_cnf__exact_random3sat_sat_n16_m72_003.cnf` | 0.0388 | 0.0398 | 0.0302 | 0.0436 | 0.0309 | 0.0340 | 0.0215 | 0.0367 | -0.0079 | SAT | SAT |
| `cnf_training_extra__extra_cnf__exact_random3sat_sat_n8_m31_007.cnf` | 0.0349 | 0.0383 | 0.0284 | 0.0410 | 0.0305 | 0.0343 | 0.0230 | 0.0357 | -0.0044 | SAT | SAT |
| `cnf_training_extra__extra_cnf__exact_random3sat_sat_n8_m31_009.cnf` | 0.0408 | 0.0406 | 0.0291 | 0.0480 | 0.0345 | 0.0367 | 0.0229 | 0.0423 | -0.0062 | SAT | SAT |
| `cnf_training_extra__extra_cnf__exact_random3sat_sat_n8_m36_002.cnf` | 0.0422 | 0.0419 | 0.0386 | 0.0483 | 0.0354 | 0.0376 | 0.0259 | 0.0438 | -0.0068 | SAT | SAT |
| `cnf_training_extra__extra_cnf__exact_random3sat_sat_n8_m36_005.cnf` | 0.0330 | 0.0317 | 0.0294 | 0.0401 | 0.0346 | 0.0347 | 0.0330 | 0.0361 | +0.0016 | SAT | SAT |
| `cnf_training_extra__extra_cnf__exact_random3sat_sat_n9_m32_018.cnf` | 0.0423 | 0.0403 | 0.0385 | 0.0481 | 0.0330 | 0.0334 | 0.0245 | 0.0426 | -0.0093 | SAT | SAT |
| `cnf_training_extra__extra_cnf__exact_random3sat_sat_n9_m38_010.cnf` | 0.0397 | 0.0407 | 0.0296 | 0.0538 | 0.0286 | 0.0307 | 0.0231 | 0.0333 | -0.0110 | SAT | SAT |
| `cnf_training_extra__extra_cnf__exact_random3sat_unsat_n10_m49_015.cnf` | 0.0354 | 0.0369 | 0.0285 | 0.0407 | 0.0285 | 0.0263 | 0.0224 | 0.0358 | -0.0069 | UNSAT | UNSAT |
| `cnf_training_extra__extra_cnf__exact_random3sat_unsat_n11_m54_012.cnf` | 0.0389 | 0.0379 | 0.0343 | 0.0432 | 0.0322 | 0.0291 | 0.0249 | 0.0427 | -0.0067 | UNSAT | UNSAT |
| `cnf_training_extra__extra_cnf__exact_random3sat_unsat_n12_m64_007.cnf` | 0.0354 | 0.0376 | 0.0280 | 0.0405 | 0.0314 | 0.0313 | 0.0220 | 0.0419 | -0.0040 | UNSAT | UNSAT |
| `cnf_training_extra__extra_cnf__exact_random3sat_unsat_n12_m64_013.cnf` | 0.0396 | 0.0386 | 0.0309 | 0.0532 | 0.0305 | 0.0327 | 0.0201 | 0.0456 | -0.0091 | UNSAT | UNSAT |
| `cnf_training_extra__extra_cnf__exact_random3sat_unsat_n13_m69_006.cnf` | 0.0308 | 0.0294 | 0.0289 | 0.0346 | 0.0311 | 0.0329 | 0.0209 | 0.0371 | +0.0003 | UNSAT | UNSAT |
| `cnf_training_extra__extra_cnf__exact_random3sat_unsat_n13_m69_010.cnf` | 0.0428 | 0.0419 | 0.0378 | 0.0506 | 0.0291 | 0.0236 | 0.0229 | 0.0390 | -0.0137 | UNSAT | UNSAT |
| `cnf_training_extra__extra_cnf__exact_random3sat_unsat_n14_m74_017.cnf` | 0.0385 | 0.0407 | 0.0292 | 0.0510 | 0.0327 | 0.0365 | 0.0230 | 0.0412 | -0.0058 | UNSAT | UNSAT |
| `cnf_training_extra__extra_cnf__exact_random3sat_unsat_n15_m68_011.cnf` | 0.0315 | 0.0283 | 0.0271 | 0.0423 | 0.0299 | 0.0247 | 0.0245 | 0.0411 | -0.0016 | UNSAT | UNSAT |
| `cnf_training_extra__extra_cnf__exact_random3sat_unsat_n15_m68_018.cnf` | 0.0376 | 0.0343 | 0.0285 | 0.0462 | 0.0348 | 0.0330 | 0.0314 | 0.0433 | -0.0028 | UNSAT | UNSAT |
| `cnf_training_extra__extra_cnf__exact_random3sat_unsat_n15_m80_014.cnf` | 0.0386 | 0.0398 | 0.0296 | 0.0511 | 0.0342 | 0.0352 | 0.0276 | 0.0391 | -0.0044 | UNSAT | UNSAT |
| `cnf_training_extra__extra_cnf__exact_random3sat_unsat_n16_m78_005.cnf` | 0.0405 | 0.0427 | 0.0289 | 0.0448 | 0.0261 | 0.0235 | 0.0217 | 0.0332 | -0.0144 | UNSAT | UNSAT |
| `cnf_training_extra__extra_cnf__exact_random3sat_unsat_n16_m78_008.cnf` | 0.0340 | 0.0318 | 0.0266 | 0.0412 | 0.0306 | 0.0266 | 0.0241 | 0.0438 | -0.0034 | UNSAT | UNSAT |
| `cnf_training_extra__extra_cnf__exact_random3sat_unsat_n16_m85_002.cnf` | 0.0382 | 0.0396 | 0.0272 | 0.0447 | 0.0258 | 0.0241 | 0.0223 | 0.0345 | -0.0124 | UNSAT | UNSAT |
| `cnf_training_extra__extra_cnf__exact_random3sat_unsat_n16_m85_003.cnf` | 0.0394 | 0.0453 | 0.0266 | 0.0468 | 0.0412 | 0.0406 | 0.0388 | 0.0442 | +0.0019 | UNSAT | UNSAT |
| `cnf_training_extra__extra_cnf__exact_random3sat_unsat_n8_m31_016.cnf` | 0.0329 | 0.0299 | 0.0272 | 0.0480 | 0.0392 | 0.0387 | 0.0355 | 0.0437 | +0.0063 | UNSAT | UNSAT |
| `cnf_training_extra__extra_cnf__exact_random3sat_unsat_n8_m34_009.cnf` | 0.0360 | 0.0391 | 0.0285 | 0.0421 | 0.0311 | 0.0347 | 0.0214 | 0.0403 | -0.0049 | UNSAT | UNSAT |
| `cnf_training_extra__extra_cnf__exact_random3sat_unsat_n9_m38_004.cnf` | 0.0376 | 0.0403 | 0.0300 | 0.0438 | 0.0347 | 0.0334 | 0.0223 | 0.0450 | -0.0030 | UNSAT | UNSAT |
| `cnf_training_extra__extra_cnf__exact_random3sat_unsat_n9_m44_001.cnf` | 0.0420 | 0.0440 | 0.0297 | 0.0520 | 0.0285 | 0.0312 | 0.0201 | 0.0343 | -0.0135 | UNSAT | UNSAT |
| `cnf_training_extra__extra_cnf__graphcolor_k3_complete_K4_unsat.cnf` | 0.0438 | 0.0425 | 0.0380 | 0.0506 | 0.0320 | 0.0317 | 0.0214 | 0.0413 | -0.0118 | UNSAT | UNSAT |
| `cnf_training_extra__extra_cnf__graphcolor_k3_complete_K5_unsat.cnf` | 0.0362 | 0.0375 | 0.0291 | 0.0420 | 0.0319 | 0.0314 | 0.0198 | 0.0437 | -0.0043 | UNSAT | UNSAT |
| `cnf_training_extra__extra_cnf__graphcolor_k3_complete_K6_unsat.cnf` | 0.0294 | 0.0277 | 0.0255 | 0.0393 | 0.0275 | 0.0216 | 0.0213 | 0.0398 | -0.0019 | UNSAT | UNSAT |
| `cnf_training_extra__extra_cnf__graphcolor_k3_planted_v12_e26_001.cnf` | 0.0347 | 0.0341 | 0.0280 | 0.0399 | 0.0300 | 0.0318 | 0.0210 | 0.0332 | -0.0047 | SAT | SAT |
| `cnf_training_extra__extra_cnf__graphcolor_k3_planted_v16_e35_002.cnf` | 0.0311 | 0.0324 | 0.0266 | 0.0338 | 0.0302 | 0.0262 | 0.0234 | 0.0416 | -0.0008 | SAT | SAT |
| `cnf_training_extra__extra_cnf__graphcolor_k3_planted_v20_e44_003.cnf` | 0.0353 | 0.0377 | 0.0266 | 0.0424 | 0.0271 | 0.0223 | 0.0204 | 0.0378 | -0.0083 | SAT | SAT |
| `cnf_training_extra__extra_cnf__graphcolor_k3_planted_v24_e53_004.cnf` | 0.0343 | 0.0319 | 0.0279 | 0.0442 | 0.0345 | 0.0340 | 0.0310 | 0.0381 | +0.0002 | SAT | SAT |
| `cnf_training_extra__extra_cnf__graphcolor_k3_planted_v30_e66_005.cnf` | 0.0367 | 0.0404 | 0.0277 | 0.0432 | 0.0320 | 0.0355 | 0.0211 | 0.0404 | -0.0047 | SAT | SAT |
| `cnf_training_extra__extra_cnf__graphcolor_k3_planted_v36_e79_006.cnf` | 0.0417 | 0.0445 | 0.0305 | 0.0479 | 0.0259 | 0.0236 | 0.0211 | 0.0348 | -0.0158 | SAT | SAT |
| `cnf_training_extra__extra_cnf__graphcolor_k3_planted_v42_e92_007.cnf` | 0.0424 | 0.0420 | 0.0372 | 0.0455 | 0.0361 | 0.0342 | 0.0276 | 0.0480 | -0.0064 | SAT | SAT |
| `cnf_training_extra__extra_cnf__graphcolor_k3_planted_v50_e110_008.cnf` | 0.0387 | 0.0407 | 0.0296 | 0.0495 | 0.0337 | 0.0346 | 0.0263 | 0.0398 | -0.0050 | SAT | SAT |
| `cnf_training_extra__extra_cnf__graphcolor_k3_planted_v60_e132_009.cnf` | 0.0391 | 0.0362 | 0.0335 | 0.0487 | 0.0403 | 0.0394 | 0.0364 | 0.0467 | +0.0012 | SAT | SAT |
| `cnf_training_extra__extra_cnf__graphcolor_k3_planted_v72_e158_010.cnf` | 0.0436 | 0.0460 | 0.0311 | 0.0555 | 0.0317 | 0.0268 | 0.0258 | 0.0413 | -0.0120 | SAT | SAT |
| `cnf_training_extra__extra_cnf__horn_chain_len12_sat.cnf` | 0.0392 | 0.0410 | 0.0288 | 0.0446 | 0.0330 | 0.0383 | 0.0216 | 0.0400 | -0.0062 | SAT | SAT |
| `cnf_training_extra__extra_cnf__horn_chain_len12_unsat.cnf` | 0.0387 | 0.0433 | 0.0287 | 0.0448 | 0.0299 | 0.0281 | 0.0211 | 0.0428 | -0.0088 | UNSAT | UNSAT |
| `cnf_training_extra__extra_cnf__horn_chain_len16_sat.cnf` | 0.0421 | 0.0450 | 0.0299 | 0.0511 | 0.0341 | 0.0361 | 0.0261 | 0.0384 | -0.0080 | SAT | SAT |
| `cnf_training_extra__extra_cnf__horn_chain_len16_unsat.cnf` | 0.0304 | 0.0309 | 0.0267 | 0.0341 | 0.0316 | 0.0359 | 0.0215 | 0.0410 | +0.0012 | UNSAT | UNSAT |
| `cnf_training_extra__extra_cnf__horn_chain_len24_sat.cnf` | 0.0369 | 0.0354 | 0.0285 | 0.0479 | 0.0276 | 0.0260 | 0.0208 | 0.0381 | -0.0093 | SAT | SAT |
| `cnf_training_extra__extra_cnf__horn_chain_len24_unsat.cnf` | 0.0350 | 0.0360 | 0.0291 | 0.0383 | 0.0241 | 0.0209 | 0.0202 | 0.0353 | -0.0109 | UNSAT | UNSAT |
| `cnf_training_extra__extra_cnf__horn_chain_len32_sat.cnf` | 0.0361 | 0.0335 | 0.0310 | 0.0440 | 0.0273 | 0.0212 | 0.0204 | 0.0417 | -0.0087 | SAT | SAT |
| `cnf_training_extra__extra_cnf__horn_chain_len32_unsat.cnf` | 0.0464 | 0.0479 | 0.0393 | 0.0515 | 0.0302 | 0.0328 | 0.0219 | 0.0406 | -0.0161 | UNSAT | UNSAT |
| `cnf_training_extra__extra_cnf__horn_chain_len48_sat.cnf` | 0.0418 | 0.0452 | 0.0286 | 0.0494 | 0.0323 | 0.0341 | 0.0230 | 0.0373 | -0.0096 | SAT | SAT |
| `cnf_training_extra__extra_cnf__horn_chain_len48_unsat.cnf` | 0.0371 | 0.0389 | 0.0292 | 0.0471 | 0.0297 | 0.0242 | 0.0232 | 0.0425 | -0.0074 | UNSAT | UNSAT |
| `cnf_training_extra__extra_cnf__horn_chain_len64_sat.cnf` | 0.0357 | 0.0378 | 0.0306 | 0.0398 | 0.0221 | 0.0208 | 0.0201 | 0.0250 | -0.0136 | SAT | SAT |
| `cnf_training_extra__extra_cnf__horn_chain_len64_unsat.cnf` | 0.0412 | 0.0419 | 0.0288 | 0.0504 | 0.0300 | 0.0304 | 0.0228 | 0.0342 | -0.0112 | UNSAT | UNSAT |
| `cnf_training_extra__extra_cnf__horn_chain_len8_sat.cnf` | 0.0385 | 0.0383 | 0.0295 | 0.0479 | 0.0319 | 0.0359 | 0.0202 | 0.0465 | -0.0066 | SAT | SAT |
| `cnf_training_extra__extra_cnf__horn_chain_len8_unsat.cnf` | 0.0403 | 0.0425 | 0.0283 | 0.0457 | 0.0316 | 0.0333 | 0.0234 | 0.0416 | -0.0087 | UNSAT | UNSAT |
| `cnf_training_extra__extra_cnf__nqueens_2x2_unsat.cnf` | 0.0376 | 0.0365 | 0.0309 | 0.0474 | 0.0323 | 0.0352 | 0.0226 | 0.0413 | -0.0053 | UNSAT | UNSAT |
| `cnf_training_extra__extra_cnf__nqueens_3x3_unsat.cnf` | 0.0433 | 0.0426 | 0.0362 | 0.0519 | 0.0328 | 0.0326 | 0.0303 | 0.0360 | -0.0105 | UNSAT | UNSAT |
| `cnf_training_extra__extra_cnf__nqueens_4x4_sat.cnf` | 0.0431 | 0.0429 | 0.0347 | 0.0505 | 0.0297 | 0.0266 | 0.0227 | 0.0451 | -0.0134 | SAT | SAT |
| `cnf_training_extra__extra_cnf__nqueens_5x5_sat.cnf` | 0.0387 | 0.0418 | 0.0273 | 0.0448 | 0.0221 | 0.0217 | 0.0201 | 0.0243 | -0.0166 | SAT | SAT |
| `cnf_training_extra__extra_cnf__nqueens_6x6_sat.cnf` | 0.0388 | 0.0395 | 0.0329 | 0.0485 | 0.0279 | 0.0247 | 0.0234 | 0.0410 | -0.0109 | SAT | SAT |
| `cnf_training_extra__extra_cnf__nqueens_7x7_sat.cnf` | 0.0375 | 0.0378 | 0.0291 | 0.0488 | 0.0346 | 0.0354 | 0.0243 | 0.0405 | -0.0029 | SAT | SAT |
| `cnf_training_extra__extra_cnf__nqueens_8x8_sat.cnf` | 0.0466 | 0.0464 | 0.0445 | 0.0502 | 0.0341 | 0.0352 | 0.0243 | 0.0430 | -0.0124 | SAT | SAT |
| `cnf_training_extra__extra_cnf__nqueens_9x9_sat.cnf` | 0.0410 | 0.0376 | 0.0351 | 0.0505 | 0.0298 | 0.0282 | 0.0246 | 0.0375 | -0.0112 | SAT | SAT |
| `cnf_training_extra__extra_cnf__pigeonhole_php_10_into_9.cnf` | 0.0350 | 0.0302 | 0.0276 | 0.0474 | 0.0325 | 0.0325 | 0.0254 | 0.0425 | -0.0025 | UNSAT | UNSAT |
| `cnf_training_extra__extra_cnf__pigeonhole_php_4_into_3.cnf` | 0.0392 | 0.0401 | 0.0273 | 0.0464 | 0.0248 | 0.0208 | 0.0207 | 0.0332 | -0.0144 | UNSAT | UNSAT |
| `cnf_training_extra__extra_cnf__pigeonhole_php_5_into_4.cnf` | 0.0305 | 0.0282 | 0.0277 | 0.0400 | 0.0317 | 0.0329 | 0.0202 | 0.0400 | +0.0013 | UNSAT | UNSAT |
| `cnf_training_extra__extra_cnf__pigeonhole_php_6_into_5.cnf` | 0.0364 | 0.0394 | 0.0260 | 0.0461 | 0.0259 | 0.0239 | 0.0192 | 0.0336 | -0.0105 | UNSAT | UNSAT |
| `cnf_training_extra__extra_cnf__pigeonhole_php_7_into_6.cnf` | 0.0335 | 0.0290 | 0.0260 | 0.0461 | 0.0304 | 0.0303 | 0.0208 | 0.0399 | -0.0030 | UNSAT | UNSAT |
| `cnf_training_extra__extra_cnf__pigeonhole_php_8_into_7.cnf` | 0.0389 | 0.0405 | 0.0260 | 0.0464 | 0.0309 | 0.0325 | 0.0248 | 0.0365 | -0.0080 | UNSAT | UNSAT |
| `cnf_training_extra__extra_cnf__pigeonhole_php_9_into_8.cnf` | 0.0376 | 0.0434 | 0.0257 | 0.0465 | 0.0283 | 0.0242 | 0.0228 | 0.0371 | -0.0092 | UNSAT | UNSAT |
| `cnf_training_extra__extra_cnf__planted3sat_n20_m85_001.cnf` | 0.0367 | 0.0402 | 0.0282 | 0.0417 | 0.0284 | 0.0248 | 0.0195 | 0.0400 | -0.0083 | SAT | SAT |
| `cnf_training_extra__extra_cnf__planted3sat_n20_m85_002.cnf` | 0.0378 | 0.0392 | 0.0318 | 0.0438 | 0.0330 | 0.0331 | 0.0261 | 0.0399 | -0.0048 | SAT | SAT |
| `cnf_training_extra__extra_cnf__planted3sat_n20_m85_003.cnf` | 0.0385 | 0.0367 | 0.0330 | 0.0458 | 0.0264 | 0.0248 | 0.0209 | 0.0395 | -0.0120 | SAT | SAT |
| `cnf_training_extra__extra_cnf__planted3sat_n20_m85_004.cnf` | 0.0355 | 0.0319 | 0.0291 | 0.0446 | 0.0318 | 0.0314 | 0.0268 | 0.0358 | -0.0037 | SAT | SAT |
| `cnf_training_extra__extra_cnf__planted3sat_n20_m85_005.cnf` | 0.0348 | 0.0315 | 0.0272 | 0.0440 | 0.0297 | 0.0331 | 0.0225 | 0.0358 | -0.0051 | SAT | SAT |
| `cnf_training_extra__extra_cnf__planted3sat_n20_m85_006.cnf` | 0.0344 | 0.0344 | 0.0282 | 0.0417 | 0.0265 | 0.0240 | 0.0212 | 0.0328 | -0.0079 | SAT | SAT |
| `cnf_training_extra__extra_cnf__planted3sat_n20_m85_007.cnf` | 0.0354 | 0.0348 | 0.0303 | 0.0405 | 0.0250 | 0.0225 | 0.0204 | 0.0353 | -0.0104 | SAT | SAT |
| `cnf_training_extra__extra_cnf__planted3sat_n20_m85_008.cnf` | 0.0404 | 0.0400 | 0.0343 | 0.0500 | 0.0264 | 0.0224 | 0.0205 | 0.0344 | -0.0140 | SAT | SAT |
| `cnf_training_extra__extra_cnf__planted3sat_n20_m85_009.cnf` | 0.0362 | 0.0352 | 0.0274 | 0.0462 | 0.0352 | 0.0343 | 0.0303 | 0.0420 | -0.0009 | SAT | SAT |
| `cnf_training_extra__extra_cnf__planted3sat_n20_m85_010.cnf` | 0.0391 | 0.0373 | 0.0288 | 0.0478 | 0.0376 | 0.0353 | 0.0346 | 0.0446 | -0.0015 | SAT | SAT |
| `cnf_training_extra__extra_cnf__planted3sat_n30_m128_001.cnf` | 0.0391 | 0.0402 | 0.0316 | 0.0455 | 0.0242 | 0.0223 | 0.0212 | 0.0331 | -0.0149 | SAT | SAT |
| `cnf_training_extra__extra_cnf__planted3sat_n30_m128_002.cnf` | 0.0408 | 0.0410 | 0.0343 | 0.0464 | 0.0286 | 0.0239 | 0.0230 | 0.0372 | -0.0122 | SAT | SAT |
| `cnf_training_extra__extra_cnf__planted3sat_n30_m128_003.cnf` | 0.0355 | 0.0329 | 0.0295 | 0.0428 | 0.0257 | 0.0230 | 0.0224 | 0.0354 | -0.0097 | SAT | SAT |
| `cnf_training_extra__extra_cnf__planted3sat_n30_m128_004.cnf` | 0.0337 | 0.0315 | 0.0298 | 0.0410 | 0.0286 | 0.0283 | 0.0232 | 0.0339 | -0.0051 | SAT | SAT |
| `cnf_training_extra__extra_cnf__planted3sat_n30_m128_005.cnf` | 0.0447 | 0.0421 | 0.0303 | 0.0693 | 0.0303 | 0.0287 | 0.0223 | 0.0384 | -0.0144 | SAT | SAT |
| `cnf_training_extra__extra_cnf__planted3sat_n30_m128_006.cnf` | 0.0394 | 0.0371 | 0.0345 | 0.0456 | 0.0273 | 0.0251 | 0.0240 | 0.0329 | -0.0122 | SAT | SAT |
| `cnf_training_extra__extra_cnf__planted3sat_n30_m128_007.cnf` | 0.0358 | 0.0315 | 0.0309 | 0.0482 | 0.0364 | 0.0373 | 0.0281 | 0.0447 | +0.0006 | SAT | SAT |
| `cnf_training_extra__extra_cnf__planted3sat_n30_m128_008.cnf` | 0.0382 | 0.0355 | 0.0276 | 0.0545 | 0.0316 | 0.0312 | 0.0227 | 0.0385 | -0.0066 | SAT | SAT |
| `cnf_training_extra__extra_cnf__planted3sat_n30_m128_009.cnf` | 0.0422 | 0.0409 | 0.0297 | 0.0521 | 0.0292 | 0.0251 | 0.0223 | 0.0414 | -0.0130 | SAT | SAT |
| `cnf_training_extra__extra_cnf__planted3sat_n30_m128_010.cnf` | 0.0404 | 0.0410 | 0.0298 | 0.0528 | 0.0274 | 0.0233 | 0.0207 | 0.0359 | -0.0130 | SAT | SAT |
| `cnf_training_extra__extra_cnf__planted3sat_n40_m170_001.cnf` | 0.0408 | 0.0383 | 0.0320 | 0.0544 | 0.0250 | 0.0227 | 0.0208 | 0.0358 | -0.0158 | SAT | SAT |
| `cnf_training_extra__extra_cnf__planted3sat_n40_m170_002.cnf` | 0.0432 | 0.0439 | 0.0399 | 0.0456 | 0.0295 | 0.0277 | 0.0225 | 0.0407 | -0.0137 | SAT | SAT |
| `cnf_training_extra__extra_cnf__planted3sat_n40_m170_003.cnf` | 0.0371 | 0.0388 | 0.0293 | 0.0434 | 0.0321 | 0.0357 | 0.0246 | 0.0374 | -0.0050 | SAT | SAT |
| `cnf_training_extra__extra_cnf__planted3sat_n40_m170_004.cnf` | 0.0415 | 0.0418 | 0.0301 | 0.0529 | 0.0327 | 0.0334 | 0.0255 | 0.0367 | -0.0088 | SAT | SAT |
| `cnf_training_extra__extra_cnf__planted3sat_n40_m170_005.cnf` | 0.0418 | 0.0468 | 0.0298 | 0.0537 | 0.0332 | 0.0342 | 0.0248 | 0.0394 | -0.0085 | SAT | SAT |
| `cnf_training_extra__extra_cnf__planted3sat_n40_m170_006.cnf` | 0.0391 | 0.0423 | 0.0289 | 0.0507 | 0.0327 | 0.0328 | 0.0243 | 0.0396 | -0.0064 | SAT | SAT |
| `cnf_training_extra__extra_cnf__planted3sat_n40_m170_007.cnf` | 0.0417 | 0.0422 | 0.0341 | 0.0466 | 0.0297 | 0.0321 | 0.0228 | 0.0374 | -0.0120 | SAT | SAT |
| `cnf_training_extra__extra_cnf__planted3sat_n40_m170_008.cnf` | 0.0397 | 0.0443 | 0.0295 | 0.0471 | 0.0286 | 0.0270 | 0.0218 | 0.0362 | -0.0111 | SAT | SAT |
| `cnf_training_extra__extra_cnf__planted3sat_n40_m170_009.cnf` | 0.0382 | 0.0422 | 0.0294 | 0.0439 | 0.0332 | 0.0344 | 0.0213 | 0.0415 | -0.0050 | SAT | SAT |
| `cnf_training_extra__extra_cnf__planted3sat_n40_m170_010.cnf` | 0.0431 | 0.0478 | 0.0291 | 0.0489 | 0.0291 | 0.0279 | 0.0244 | 0.0344 | -0.0140 | SAT | SAT |
| `cnf_training_extra__extra_cnf__planted3sat_n60_m255_001.cnf` | 0.0404 | 0.0418 | 0.0339 | 0.0475 | 0.0363 | 0.0387 | 0.0247 | 0.0429 | -0.0041 | SAT | SAT |
| `cnf_training_extra__extra_cnf__planted3sat_n60_m255_002.cnf` | 0.0401 | 0.0409 | 0.0317 | 0.0459 | 0.0338 | 0.0349 | 0.0253 | 0.0379 | -0.0064 | SAT | SAT |
| `cnf_training_extra__extra_cnf__planted3sat_n60_m255_003.cnf` | 0.0428 | 0.0442 | 0.0340 | 0.0536 | 0.0332 | 0.0342 | 0.0257 | 0.0388 | -0.0096 | SAT | SAT |
| `cnf_training_extra__extra_cnf__planted3sat_n60_m255_004.cnf` | 0.0435 | 0.0453 | 0.0324 | 0.0484 | 0.0341 | 0.0355 | 0.0234 | 0.0403 | -0.0095 | SAT | SAT |
| `cnf_training_extra__extra_cnf__planted3sat_n60_m255_005.cnf` | 0.0417 | 0.0440 | 0.0327 | 0.0454 | 0.0319 | 0.0348 | 0.0225 | 0.0409 | -0.0098 | SAT | SAT |
| `cnf_training_extra__extra_cnf__planted3sat_n60_m255_006.cnf` | 0.0403 | 0.0421 | 0.0327 | 0.0449 | 0.0309 | 0.0303 | 0.0245 | 0.0411 | -0.0094 | SAT | SAT |
| `cnf_training_extra__extra_cnf__planted3sat_n60_m255_007.cnf` | 0.0449 | 0.0458 | 0.0409 | 0.0498 | 0.0394 | 0.0371 | 0.0351 | 0.0452 | -0.0055 | SAT | SAT |
| `cnf_training_extra__extra_cnf__planted3sat_n60_m255_008.cnf` | 0.0376 | 0.0367 | 0.0309 | 0.0479 | 0.0310 | 0.0289 | 0.0244 | 0.0416 | -0.0066 | SAT | SAT |
| `cnf_training_extra__extra_cnf__planted3sat_n80_m340_001.cnf` | 0.0453 | 0.0440 | 0.0400 | 0.0524 | 0.0412 | 0.0401 | 0.0337 | 0.0516 | -0.0041 | SAT | SAT |
| `cnf_training_extra__extra_cnf__planted3sat_n80_m340_002.cnf` | 0.0392 | 0.0373 | 0.0332 | 0.0497 | 0.0339 | 0.0307 | 0.0260 | 0.0450 | -0.0054 | SAT | SAT |
| `cnf_training_extra__extra_cnf__planted3sat_n80_m340_003.cnf` | 0.0374 | 0.0323 | 0.0317 | 0.0496 | 0.0309 | 0.0310 | 0.0237 | 0.0355 | -0.0066 | SAT | SAT |
| `cnf_training_extra__extra_cnf__planted3sat_n80_m340_004.cnf` | 0.0394 | 0.0398 | 0.0326 | 0.0454 | 0.0301 | 0.0332 | 0.0226 | 0.0361 | -0.0093 | SAT | SAT |
| `cnf_training_extra__extra_cnf__planted3sat_n80_m340_005.cnf` | 0.0416 | 0.0430 | 0.0340 | 0.0451 | 0.0336 | 0.0364 | 0.0227 | 0.0450 | -0.0079 | SAT | SAT |
| `cnf_training_extra__extra_cnf__planted3sat_n80_m340_006.cnf` | 0.0418 | 0.0438 | 0.0331 | 0.0451 | 0.0357 | 0.0347 | 0.0235 | 0.0462 | -0.0061 | SAT | SAT |
| `cnf_training_extra__extra_cnf__xor_parity_sat_n18_eq18_w3_001.cnf` | 0.0401 | 0.0451 | 0.0298 | 0.0485 | 0.0335 | 0.0344 | 0.0233 | 0.0399 | -0.0067 | SAT | SAT |
| `cnf_training_extra__extra_cnf__xor_parity_sat_n24_eq24_w3_002.cnf` | 0.0335 | 0.0318 | 0.0270 | 0.0393 | 0.0342 | 0.0337 | 0.0236 | 0.0406 | +0.0007 | SAT | SAT |
| `cnf_training_extra__extra_cnf__xor_parity_sat_n30_eq30_w3_003.cnf` | 0.0358 | 0.0402 | 0.0267 | 0.0414 | 0.0319 | 0.0338 | 0.0218 | 0.0434 | -0.0039 | SAT | SAT |
| `cnf_training_extra__extra_cnf__xor_parity_sat_n32_eq20_w4_007.cnf` | 0.0393 | 0.0450 | 0.0281 | 0.0470 | 0.0348 | 0.0372 | 0.0220 | 0.0390 | -0.0045 | SAT | SAT |
| `cnf_training_extra__extra_cnf__xor_parity_sat_n40_eq35_w3_004.cnf` | 0.0357 | 0.0346 | 0.0272 | 0.0467 | 0.0353 | 0.0381 | 0.0218 | 0.0441 | -0.0005 | SAT | SAT |
| `cnf_training_extra__extra_cnf__xor_parity_sat_n48_eq28_w4_008.cnf` | 0.0412 | 0.0410 | 0.0377 | 0.0467 | 0.0371 | 0.0376 | 0.0273 | 0.0451 | -0.0041 | SAT | SAT |
| `cnf_training_extra__extra_cnf__xor_parity_sat_n60_eq45_w3_005.cnf` | 0.0384 | 0.0394 | 0.0277 | 0.0444 | 0.0330 | 0.0357 | 0.0230 | 0.0418 | -0.0054 | SAT | SAT |
| `cnf_training_extra__extra_cnf__xor_parity_sat_n80_eq55_w3_006.cnf` | 0.0389 | 0.0399 | 0.0283 | 0.0444 | 0.0320 | 0.0333 | 0.0235 | 0.0442 | -0.0069 | SAT | SAT |
| `cnf_training_extra__extra_cnf__xor_parity_unsat_n18_eq12_w3_001.cnf` | 0.0345 | 0.0356 | 0.0282 | 0.0374 | 0.0342 | 0.0305 | 0.0243 | 0.0456 | -0.0003 | UNSAT | UNSAT |
| `cnf_training_extra__extra_cnf__xor_parity_unsat_n24_eq16_w3_002.cnf` | 0.0420 | 0.0472 | 0.0294 | 0.0516 | 0.0317 | 0.0292 | 0.0250 | 0.0446 | -0.0103 | UNSAT | UNSAT |
| `cnf_training_extra__extra_cnf__xor_parity_unsat_n30_eq20_w3_003.cnf` | 0.0400 | 0.0398 | 0.0310 | 0.0521 | 0.0323 | 0.0301 | 0.0201 | 0.0442 | -0.0077 | UNSAT | UNSAT |
| `cnf_training_extra__extra_cnf__xor_parity_unsat_n32_eq18_w4_006.cnf` | 0.0392 | 0.0424 | 0.0269 | 0.0495 | 0.0342 | 0.0328 | 0.0285 | 0.0404 | -0.0051 | UNSAT | UNSAT |
| `cnf_training_extra__extra_cnf__xor_parity_unsat_n40_eq24_w3_004.cnf` | 0.0452 | 0.0417 | 0.0373 | 0.0548 | 0.0330 | 0.0303 | 0.0283 | 0.0411 | -0.0122 | UNSAT | UNSAT |
| `cnf_training_extra__extra_cnf__xor_parity_unsat_n60_eq32_w3_005.cnf` | 0.0401 | 0.0407 | 0.0299 | 0.0499 | 0.0267 | 0.0234 | 0.0216 | 0.0333 | -0.0135 | UNSAT | UNSAT |
| `large__test_1.cnf` | 0.0469 | 0.0469 | 0.0402 | 0.0551 | 0.0365 | 0.0344 | 0.0336 | 0.0423 | -0.0104 | SAT | SAT |
| `large__test_10.cnf` | 1.5866 | 1.5906 | 1.5474 | 1.6368 | 0.8534 | 0.8479 | 0.8267 | 0.8968 | -0.7332 | UNSAT | UNSAT |
| `large__test_2.cnf` | 0.0440 | 0.0458 | 0.0343 | 0.0549 | 0.0369 | 0.0404 | 0.0283 | 0.0429 | -0.0071 | SAT | SAT |
| `large__test_3.cnf` | 0.2817 | 0.2738 | 0.2731 | 0.2950 | 0.2759 | 0.2728 | 0.2594 | 0.2931 | -0.0058 | UNSAT | UNSAT |
| `large__test_4.cnf` | 0.2411 | 0.2404 | 0.2269 | 0.2533 | 0.2350 | 0.2301 | 0.2150 | 0.2515 | -0.0062 | UNSAT | UNSAT |
| `large__test_5.cnf` | 0.0428 | 0.0434 | 0.0368 | 0.0509 | 0.0397 | 0.0394 | 0.0340 | 0.0456 | -0.0031 | SAT | SAT |
| `large__test_6.cnf` | 11.6822 | 11.7274 | 11.3121 | 11.9699 | 3.3346 | 3.3402 | 3.2296 | 3.4137 | -8.3476 | UNSAT | UNSAT |
| `large__test_7.cnf` | 0.0522 | 0.0560 | 0.0437 | 0.0576 | 0.0486 | 0.0481 | 0.0418 | 0.0537 | -0.0036 | SAT | SAT |
| `large__test_8.cnf` | 0.3017 | 0.3036 | 0.2814 | 0.3276 | 1.6169 | 1.6081 | 1.5763 | 1.6950 | +1.3152 | SAT | SAT |
| `large__test_9.cnf` | 0.0515 | 0.0515 | 0.0405 | 0.0645 | 0.0380 | 0.0379 | 0.0312 | 0.0442 | -0.0135 | SAT | SAT |
| `medium__test_1.cnf` | 0.0469 | 0.0486 | 0.0363 | 0.0526 | 0.0422 | 0.0421 | 0.0282 | 0.0517 | -0.0047 | UNSAT | UNSAT |
| `medium__test_10.cnf` | 0.0454 | 0.0490 | 0.0333 | 0.0518 | 0.0421 | 0.0431 | 0.0306 | 0.0477 | -0.0033 | UNSAT | UNSAT |
| `medium__test_2.cnf` | 0.0462 | 0.0491 | 0.0354 | 0.0560 | 0.0361 | 0.0389 | 0.0266 | 0.0436 | -0.0101 | UNSAT | UNSAT |
| `medium__test_3.cnf` | 0.6682 | 0.6664 | 0.6545 | 0.6882 | 0.4754 | 0.4752 | 0.4543 | 0.4919 | -0.1928 | UNSAT | UNSAT |
| `medium__test_4.cnf` | 1.6447 | 1.6344 | 1.6078 | 1.7092 | 0.8491 | 0.8458 | 0.8225 | 0.8719 | -0.7956 | UNSAT | UNSAT |
| `medium__test_5.cnf` | 0.0461 | 0.0477 | 0.0378 | 0.0532 | 0.0400 | 0.0386 | 0.0308 | 0.0483 | -0.0061 | UNSAT | UNSAT |
| `medium__test_6.cnf` | 0.0413 | 0.0431 | 0.0341 | 0.0466 | 0.0361 | 0.0406 | 0.0268 | 0.0442 | -0.0052 | UNSAT | UNSAT |
| `medium__test_7.cnf` | 0.0431 | 0.0451 | 0.0368 | 0.0480 | 0.0340 | 0.0343 | 0.0261 | 0.0461 | -0.0091 | UNSAT | UNSAT |
| `medium__test_8.cnf` | 0.0408 | 0.0440 | 0.0317 | 0.0469 | 0.0334 | 0.0340 | 0.0239 | 0.0453 | -0.0074 | SAT | SAT |
| `medium__test_9.cnf` | 0.0402 | 0.0452 | 0.0297 | 0.0464 | 0.0359 | 0.0373 | 0.0273 | 0.0435 | -0.0043 | SAT | SAT |
| `satlib_more__aim-100-1_6-no-1.cnf` | 0.0361 | 0.0337 | 0.0302 | 0.0430 | 0.0351 | 0.0349 | 0.0231 | 0.0429 | -0.0010 | UNSAT | UNSAT |
| `satlib_more__aim-100-1_6-no-2.cnf` | 0.0398 | 0.0410 | 0.0329 | 0.0483 | 0.0371 | 0.0400 | 0.0257 | 0.0428 | -0.0027 | UNSAT | UNSAT |
| `satlib_more__aim-100-1_6-yes1-1.cnf` | 0.0391 | 0.0351 | 0.0326 | 0.0502 | 0.0319 | 0.0334 | 0.0246 | 0.0366 | -0.0071 | SAT | SAT |
| `satlib_more__aim-100-1_6-yes1-2.cnf` | 0.0412 | 0.0392 | 0.0336 | 0.0504 | 0.0357 | 0.0368 | 0.0253 | 0.0405 | -0.0055 | SAT | SAT |
| `satlib_more__flat75-1.cnf` | 0.0375 | 0.0351 | 0.0341 | 0.0452 | 0.0345 | 0.0299 | 0.0252 | 0.0462 | -0.0030 | SAT | SAT |
| `satlib_more__flat75-10.cnf` | 0.0500 | 0.0499 | 0.0402 | 0.0590 | 0.0444 | 0.0445 | 0.0424 | 0.0456 | -0.0056 | SAT | SAT |
| `satlib_more__jnh1.cnf` | 0.0534 | 0.0541 | 0.0404 | 0.0635 | 0.0376 | 0.0342 | 0.0314 | 0.0484 | -0.0159 | SAT | SAT |
| `satlib_more__jnh10.cnf` | 0.0449 | 0.0402 | 0.0371 | 0.0561 | 0.0391 | 0.0343 | 0.0323 | 0.0494 | -0.0058 | UNSAT | UNSAT |
| `satlib_more__uf125-01.cnf` | 0.0470 | 0.0398 | 0.0390 | 0.0590 | 0.0318 | 0.0294 | 0.0288 | 0.0376 | -0.0152 | SAT | SAT |
| `satlib_more__uf125-010.cnf` | 0.0557 | 0.0524 | 0.0485 | 0.0662 | 0.0877 | 0.0902 | 0.0815 | 0.0917 | +0.0320 | SAT | SAT |
| `satlib_more__uf150-01.cnf` | 0.0623 | 0.0636 | 0.0484 | 0.0712 | 0.0542 | 0.0533 | 0.0489 | 0.0604 | -0.0081 | SAT | SAT |
| `satlib_more__uuf125-01.cnf` | 0.1197 | 0.1208 | 0.1149 | 0.1234 | 0.0972 | 0.0975 | 0.0918 | 0.1006 | -0.0226 | UNSAT | UNSAT |
| `satlib_more__uuf125-010.cnf` | 0.1684 | 0.1653 | 0.1600 | 0.1787 | 0.1438 | 0.1446 | 0.1298 | 0.1574 | -0.0246 | UNSAT | UNSAT |
| `satlib_more__uuf150-01.cnf` | 0.4193 | 0.4085 | 0.3948 | 0.4570 | 0.3498 | 0.3410 | 0.3392 | 0.3710 | -0.0695 | UNSAT | UNSAT |
| `satlib_subset__dubois20.cnf` | 0.0390 | 0.0375 | 0.0289 | 0.0529 | 0.0344 | 0.0357 | 0.0254 | 0.0394 | -0.0046 | UNSAT | UNSAT |
| `satlib_subset__dubois21.cnf` | 0.0396 | 0.0415 | 0.0294 | 0.0481 | 0.0310 | 0.0295 | 0.0211 | 0.0387 | -0.0087 | UNSAT | UNSAT |
| `satlib_subset__flat50-1.cnf` | 0.0382 | 0.0416 | 0.0300 | 0.0454 | 0.0292 | 0.0285 | 0.0253 | 0.0354 | -0.0090 | SAT | SAT |
| `satlib_subset__flat50-10.cnf` | 0.0343 | 0.0316 | 0.0283 | 0.0497 | 0.0376 | 0.0371 | 0.0297 | 0.0453 | +0.0032 | SAT | SAT |
| `satlib_subset__hole10.cnf` | 0.0379 | 0.0374 | 0.0353 | 0.0413 | 0.0322 | 0.0335 | 0.0225 | 0.0371 | -0.0057 | UNSAT | UNSAT |
| `satlib_subset__hole8.cnf` | 0.0386 | 0.0411 | 0.0294 | 0.0468 | 0.0273 | 0.0265 | 0.0199 | 0.0346 | -0.0113 | UNSAT | UNSAT |
| `satlib_subset__uf100-01.cnf` | 0.0645 | 0.0656 | 0.0587 | 0.0698 | 0.0618 | 0.0625 | 0.0504 | 0.0706 | -0.0027 | SAT | SAT |
| `satlib_subset__uf100-010.cnf` | 0.0459 | 0.0472 | 0.0361 | 0.0502 | 0.0391 | 0.0440 | 0.0249 | 0.0457 | -0.0068 | SAT | SAT |
| `satlib_subset__uuf100-01.cnf` | 0.0584 | 0.0607 | 0.0493 | 0.0645 | 0.0579 | 0.0575 | 0.0434 | 0.0669 | -0.0005 | UNSAT | UNSAT |
| `satlib_subset__uuf100-010.cnf` | 0.0715 | 0.0724 | 0.0635 | 0.0795 | 0.0659 | 0.0620 | 0.0547 | 0.0804 | -0.0056 | UNSAT | UNSAT |
| `small__test_1.cnf` | 0.0438 | 0.0429 | 0.0415 | 0.0487 | 0.0284 | 0.0225 | 0.0220 | 0.0439 | -0.0154 | SAT | SAT |
| `small__test_10.cnf` | 0.0490 | 0.0498 | 0.0437 | 0.0519 | 0.0313 | 0.0300 | 0.0232 | 0.0410 | -0.0176 | UNSAT | UNSAT |
| `small__test_2.cnf` | 0.0360 | 0.0370 | 0.0317 | 0.0409 | 0.0357 | 0.0368 | 0.0228 | 0.0449 | -0.0003 | SAT | SAT |
| `small__test_3.cnf` | 0.0389 | 0.0436 | 0.0293 | 0.0454 | 0.0358 | 0.0349 | 0.0338 | 0.0411 | -0.0031 | SAT | SAT |
| `small__test_4.cnf` | 0.0471 | 0.0440 | 0.0422 | 0.0595 | 0.0361 | 0.0341 | 0.0334 | 0.0425 | -0.0110 | UNSAT | UNSAT |
| `small__test_5.cnf` | 0.0341 | 0.0292 | 0.0283 | 0.0437 | 0.0314 | 0.0328 | 0.0220 | 0.0355 | -0.0027 | SAT | SAT |
| `small__test_6.cnf` | 0.0336 | 0.0311 | 0.0266 | 0.0430 | 0.0334 | 0.0329 | 0.0325 | 0.0355 | -0.0002 | SAT | SAT |
| `small__test_7.cnf` | 0.0388 | 0.0409 | 0.0299 | 0.0465 | 0.0339 | 0.0360 | 0.0217 | 0.0412 | -0.0049 | SAT | SAT |
| `small__test_8.cnf` | 0.0417 | 0.0415 | 0.0292 | 0.0547 | 0.0367 | 0.0353 | 0.0324 | 0.0451 | -0.0050 | UNSAT | UNSAT |
| `small__test_9.cnf` | 0.0381 | 0.0371 | 0.0311 | 0.0509 | 0.0315 | 0.0362 | 0.0228 | 0.0380 | -0.0067 | SAT | SAT |
| `special__dense.cnf` | 0.1328 | 0.1330 | 0.1317 | 0.1338 | 0.1267 | 0.1284 | 0.1183 | 0.1361 | -0.0061 | UNSAT | UNSAT |
| `special__easy.cnf` | 0.0388 | 0.0347 | 0.0303 | 0.0477 | 0.0322 | 0.0326 | 0.0258 | 0.0395 | -0.0066 | SAT | SAT |
| `special__hard.cnf` | 7.8371 | 7.8367 | 7.5602 | 8.0568 | 2.5353 | 2.5419 | 2.4750 | 2.5711 | -5.3018 | UNSAT | UNSAT |
| `special__pigeonhole.cnf` | 0.0353 | 0.0315 | 0.0287 | 0.0429 | 0.0327 | 0.0362 | 0.0233 | 0.0411 | -0.0026 | UNSAT | UNSAT |
| `special__tseitin.cnf` | 0.0378 | 0.0400 | 0.0294 | 0.0472 | 0.0307 | 0.0356 | 0.0221 | 0.0382 | -0.0070 | UNSAT | UNSAT |
