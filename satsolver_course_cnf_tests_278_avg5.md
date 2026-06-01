# SAT Solver Course CNF Tests Avg5 Benchmark

Generated: 2026-05-31T22:49:39
Dataset: `course_cnf_tests scratch set, 278 CNF files`
Source benchmark output: `/tmp/satsolver_course278_avg5.txt`
Solver: `satsolver`
Mode: `cli`
CLI script: `/home/doomguy/Desktop/sat/satsolver/satsolver.py`
Python executable: `/usr/bin/python`
Repeats: `5`
Bruteforce var limit: `16`
Metric note: `avg5 total` is `measured total / 5`, i.e. the mean runtime over five CLI runs per case. `median total` is the benchmark harness representative median sum.
Note: Restored old baseline artifact. This run excludes `cnf_training_complex__complex_cnf_hard__mycielski_iter4_color5_unsat.cnf`, matching the original 278-case benchmark set.

## Overall

| cases | solved | errors | SAT | UNSAT | avg5 total s | median total s | avg/case s | median/case s | max median-case s | measured total s | wall clock s |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 278 | 278 | 0 | 157 | 121 | 26.7588 | 26.3869 | 0.0963 | 0.0293 | 3.4581 | 133.7938 | 143.3749 |

## Folder Summary

| folder | cases | solved | errors | SAT | UNSAT | avg5 total s | median total s | avg/case s | median/case s | max median-case s | measured total s |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| `.` | 278 | 278 | 0 | 157 | 121 | 26.7588 | 26.3869 | 0.0963 | 0.0293 | 3.4581 | 133.7938 |

## Slowest Cases By Avg5

| case | result | vars | clauses | avg5 s | median s | best s | samples | validation |
|---|---|---:|---:|---:|---:|---:|---|---|
| `large__test_6.cnf` | UNSAT | 271 | 1393 | 3.4833 | 3.4581 | 3.4106 | `[3.5009, 3.4106, 3.6070, 3.4581, 3.4401]` | valid UNSAT (format checked) |
| `special__hard.cnf` | UNSAT | 200 | 850 | 2.6175 | 2.5953 | 2.5664 | `[2.5953, 2.6456, 2.5664, 2.6878, 2.5924]` | valid UNSAT (format checked) |
| `cnf_training_complex__complex_cnf_hard__planted3sat_balanced_n260_m1108_seed1.cnf` | SAT | 260 | 1108 | 1.4830 | 1.4818 | 1.4607 | `[1.4979, 1.4607, 1.4738, 1.5010, 1.4818]` | valid SAT |
| `cnf_training_complex__complex_cnf_hard__ramsey_R3_4_n11_unsat.cnf` | UNSAT | 55 | 495 | 1.1462 | 1.1508 | 1.0958 | `[1.1679, 1.1508, 1.1475, 1.0958, 1.1691]` | valid UNSAT (format checked) |
| `cnf_training_complex__complex_cnf_moderate__ramsey_R3_4_n10_unsat.cnf` | UNSAT | 45 | 330 | 1.1343 | 1.1424 | 1.0897 | `[1.1712, 1.1747, 1.0934, 1.1424, 1.0897]` | valid UNSAT (format checked) |
| `cnf_training_complex__complex_cnf_moderate__ramsey_R3_4_n9_unsat.cnf` | UNSAT | 36 | 210 | 1.1314 | 1.1292 | 1.0938 | `[1.1292, 1.1273, 1.0938, 1.1656, 1.1413]` | valid UNSAT (format checked) |
| `cnf_training_complex__complex_cnf_moderate__planted3sat_balanced_n200_m852_seed2.cnf` | SAT | 200 | 852 | 0.9317 | 0.9324 | 0.8870 | `[0.9001, 0.8870, 0.9324, 0.9583, 0.9808]` | valid SAT |
| `medium__test_4.cnf` | UNSAT | 191 | 886 | 0.8882 | 0.8970 | 0.8534 | `[0.9225, 0.8665, 0.9016, 0.8970, 0.8534]` | valid UNSAT (format checked) |
| `cnf_training_complex__complex_cnf_hard__planted3sat_balanced_n320_m1363_seed1.cnf` | SAT | 320 | 1363 | 0.8874 | 0.9003 | 0.8569 | `[0.9107, 0.9043, 0.9003, 0.8569, 0.8646]` | valid SAT |
| `large__test_10.cnf` | UNSAT | 229 | 1280 | 0.8546 | 0.8468 | 0.8234 | `[0.8234, 0.8387, 0.8468, 0.8618, 0.9023]` | valid UNSAT (format checked) |
| `cnf_training_complex__complex_cnf_hard__planted3sat_balanced_n260_m1108_seed2.cnf` | SAT | 260 | 1108 | 0.6234 | 0.6161 | 0.5905 | `[0.6161, 0.6127, 0.6570, 0.6407, 0.5905]` | valid SAT |
| `medium__test_3.cnf` | UNSAT | 172 | 774 | 0.5169 | 0.5134 | 0.4974 | `[0.5063, 0.4974, 0.5134, 0.5308, 0.5365]` | valid UNSAT (format checked) |
| `cnf_training_complex__complex_cnf_moderate__planted3sat_balanced_n200_m852_seed1.cnf` | SAT | 200 | 852 | 0.4726 | 0.4639 | 0.4551 | `[0.5063, 0.4639, 0.4551, 0.4614, 0.4764]` | valid SAT |
| `satlib_more__uuf150-01.cnf` | UNSAT | 150 | 645 | 0.3745 | 0.3602 | 0.3413 | `[0.3711, 0.4556, 0.3602, 0.3413, 0.3443]` | valid UNSAT (format checked) |
| `cnf_training_complex__complex_cnf_hard__planted3sat_balanced_n400_m1704_seed1.cnf` | SAT | 400 | 1704 | 0.3234 | 0.3240 | 0.3067 | `[0.3166, 0.3067, 0.3330, 0.3367, 0.3240]` | valid SAT |
| `cnf_training_complex__complex_cnf_hard__planted3sat_balanced_n320_m1363_seed2.cnf` | SAT | 320 | 1363 | 0.2918 | 0.2955 | 0.2724 | `[0.2794, 0.2955, 0.3124, 0.2724, 0.2993]` | valid SAT |
| `large__test_3.cnf` | UNSAT | 227 | 1460 | 0.2853 | 0.2826 | 0.2764 | `[0.2991, 0.2826, 0.2812, 0.2764, 0.2872]` | valid UNSAT (format checked) |
| `cnf_training_complex__complex_cnf_moderate__mycielski_iter3_color4_unsat.cnf` | UNSAT | 92 | 445 | 0.2624 | 0.2665 | 0.2436 | `[0.2759, 0.2718, 0.2436, 0.2542, 0.2665]` | valid UNSAT (format checked) |
| `large__test_4.cnf` | UNSAT | 219 | 1363 | 0.2553 | 0.2523 | 0.2365 | `[0.2535, 0.2365, 0.2935, 0.2408, 0.2523]` | valid UNSAT (format checked) |
| `cnf_training_complex__complex_cnf_moderate__xor_sparse_sat_n128_eq165_w3-4_seed3.cnf` | SAT | 128 | 1000 | 0.2438 | 0.2452 | 0.2234 | `[0.2234, 0.2526, 0.2534, 0.2444, 0.2452]` | valid SAT |

## All Cases

| case | result | ok | vars | clauses | avg5 s | median s | best s | samples | validation |
|---|---|---:|---:|---:|---:|---:|---:|---|---|
| `cnf_training_complex__complex_cnf_hard__planted3sat_balanced_n260_m1108_seed1.cnf` | SAT | yes | 260 | 1108 | 1.4830 | 1.4818 | 1.4607 | `[1.4979, 1.4607, 1.4738, 1.5010, 1.4818]` | valid SAT |
| `cnf_training_complex__complex_cnf_hard__planted3sat_balanced_n260_m1108_seed2.cnf` | SAT | yes | 260 | 1108 | 0.6234 | 0.6161 | 0.5905 | `[0.6161, 0.6127, 0.6570, 0.6407, 0.5905]` | valid SAT |
| `cnf_training_complex__complex_cnf_hard__planted3sat_balanced_n320_m1363_seed1.cnf` | SAT | yes | 320 | 1363 | 0.8874 | 0.9003 | 0.8569 | `[0.9107, 0.9043, 0.9003, 0.8569, 0.8646]` | valid SAT |
| `cnf_training_complex__complex_cnf_hard__planted3sat_balanced_n320_m1363_seed2.cnf` | SAT | yes | 320 | 1363 | 0.2918 | 0.2955 | 0.2724 | `[0.2794, 0.2955, 0.3124, 0.2724, 0.2993]` | valid SAT |
| `cnf_training_complex__complex_cnf_hard__planted3sat_balanced_n400_m1704_seed1.cnf` | SAT | yes | 400 | 1704 | 0.3234 | 0.3240 | 0.3067 | `[0.3166, 0.3067, 0.3330, 0.3367, 0.3240]` | valid SAT |
| `cnf_training_complex__complex_cnf_hard__ramsey_R3_4_n11_unsat.cnf` | UNSAT | yes | 55 | 495 | 1.1462 | 1.1508 | 1.0958 | `[1.1679, 1.1508, 1.1475, 1.0958, 1.1691]` | valid UNSAT (format checked) |
| `cnf_training_complex__complex_cnf_hard__tseitin_deg3_v100_sat.cnf` | SAT | yes | 150 | 400 | 0.0324 | 0.0345 | 0.0266 | `[0.0345, 0.0279, 0.0362, 0.0369, 0.0266]` | valid SAT |
| `cnf_training_complex__complex_cnf_hard__tseitin_deg3_v100_unsat.cnf` | UNSAT | yes | 150 | 400 | 0.0254 | 0.0255 | 0.0248 | `[0.0253, 0.0255, 0.0262, 0.0256, 0.0248]` | valid UNSAT (format checked) |
| `cnf_training_complex__complex_cnf_hard__tseitin_deg3_v120_sat.cnf` | SAT | yes | 180 | 480 | 0.0296 | 0.0291 | 0.0275 | `[0.0275, 0.0301, 0.0326, 0.0291, 0.0286]` | valid SAT |
| `cnf_training_complex__complex_cnf_hard__tseitin_deg3_v120_unsat.cnf` | UNSAT | yes | 180 | 480 | 0.0312 | 0.0346 | 0.0228 | `[0.0354, 0.0387, 0.0228, 0.0244, 0.0346]` | valid UNSAT (format checked) |
| `cnf_training_complex__complex_cnf_hard__tseitin_deg3_v160_sat.cnf` | SAT | yes | 240 | 640 | 0.0461 | 0.0457 | 0.0410 | `[0.0410, 0.0480, 0.0457, 0.0524, 0.0433]` | valid SAT |
| `cnf_training_complex__complex_cnf_hard__tseitin_deg3_v160_unsat.cnf` | UNSAT | yes | 240 | 640 | 0.0273 | 0.0266 | 0.0236 | `[0.0245, 0.0341, 0.0236, 0.0266, 0.0277]` | valid UNSAT (format checked) |
| `cnf_training_complex__complex_cnf_hard__tseitin_deg4_v64_sat.cnf` | SAT | yes | 128 | 512 | 0.0510 | 0.0451 | 0.0432 | `[0.0432, 0.0525, 0.0439, 0.0701, 0.0451]` | valid SAT |
| `cnf_training_complex__complex_cnf_hard__tseitin_deg4_v64_unsat.cnf` | UNSAT | yes | 128 | 512 | 0.0368 | 0.0411 | 0.0270 | `[0.0411, 0.0270, 0.0287, 0.0420, 0.0451]` | valid UNSAT (format checked) |
| `cnf_training_complex__complex_cnf_hard__tseitin_deg4_v96_sat.cnf` | SAT | yes | 192 | 768 | 0.0391 | 0.0414 | 0.0336 | `[0.0414, 0.0342, 0.0436, 0.0427, 0.0336]` | valid SAT |
| `cnf_training_complex__complex_cnf_hard__tseitin_deg4_v96_unsat.cnf` | UNSAT | yes | 192 | 768 | 0.0275 | 0.0253 | 0.0245 | `[0.0245, 0.0253, 0.0363, 0.0263, 0.0252]` | valid UNSAT (format checked) |
| `cnf_training_complex__complex_cnf_hard__vdw_2color_k4_n45_unsat.cnf` | UNSAT | yes | 45 | 630 | 0.0540 | 0.0515 | 0.0449 | `[0.0566, 0.0449, 0.0515, 0.0477, 0.0693]` | valid UNSAT (format checked) |
| `cnf_training_complex__complex_cnf_hard__vdw_2color_k4_n60_unsat.cnf` | UNSAT | yes | 60 | 1140 | 0.0559 | 0.0558 | 0.0498 | `[0.0623, 0.0584, 0.0558, 0.0534, 0.0498]` | valid UNSAT (format checked) |
| `cnf_training_complex__complex_cnf_hard__xor_sparse_unsat_n100_eq135_w3-4_seed4.cnf` | UNSAT | yes | 100 | 828 | 0.0283 | 0.0270 | 0.0252 | `[0.0270, 0.0342, 0.0278, 0.0270, 0.0252]` | valid UNSAT (format checked) |
| `cnf_training_complex__complex_cnf_hard__xor_sparse_unsat_n140_eq190_w3-4_seed5.cnf` | UNSAT | yes | 140 | 1104 | 0.0334 | 0.0270 | 0.0261 | `[0.0270, 0.0267, 0.0497, 0.0261, 0.0376]` | valid UNSAT (format checked) |
| `cnf_training_complex__complex_cnf_hard__xor_sparse_unsat_n180_eq250_w3-4_seed6.cnf` | UNSAT | yes | 180 | 1544 | 0.0380 | 0.0379 | 0.0317 | `[0.0379, 0.0317, 0.0375, 0.0447, 0.0383]` | valid UNSAT (format checked) |
| `cnf_training_complex__complex_cnf_moderate__mycielski_iter2_color3_unsat.cnf` | UNSAT | yes | 33 | 104 | 0.0327 | 0.0307 | 0.0242 | `[0.0490, 0.0323, 0.0307, 0.0242, 0.0275]` | valid UNSAT (format checked) |
| `cnf_training_complex__complex_cnf_moderate__mycielski_iter2_color4_sat.cnf` | SAT | yes | 44 | 157 | 0.0281 | 0.0255 | 0.0248 | `[0.0252, 0.0248, 0.0255, 0.0260, 0.0388]` | valid SAT |
| `cnf_training_complex__complex_cnf_moderate__mycielski_iter3_color4_unsat.cnf` | UNSAT | yes | 92 | 445 | 0.2624 | 0.2665 | 0.2436 | `[0.2759, 0.2718, 0.2436, 0.2542, 0.2665]` | valid UNSAT (format checked) |
| `cnf_training_complex__complex_cnf_moderate__mycielski_iter3_color5_sat.cnf` | SAT | yes | 115 | 608 | 0.0372 | 0.0358 | 0.0346 | `[0.0380, 0.0346, 0.0355, 0.0358, 0.0422]` | valid SAT |
| `cnf_training_complex__complex_cnf_moderate__ordering_no_minimum_n10.cnf` | UNSAT | yes | 45 | 730 | 0.0491 | 0.0490 | 0.0461 | `[0.0490, 0.0526, 0.0497, 0.0483, 0.0461]` | valid UNSAT (format checked) |
| `cnf_training_complex__complex_cnf_moderate__ordering_no_minimum_n12.cnf` | UNSAT | yes | 66 | 1332 | 0.0631 | 0.0633 | 0.0542 | `[0.0570, 0.0672, 0.0542, 0.0633, 0.0738]` | valid UNSAT (format checked) |
| `cnf_training_complex__complex_cnf_moderate__ordering_no_minimum_n8.cnf` | UNSAT | yes | 28 | 344 | 0.0358 | 0.0383 | 0.0285 | `[0.0285, 0.0398, 0.0298, 0.0383, 0.0428]` | valid UNSAT (format checked) |
| `cnf_training_complex__complex_cnf_moderate__orthogonal_latin_squares_order3_sat.cnf` | SAT | yes | 81 | 1998 | 0.0401 | 0.0357 | 0.0325 | `[0.0357, 0.0479, 0.0325, 0.0497, 0.0349]` | valid SAT |
| `cnf_training_complex__complex_cnf_moderate__pigeonhole_php_11_into_10.cnf` | UNSAT | yes | 110 | 1056 | 0.0302 | 0.0260 | 0.0233 | `[0.0260, 0.0259, 0.0372, 0.0233, 0.0386]` | valid UNSAT (format checked) |
| `cnf_training_complex__complex_cnf_moderate__pigeonhole_php_13_into_12.cnf` | UNSAT | yes | 156 | 1807 | 0.0259 | 0.0258 | 0.0239 | `[0.0258, 0.0239, 0.0250, 0.0291, 0.0259]` | valid UNSAT (format checked) |
| `cnf_training_complex__complex_cnf_moderate__pigeonhole_php_9_into_8.cnf` | UNSAT | yes | 72 | 549 | 0.0288 | 0.0275 | 0.0228 | `[0.0236, 0.0325, 0.0275, 0.0228, 0.0375]` | valid UNSAT (format checked) |
| `cnf_training_complex__complex_cnf_moderate__planted3sat_balanced_n120_m511_seed1.cnf` | SAT | yes | 120 | 511 | 0.0355 | 0.0290 | 0.0271 | `[0.0286, 0.0271, 0.0529, 0.0290, 0.0401]` | valid SAT |
| `cnf_training_complex__complex_cnf_moderate__planted3sat_balanced_n120_m511_seed2.cnf` | SAT | yes | 120 | 511 | 0.0316 | 0.0306 | 0.0270 | `[0.0320, 0.0270, 0.0306, 0.0389, 0.0296]` | valid SAT |
| `cnf_training_complex__complex_cnf_moderate__planted3sat_balanced_n160_m682_seed1.cnf` | SAT | yes | 160 | 682 | 0.0406 | 0.0391 | 0.0357 | `[0.0424, 0.0357, 0.0389, 0.0468, 0.0391]` | valid SAT |
| `cnf_training_complex__complex_cnf_moderate__planted3sat_balanced_n160_m682_seed2.cnf` | SAT | yes | 160 | 682 | 0.0392 | 0.0401 | 0.0338 | `[0.0386, 0.0428, 0.0406, 0.0401, 0.0338]` | valid SAT |
| `cnf_training_complex__complex_cnf_moderate__planted3sat_balanced_n200_m852_seed1.cnf` | SAT | yes | 200 | 852 | 0.4726 | 0.4639 | 0.4551 | `[0.5063, 0.4639, 0.4551, 0.4614, 0.4764]` | valid SAT |
| `cnf_training_complex__complex_cnf_moderate__planted3sat_balanced_n200_m852_seed2.cnf` | SAT | yes | 200 | 852 | 0.9317 | 0.9324 | 0.8870 | `[0.9001, 0.8870, 0.9324, 0.9583, 0.9808]` | valid SAT |
| `cnf_training_complex__complex_cnf_moderate__ramsey_R3_3_n6_unsat.cnf` | UNSAT | yes | 15 | 40 | 0.0337 | 0.0328 | 0.0295 | `[0.0295, 0.0391, 0.0325, 0.0344, 0.0328]` | valid UNSAT (brute-force checked) |
| `cnf_training_complex__complex_cnf_moderate__ramsey_R3_3_n7_unsat.cnf` | UNSAT | yes | 21 | 70 | 0.0270 | 0.0273 | 0.0211 | `[0.0273, 0.0316, 0.0318, 0.0231, 0.0211]` | valid UNSAT (format checked) |
| `cnf_training_complex__complex_cnf_moderate__ramsey_R3_3_n8_unsat.cnf` | UNSAT | yes | 28 | 112 | 0.0233 | 0.0222 | 0.0219 | `[0.0273, 0.0219, 0.0222, 0.0220, 0.0232]` | valid UNSAT (format checked) |
| `cnf_training_complex__complex_cnf_moderate__ramsey_R3_4_n10_unsat.cnf` | UNSAT | yes | 45 | 330 | 1.1343 | 1.1424 | 1.0897 | `[1.1712, 1.1747, 1.0934, 1.1424, 1.0897]` | valid UNSAT (format checked) |
| `cnf_training_complex__complex_cnf_moderate__ramsey_R3_4_n9_unsat.cnf` | UNSAT | yes | 36 | 210 | 1.1314 | 1.1292 | 1.0938 | `[1.1292, 1.1273, 1.0938, 1.1656, 1.1413]` | valid UNSAT (format checked) |
| `cnf_training_complex__complex_cnf_moderate__tseitin_deg3_v40_sat.cnf` | SAT | yes | 60 | 160 | 0.0319 | 0.0337 | 0.0224 | `[0.0351, 0.0439, 0.0241, 0.0337, 0.0224]` | valid SAT |
| `cnf_training_complex__complex_cnf_moderate__tseitin_deg3_v40_unsat.cnf` | UNSAT | yes | 60 | 160 | 0.0343 | 0.0372 | 0.0228 | `[0.0342, 0.0395, 0.0228, 0.0377, 0.0372]` | valid UNSAT (format checked) |
| `cnf_training_complex__complex_cnf_moderate__tseitin_deg3_v60_sat.cnf` | SAT | yes | 90 | 240 | 0.0257 | 0.0259 | 0.0234 | `[0.0256, 0.0259, 0.0270, 0.0234, 0.0266]` | valid SAT |
| `cnf_training_complex__complex_cnf_moderate__tseitin_deg3_v60_unsat.cnf` | UNSAT | yes | 90 | 240 | 0.0283 | 0.0259 | 0.0236 | `[0.0328, 0.0236, 0.0336, 0.0259, 0.0255]` | valid UNSAT (format checked) |
| `cnf_training_complex__complex_cnf_moderate__tseitin_deg3_v80_sat.cnf` | SAT | yes | 120 | 320 | 0.0311 | 0.0276 | 0.0253 | `[0.0253, 0.0405, 0.0359, 0.0276, 0.0263]` | valid SAT |
| `cnf_training_complex__complex_cnf_moderate__tseitin_deg3_v80_unsat.cnf` | UNSAT | yes | 120 | 320 | 0.0324 | 0.0333 | 0.0215 | `[0.0350, 0.0312, 0.0411, 0.0333, 0.0215]` | valid UNSAT (format checked) |
| `cnf_training_complex__complex_cnf_moderate__vdw_2color_k3_n16_unsat.cnf` | UNSAT | yes | 16 | 112 | 0.0244 | 0.0219 | 0.0212 | `[0.0212, 0.0212, 0.0342, 0.0233, 0.0219]` | valid UNSAT (brute-force checked) |
| `cnf_training_complex__complex_cnf_moderate__vdw_2color_k3_n9_unsat.cnf` | UNSAT | yes | 9 | 32 | 0.0247 | 0.0225 | 0.0215 | `[0.0235, 0.0224, 0.0215, 0.0225, 0.0335]` | valid UNSAT (brute-force checked) |
| `cnf_training_complex__complex_cnf_moderate__vdw_2color_k4_n35_unsat.cnf` | UNSAT | yes | 35 | 374 | 0.0519 | 0.0525 | 0.0470 | `[0.0574, 0.0470, 0.0539, 0.0488, 0.0525]` | valid UNSAT (format checked) |
| `cnf_training_complex__complex_cnf_moderate__xor_sparse_sat_n128_eq165_w3-4_seed3.cnf` | SAT | yes | 128 | 1000 | 0.2438 | 0.2452 | 0.2234 | `[0.2234, 0.2526, 0.2534, 0.2444, 0.2452]` | valid SAT |
| `cnf_training_complex__complex_cnf_moderate__xor_sparse_sat_n64_eq82_w3_seed1.cnf` | SAT | yes | 64 | 328 | 0.0388 | 0.0391 | 0.0258 | `[0.0477, 0.0387, 0.0425, 0.0258, 0.0391]` | valid SAT |
| `cnf_training_complex__complex_cnf_moderate__xor_sparse_sat_n96_eq125_w3_seed2.cnf` | SAT | yes | 96 | 500 | 0.0336 | 0.0315 | 0.0293 | `[0.0355, 0.0293, 0.0315, 0.0423, 0.0294]` | valid SAT |
| `cnf_training_complex__complex_cnf_moderate__xor_sparse_unsat_n48_eq62_w3_seed1.cnf` | UNSAT | yes | 48 | 248 | 0.0241 | 0.0255 | 0.0211 | `[0.0258, 0.0255, 0.0257, 0.0211, 0.0222]` | valid UNSAT (format checked) |
| `cnf_training_complex__complex_cnf_moderate__xor_sparse_unsat_n64_eq86_w3_seed2.cnf` | UNSAT | yes | 64 | 344 | 0.0260 | 0.0260 | 0.0224 | `[0.0324, 0.0263, 0.0230, 0.0260, 0.0224]` | valid UNSAT (format checked) |
| `cnf_training_complex__complex_cnf_moderate__xor_sparse_unsat_n80_eq108_w3-4_seed3.cnf` | UNSAT | yes | 80 | 608 | 0.0289 | 0.0291 | 0.0249 | `[0.0249, 0.0354, 0.0295, 0.0258, 0.0291]` | valid UNSAT (format checked) |
| `cnf_training_complex__complex_cnf_stress__tseitin_deg3_v240_unsat.cnf` | UNSAT | yes | 360 | 960 | 0.0289 | 0.0286 | 0.0268 | `[0.0308, 0.0286, 0.0302, 0.0280, 0.0268]` | valid UNSAT (format checked) |
| `cnf_training_complex__complex_cnf_stress__tseitin_deg4_v160_unsat.cnf` | UNSAT | yes | 320 | 1280 | 0.0313 | 0.0310 | 0.0266 | `[0.0310, 0.0392, 0.0278, 0.0266, 0.0322]` | valid UNSAT (format checked) |
| `cnf_training_complex__complex_cnf_stress__xor_sparse_unsat_n240_eq330_w3-4_seed1.cnf` | UNSAT | yes | 240 | 1996 | 0.0343 | 0.0305 | 0.0287 | `[0.0291, 0.0489, 0.0344, 0.0287, 0.0305]` | valid UNSAT (format checked) |
| `cnf_training_extra__extra_cnf__cardinality_exactly_one_sat_g10_s5_004.cnf` | SAT | yes | 50 | 110 | 0.0275 | 0.0267 | 0.0209 | `[0.0267, 0.0342, 0.0209, 0.0347, 0.0212]` | valid SAT |
| `cnf_training_extra__extra_cnf__cardinality_exactly_one_sat_g12_s6_005.cnf` | SAT | yes | 72 | 192 | 0.0230 | 0.0214 | 0.0211 | `[0.0211, 0.0212, 0.0214, 0.0263, 0.0249]` | valid SAT |
| `cnf_training_extra__extra_cnf__cardinality_exactly_one_sat_g16_s4_006.cnf` | SAT | yes | 64 | 112 | 0.0263 | 0.0270 | 0.0224 | `[0.0282, 0.0270, 0.0224, 0.0274, 0.0267]` | valid SAT |
| `cnf_training_extra__extra_cnf__cardinality_exactly_one_sat_g4_s4_001.cnf` | SAT | yes | 16 | 28 | 0.0316 | 0.0348 | 0.0229 | `[0.0390, 0.0229, 0.0348, 0.0264, 0.0349]` | valid SAT |
| `cnf_training_extra__extra_cnf__cardinality_exactly_one_sat_g5_s5_002.cnf` | SAT | yes | 25 | 55 | 0.0215 | 0.0213 | 0.0209 | `[0.0213, 0.0216, 0.0209, 0.0211, 0.0225]` | valid SAT |
| `cnf_training_extra__extra_cnf__cardinality_exactly_one_sat_g8_s4_003.cnf` | SAT | yes | 32 | 56 | 0.0272 | 0.0220 | 0.0209 | `[0.0215, 0.0220, 0.0377, 0.0339, 0.0209]` | valid SAT |
| `cnf_training_extra__extra_cnf__cardinality_exactly_one_unsat_g10_s6_005.cnf` | UNSAT | yes | 60 | 162 | 0.0242 | 0.0212 | 0.0207 | `[0.0208, 0.0207, 0.0311, 0.0212, 0.0272]` | valid UNSAT (format checked) |
| `cnf_training_extra__extra_cnf__cardinality_exactly_one_unsat_g12_s4_006.cnf` | UNSAT | yes | 48 | 86 | 0.0258 | 0.0238 | 0.0210 | `[0.0210, 0.0238, 0.0253, 0.0230, 0.0357]` | valid UNSAT (format checked) |
| `cnf_training_extra__extra_cnf__cardinality_exactly_one_unsat_g3_s4_001.cnf` | UNSAT | yes | 12 | 23 | 0.0277 | 0.0236 | 0.0233 | `[0.0435, 0.0233, 0.0247, 0.0236, 0.0233]` | valid UNSAT (brute-force checked) |
| `cnf_training_extra__extra_cnf__cardinality_exactly_one_unsat_g4_s5_002.cnf` | UNSAT | yes | 20 | 46 | 0.0249 | 0.0262 | 0.0214 | `[0.0280, 0.0262, 0.0214, 0.0216, 0.0273]` | valid UNSAT (format checked) |
| `cnf_training_extra__extra_cnf__cardinality_exactly_one_unsat_g6_s4_003.cnf` | UNSAT | yes | 24 | 44 | 0.0301 | 0.0310 | 0.0210 | `[0.0310, 0.0330, 0.0301, 0.0210, 0.0353]` | valid UNSAT (format checked) |
| `cnf_training_extra__extra_cnf__cardinality_exactly_one_unsat_g8_s5_004.cnf` | UNSAT | yes | 40 | 90 | 0.0218 | 0.0221 | 0.0210 | `[0.0221, 0.0210, 0.0228, 0.0222, 0.0210]` | valid UNSAT (format checked) |
| `cnf_training_extra__extra_cnf__equivalence_chain_len10_sat.cnf` | SAT | yes | 10 | 20 | 0.0251 | 0.0208 | 0.0205 | `[0.0208, 0.0205, 0.0207, 0.0410, 0.0227]` | valid SAT |
| `cnf_training_extra__extra_cnf__equivalence_chain_len10_unsat.cnf` | UNSAT | yes | 10 | 20 | 0.0249 | 0.0236 | 0.0200 | `[0.0263, 0.0338, 0.0209, 0.0200, 0.0236]` | valid UNSAT (brute-force checked) |
| `cnf_training_extra__extra_cnf__equivalence_chain_len120_sat.cnf` | SAT | yes | 120 | 240 | 0.0290 | 0.0264 | 0.0239 | `[0.0316, 0.0264, 0.0375, 0.0256, 0.0239]` | valid SAT |
| `cnf_training_extra__extra_cnf__equivalence_chain_len120_unsat.cnf` | UNSAT | yes | 120 | 240 | 0.0292 | 0.0271 | 0.0230 | `[0.0230, 0.0252, 0.0271, 0.0353, 0.0353]` | valid UNSAT (format checked) |
| `cnf_training_extra__extra_cnf__equivalence_chain_len20_sat.cnf` | SAT | yes | 20 | 40 | 0.0271 | 0.0259 | 0.0243 | `[0.0289, 0.0243, 0.0259, 0.0254, 0.0312]` | valid SAT |
| `cnf_training_extra__extra_cnf__equivalence_chain_len20_unsat.cnf` | UNSAT | yes | 20 | 40 | 0.0316 | 0.0305 | 0.0243 | `[0.0464, 0.0316, 0.0305, 0.0250, 0.0243]` | valid UNSAT (format checked) |
| `cnf_training_extra__extra_cnf__equivalence_chain_len40_sat.cnf` | SAT | yes | 40 | 80 | 0.0299 | 0.0298 | 0.0249 | `[0.0322, 0.0298, 0.0249, 0.0348, 0.0277]` | valid SAT |
| `cnf_training_extra__extra_cnf__equivalence_chain_len40_unsat.cnf` | UNSAT | yes | 40 | 80 | 0.0280 | 0.0284 | 0.0222 | `[0.0284, 0.0316, 0.0324, 0.0252, 0.0222]` | valid UNSAT (format checked) |
| `cnf_training_extra__extra_cnf__equivalence_chain_len80_sat.cnf` | SAT | yes | 80 | 160 | 0.0296 | 0.0299 | 0.0216 | `[0.0299, 0.0391, 0.0316, 0.0216, 0.0259]` | valid SAT |
| `cnf_training_extra__extra_cnf__equivalence_chain_len80_unsat.cnf` | UNSAT | yes | 80 | 160 | 0.0298 | 0.0235 | 0.0224 | `[0.0228, 0.0224, 0.0441, 0.0235, 0.0361]` | valid UNSAT (format checked) |
| `cnf_training_extra__extra_cnf__exact_random3sat_sat_n10_m49_008.cnf` | SAT | yes | 10 | 49 | 0.0315 | 0.0338 | 0.0210 | `[0.0352, 0.0288, 0.0210, 0.0384, 0.0338]` | valid SAT |
| `cnf_training_extra__extra_cnf__exact_random3sat_sat_n11_m40_017.cnf` | SAT | yes | 11 | 40 | 0.0335 | 0.0323 | 0.0314 | `[0.0314, 0.0370, 0.0323, 0.0323, 0.0346]` | valid SAT |
| `cnf_training_extra__extra_cnf__exact_random3sat_sat_n11_m46_001.cnf` | SAT | yes | 11 | 46 | 0.0282 | 0.0274 | 0.0207 | `[0.0274, 0.0337, 0.0225, 0.0207, 0.0368]` | valid SAT |
| `cnf_training_extra__extra_cnf__exact_random3sat_sat_n12_m43_012.cnf` | SAT | yes | 12 | 43 | 0.0311 | 0.0258 | 0.0223 | `[0.0474, 0.0350, 0.0258, 0.0223, 0.0250]` | valid SAT |
| `cnf_training_extra__extra_cnf__exact_random3sat_sat_n12_m47_006.cnf` | SAT | yes | 12 | 47 | 0.0302 | 0.0317 | 0.0211 | `[0.0336, 0.0297, 0.0317, 0.0211, 0.0349]` | valid SAT |
| `cnf_training_extra__extra_cnf__exact_random3sat_sat_n12_m47_013.cnf` | SAT | yes | 12 | 47 | 0.0294 | 0.0265 | 0.0205 | `[0.0412, 0.0242, 0.0205, 0.0265, 0.0347]` | valid SAT |
| `cnf_training_extra__extra_cnf__exact_random3sat_sat_n13_m47_011.cnf` | SAT | yes | 13 | 47 | 0.0377 | 0.0395 | 0.0282 | `[0.0282, 0.0395, 0.0418, 0.0389, 0.0399]` | valid SAT |
| `cnf_training_extra__extra_cnf__exact_random3sat_sat_n13_m64_004.cnf` | SAT | yes | 13 | 64 | 0.0314 | 0.0333 | 0.0212 | `[0.0366, 0.0300, 0.0333, 0.0359, 0.0212]` | valid SAT |
| `cnf_training_extra__extra_cnf__exact_random3sat_sat_n14_m50_015.cnf` | SAT | yes | 14 | 50 | 0.0269 | 0.0238 | 0.0221 | `[0.0221, 0.0241, 0.0235, 0.0238, 0.0408]` | valid SAT |
| `cnf_training_extra__extra_cnf__exact_random3sat_sat_n15_m68_014.cnf` | SAT | yes | 15 | 68 | 0.0355 | 0.0388 | 0.0227 | `[0.0349, 0.0388, 0.0408, 0.0403, 0.0227]` | valid SAT |
| `cnf_training_extra__extra_cnf__exact_random3sat_sat_n16_m62_016.cnf` | SAT | yes | 16 | 62 | 0.0330 | 0.0326 | 0.0248 | `[0.0410, 0.0299, 0.0248, 0.0367, 0.0326]` | valid SAT |
| `cnf_training_extra__extra_cnf__exact_random3sat_sat_n16_m72_003.cnf` | SAT | yes | 16 | 72 | 0.0283 | 0.0295 | 0.0245 | `[0.0245, 0.0298, 0.0264, 0.0295, 0.0314]` | valid SAT |
| `cnf_training_extra__extra_cnf__exact_random3sat_sat_n8_m31_007.cnf` | SAT | yes | 8 | 31 | 0.0279 | 0.0282 | 0.0226 | `[0.0343, 0.0227, 0.0282, 0.0317, 0.0226]` | valid SAT |
| `cnf_training_extra__extra_cnf__exact_random3sat_sat_n8_m31_009.cnf` | SAT | yes | 8 | 31 | 0.0318 | 0.0327 | 0.0271 | `[0.0327, 0.0344, 0.0271, 0.0277, 0.0370]` | valid SAT |
| `cnf_training_extra__extra_cnf__exact_random3sat_sat_n8_m36_002.cnf` | SAT | yes | 8 | 36 | 0.0255 | 0.0264 | 0.0221 | `[0.0267, 0.0264, 0.0221, 0.0256, 0.0266]` | valid SAT |
| `cnf_training_extra__extra_cnf__exact_random3sat_sat_n8_m36_005.cnf` | SAT | yes | 8 | 36 | 0.0279 | 0.0261 | 0.0248 | `[0.0283, 0.0351, 0.0261, 0.0248, 0.0253]` | valid SAT |
| `cnf_training_extra__extra_cnf__exact_random3sat_sat_n9_m32_018.cnf` | SAT | yes | 9 | 32 | 0.0262 | 0.0244 | 0.0208 | `[0.0208, 0.0371, 0.0247, 0.0242, 0.0244]` | valid SAT |
| `cnf_training_extra__extra_cnf__exact_random3sat_sat_n9_m38_010.cnf` | SAT | yes | 9 | 38 | 0.0234 | 0.0236 | 0.0203 | `[0.0203, 0.0206, 0.0236, 0.0251, 0.0277]` | valid SAT |
| `cnf_training_extra__extra_cnf__exact_random3sat_unsat_n10_m49_015.cnf` | UNSAT | yes | 10 | 49 | 0.0298 | 0.0318 | 0.0230 | `[0.0318, 0.0323, 0.0234, 0.0230, 0.0384]` | valid UNSAT (brute-force checked) |
| `cnf_training_extra__extra_cnf__exact_random3sat_unsat_n11_m54_012.cnf` | UNSAT | yes | 11 | 54 | 0.0238 | 0.0232 | 0.0227 | `[0.0229, 0.0227, 0.0261, 0.0232, 0.0239]` | valid UNSAT (brute-force checked) |
| `cnf_training_extra__extra_cnf__exact_random3sat_unsat_n12_m64_007.cnf` | UNSAT | yes | 12 | 64 | 0.0294 | 0.0264 | 0.0237 | `[0.0237, 0.0369, 0.0242, 0.0357, 0.0264]` | valid UNSAT (brute-force checked) |
| `cnf_training_extra__extra_cnf__exact_random3sat_unsat_n12_m64_013.cnf` | UNSAT | yes | 12 | 64 | 0.0304 | 0.0342 | 0.0213 | `[0.0360, 0.0213, 0.0342, 0.0241, 0.0366]` | valid UNSAT (brute-force checked) |
| `cnf_training_extra__extra_cnf__exact_random3sat_unsat_n13_m69_006.cnf` | UNSAT | yes | 13 | 69 | 0.0301 | 0.0251 | 0.0241 | `[0.0377, 0.0251, 0.0241, 0.0389, 0.0247]` | valid UNSAT (brute-force checked) |
| `cnf_training_extra__extra_cnf__exact_random3sat_unsat_n13_m69_010.cnf` | UNSAT | yes | 13 | 69 | 0.0295 | 0.0262 | 0.0228 | `[0.0237, 0.0360, 0.0262, 0.0389, 0.0228]` | valid UNSAT (brute-force checked) |
| `cnf_training_extra__extra_cnf__exact_random3sat_unsat_n14_m74_017.cnf` | UNSAT | yes | 14 | 74 | 0.0339 | 0.0340 | 0.0235 | `[0.0340, 0.0416, 0.0235, 0.0337, 0.0368]` | valid UNSAT (brute-force checked) |
| `cnf_training_extra__extra_cnf__exact_random3sat_unsat_n15_m68_011.cnf` | UNSAT | yes | 15 | 68 | 0.0287 | 0.0285 | 0.0239 | `[0.0250, 0.0367, 0.0285, 0.0293, 0.0239]` | valid UNSAT (brute-force checked) |
| `cnf_training_extra__extra_cnf__exact_random3sat_unsat_n15_m68_018.cnf` | UNSAT | yes | 15 | 68 | 0.0272 | 0.0254 | 0.0234 | `[0.0254, 0.0369, 0.0234, 0.0238, 0.0262]` | valid UNSAT (brute-force checked) |
| `cnf_training_extra__extra_cnf__exact_random3sat_unsat_n15_m80_014.cnf` | UNSAT | yes | 15 | 80 | 0.0301 | 0.0335 | 0.0235 | `[0.0251, 0.0336, 0.0335, 0.0235, 0.0349]` | valid UNSAT (brute-force checked) |
| `cnf_training_extra__extra_cnf__exact_random3sat_unsat_n16_m78_005.cnf` | UNSAT | yes | 16 | 78 | 0.0353 | 0.0371 | 0.0252 | `[0.0252, 0.0433, 0.0333, 0.0374, 0.0371]` | valid UNSAT (brute-force checked) |
| `cnf_training_extra__extra_cnf__exact_random3sat_unsat_n16_m78_008.cnf` | UNSAT | yes | 16 | 78 | 0.0328 | 0.0353 | 0.0243 | `[0.0273, 0.0353, 0.0400, 0.0243, 0.0369]` | valid UNSAT (brute-force checked) |
| `cnf_training_extra__extra_cnf__exact_random3sat_unsat_n16_m85_002.cnf` | UNSAT | yes | 16 | 85 | 0.0342 | 0.0347 | 0.0271 | `[0.0347, 0.0344, 0.0393, 0.0271, 0.0354]` | valid UNSAT (brute-force checked) |
| `cnf_training_extra__extra_cnf__exact_random3sat_unsat_n16_m85_003.cnf` | UNSAT | yes | 16 | 85 | 0.0278 | 0.0253 | 0.0225 | `[0.0251, 0.0328, 0.0225, 0.0335, 0.0253]` | valid UNSAT (brute-force checked) |
| `cnf_training_extra__extra_cnf__exact_random3sat_unsat_n8_m31_016.cnf` | UNSAT | yes | 8 | 31 | 0.0338 | 0.0351 | 0.0238 | `[0.0356, 0.0351, 0.0406, 0.0238, 0.0341]` | valid UNSAT (brute-force checked) |
| `cnf_training_extra__extra_cnf__exact_random3sat_unsat_n8_m34_009.cnf` | UNSAT | yes | 8 | 34 | 0.0290 | 0.0296 | 0.0221 | `[0.0325, 0.0296, 0.0221, 0.0234, 0.0374]` | valid UNSAT (brute-force checked) |
| `cnf_training_extra__extra_cnf__exact_random3sat_unsat_n9_m38_004.cnf` | UNSAT | yes | 9 | 38 | 0.0285 | 0.0273 | 0.0222 | `[0.0347, 0.0222, 0.0273, 0.0312, 0.0271]` | valid UNSAT (brute-force checked) |
| `cnf_training_extra__extra_cnf__exact_random3sat_unsat_n9_m44_001.cnf` | UNSAT | yes | 9 | 44 | 0.0266 | 0.0250 | 0.0225 | `[0.0250, 0.0367, 0.0262, 0.0228, 0.0225]` | valid UNSAT (brute-force checked) |
| `cnf_training_extra__extra_cnf__graphcolor_k3_complete_K4_unsat.cnf` | UNSAT | yes | 12 | 34 | 0.0289 | 0.0254 | 0.0250 | `[0.0250, 0.0324, 0.0369, 0.0250, 0.0254]` | valid UNSAT (brute-force checked) |
| `cnf_training_extra__extra_cnf__graphcolor_k3_complete_K5_unsat.cnf` | UNSAT | yes | 15 | 50 | 0.0296 | 0.0305 | 0.0240 | `[0.0344, 0.0340, 0.0305, 0.0253, 0.0240]` | valid UNSAT (brute-force checked) |
| `cnf_training_extra__extra_cnf__graphcolor_k3_complete_K6_unsat.cnf` | UNSAT | yes | 18 | 69 | 0.0255 | 0.0230 | 0.0223 | `[0.0228, 0.0223, 0.0361, 0.0230, 0.0233]` | valid UNSAT (format checked) |
| `cnf_training_extra__extra_cnf__graphcolor_k3_planted_v12_e26_001.cnf` | SAT | yes | 36 | 126 | 0.0259 | 0.0250 | 0.0230 | `[0.0251, 0.0235, 0.0250, 0.0331, 0.0230]` | valid SAT |
| `cnf_training_extra__extra_cnf__graphcolor_k3_planted_v16_e35_002.cnf` | SAT | yes | 48 | 169 | 0.0295 | 0.0304 | 0.0221 | `[0.0304, 0.0358, 0.0231, 0.0221, 0.0363]` | valid SAT |
| `cnf_training_extra__extra_cnf__graphcolor_k3_planted_v20_e44_003.cnf` | SAT | yes | 60 | 212 | 0.0296 | 0.0287 | 0.0250 | `[0.0290, 0.0287, 0.0261, 0.0394, 0.0250]` | valid SAT |
| `cnf_training_extra__extra_cnf__graphcolor_k3_planted_v24_e53_004.cnf` | SAT | yes | 72 | 255 | 0.0333 | 0.0359 | 0.0255 | `[0.0255, 0.0359, 0.0405, 0.0274, 0.0373]` | valid SAT |
| `cnf_training_extra__extra_cnf__graphcolor_k3_planted_v30_e66_005.cnf` | SAT | yes | 90 | 318 | 0.0260 | 0.0249 | 0.0244 | `[0.0249, 0.0244, 0.0293, 0.0245, 0.0268]` | valid SAT |
| `cnf_training_extra__extra_cnf__graphcolor_k3_planted_v36_e79_006.cnf` | SAT | yes | 108 | 381 | 0.0325 | 0.0343 | 0.0254 | `[0.0343, 0.0365, 0.0402, 0.0260, 0.0254]` | valid SAT |
| `cnf_training_extra__extra_cnf__graphcolor_k3_planted_v42_e92_007.cnf` | SAT | yes | 126 | 444 | 0.0321 | 0.0314 | 0.0265 | `[0.0314, 0.0294, 0.0379, 0.0265, 0.0354]` | valid SAT |
| `cnf_training_extra__extra_cnf__graphcolor_k3_planted_v50_e110_008.cnf` | SAT | yes | 150 | 530 | 0.0374 | 0.0353 | 0.0285 | `[0.0345, 0.0285, 0.0353, 0.0501, 0.0388]` | valid SAT |
| `cnf_training_extra__extra_cnf__graphcolor_k3_planted_v60_e132_009.cnf` | SAT | yes | 180 | 636 | 0.0306 | 0.0289 | 0.0265 | `[0.0289, 0.0288, 0.0379, 0.0310, 0.0265]` | valid SAT |
| `cnf_training_extra__extra_cnf__graphcolor_k3_planted_v72_e158_010.cnf` | SAT | yes | 216 | 762 | 0.0387 | 0.0361 | 0.0304 | `[0.0361, 0.0445, 0.0487, 0.0304, 0.0338]` | valid SAT |
| `cnf_training_extra__extra_cnf__horn_chain_len12_sat.cnf` | SAT | yes | 12 | 12 | 0.0301 | 0.0260 | 0.0205 | `[0.0260, 0.0367, 0.0236, 0.0205, 0.0437]` | valid SAT |
| `cnf_training_extra__extra_cnf__horn_chain_len12_unsat.cnf` | UNSAT | yes | 12 | 13 | 0.0282 | 0.0258 | 0.0218 | `[0.0218, 0.0258, 0.0357, 0.0229, 0.0350]` | valid UNSAT (brute-force checked) |
| `cnf_training_extra__extra_cnf__horn_chain_len16_sat.cnf` | SAT | yes | 16 | 16 | 0.0380 | 0.0385 | 0.0358 | `[0.0375, 0.0385, 0.0358, 0.0391, 0.0389]` | valid SAT |
| `cnf_training_extra__extra_cnf__horn_chain_len16_unsat.cnf` | UNSAT | yes | 16 | 17 | 0.0287 | 0.0265 | 0.0224 | `[0.0255, 0.0340, 0.0350, 0.0265, 0.0224]` | valid UNSAT (brute-force checked) |
| `cnf_training_extra__extra_cnf__horn_chain_len24_sat.cnf` | SAT | yes | 24 | 24 | 0.0265 | 0.0231 | 0.0214 | `[0.0390, 0.0214, 0.0231, 0.0268, 0.0223]` | valid SAT |
| `cnf_training_extra__extra_cnf__horn_chain_len24_unsat.cnf` | UNSAT | yes | 24 | 25 | 0.0322 | 0.0284 | 0.0270 | `[0.0378, 0.0284, 0.0410, 0.0270, 0.0271]` | valid UNSAT (format checked) |
| `cnf_training_extra__extra_cnf__horn_chain_len32_sat.cnf` | SAT | yes | 32 | 32 | 0.0292 | 0.0232 | 0.0225 | `[0.0232, 0.0403, 0.0229, 0.0225, 0.0370]` | valid SAT |
| `cnf_training_extra__extra_cnf__horn_chain_len32_unsat.cnf` | UNSAT | yes | 32 | 33 | 0.0310 | 0.0324 | 0.0208 | `[0.0293, 0.0389, 0.0336, 0.0208, 0.0324]` | valid UNSAT (format checked) |
| `cnf_training_extra__extra_cnf__horn_chain_len48_sat.cnf` | SAT | yes | 48 | 48 | 0.0313 | 0.0304 | 0.0202 | `[0.0339, 0.0209, 0.0304, 0.0202, 0.0510]` | valid SAT |
| `cnf_training_extra__extra_cnf__horn_chain_len48_unsat.cnf` | UNSAT | yes | 48 | 49 | 0.0269 | 0.0216 | 0.0210 | `[0.0353, 0.0210, 0.0212, 0.0216, 0.0352]` | valid UNSAT (format checked) |
| `cnf_training_extra__extra_cnf__horn_chain_len64_sat.cnf` | SAT | yes | 64 | 64 | 0.0275 | 0.0242 | 0.0228 | `[0.0342, 0.0328, 0.0228, 0.0242, 0.0233]` | valid SAT |
| `cnf_training_extra__extra_cnf__horn_chain_len64_unsat.cnf` | UNSAT | yes | 64 | 65 | 0.0324 | 0.0319 | 0.0314 | `[0.0314, 0.0319, 0.0335, 0.0318, 0.0335]` | valid UNSAT (format checked) |
| `cnf_training_extra__extra_cnf__horn_chain_len8_sat.cnf` | SAT | yes | 8 | 8 | 0.0266 | 0.0248 | 0.0243 | `[0.0243, 0.0253, 0.0243, 0.0248, 0.0342]` | valid SAT |
| `cnf_training_extra__extra_cnf__horn_chain_len8_unsat.cnf` | UNSAT | yes | 8 | 9 | 0.0276 | 0.0267 | 0.0244 | `[0.0271, 0.0339, 0.0261, 0.0244, 0.0267]` | valid UNSAT (brute-force checked) |
| `cnf_training_extra__extra_cnf__nqueens_2x2_unsat.cnf` | UNSAT | yes | 4 | 8 | 0.0349 | 0.0345 | 0.0259 | `[0.0345, 0.0259, 0.0289, 0.0499, 0.0354]` | valid UNSAT (brute-force checked) |
| `cnf_training_extra__extra_cnf__nqueens_3x3_unsat.cnf` | UNSAT | yes | 9 | 31 | 0.0255 | 0.0241 | 0.0236 | `[0.0241, 0.0286, 0.0236, 0.0237, 0.0274]` | valid UNSAT (brute-force checked) |
| `cnf_training_extra__extra_cnf__nqueens_4x4_sat.cnf` | SAT | yes | 16 | 80 | 0.0302 | 0.0268 | 0.0261 | `[0.0268, 0.0356, 0.0263, 0.0261, 0.0361]` | valid SAT |
| `cnf_training_extra__extra_cnf__nqueens_5x5_sat.cnf` | SAT | yes | 25 | 165 | 0.0270 | 0.0264 | 0.0230 | `[0.0346, 0.0264, 0.0230, 0.0274, 0.0236]` | valid SAT |
| `cnf_training_extra__extra_cnf__nqueens_6x6_sat.cnf` | SAT | yes | 36 | 296 | 0.0283 | 0.0246 | 0.0237 | `[0.0237, 0.0246, 0.0384, 0.0305, 0.0242]` | valid SAT |
| `cnf_training_extra__extra_cnf__nqueens_7x7_sat.cnf` | SAT | yes | 49 | 483 | 0.0368 | 0.0386 | 0.0305 | `[0.0353, 0.0387, 0.0410, 0.0305, 0.0386]` | valid SAT |
| `cnf_training_extra__extra_cnf__nqueens_8x8_sat.cnf` | SAT | yes | 64 | 736 | 0.0340 | 0.0297 | 0.0269 | `[0.0275, 0.0269, 0.0297, 0.0395, 0.0463]` | valid SAT |
| `cnf_training_extra__extra_cnf__nqueens_9x9_sat.cnf` | SAT | yes | 81 | 1065 | 0.0365 | 0.0328 | 0.0282 | `[0.0292, 0.0282, 0.0455, 0.0468, 0.0328]` | valid SAT |
| `cnf_training_extra__extra_cnf__pigeonhole_php_10_into_9.cnf` | UNSAT | yes | 90 | 415 | 0.0280 | 0.0264 | 0.0247 | `[0.0267, 0.0366, 0.0264, 0.0258, 0.0247]` | valid UNSAT (format checked) |
| `cnf_training_extra__extra_cnf__pigeonhole_php_4_into_3.cnf` | UNSAT | yes | 12 | 22 | 0.0293 | 0.0243 | 0.0232 | `[0.0243, 0.0424, 0.0232, 0.0233, 0.0332]` | valid UNSAT (brute-force checked) |
| `cnf_training_extra__extra_cnf__pigeonhole_php_5_into_4.cnf` | UNSAT | yes | 20 | 45 | 0.0282 | 0.0262 | 0.0248 | `[0.0293, 0.0262, 0.0345, 0.0261, 0.0248]` | valid UNSAT (format checked) |
| `cnf_training_extra__extra_cnf__pigeonhole_php_6_into_5.cnf` | UNSAT | yes | 30 | 81 | 0.0285 | 0.0263 | 0.0233 | `[0.0233, 0.0265, 0.0428, 0.0263, 0.0237]` | valid UNSAT (format checked) |
| `cnf_training_extra__extra_cnf__pigeonhole_php_7_into_6.cnf` | UNSAT | yes | 42 | 133 | 0.0291 | 0.0276 | 0.0230 | `[0.0276, 0.0260, 0.0339, 0.0349, 0.0230]` | valid UNSAT (format checked) |
| `cnf_training_extra__extra_cnf__pigeonhole_php_8_into_7.cnf` | UNSAT | yes | 56 | 204 | 0.0290 | 0.0278 | 0.0234 | `[0.0345, 0.0278, 0.0353, 0.0234, 0.0239]` | valid UNSAT (format checked) |
| `cnf_training_extra__extra_cnf__pigeonhole_php_9_into_8.cnf` | UNSAT | yes | 72 | 297 | 0.0246 | 0.0246 | 0.0231 | `[0.0255, 0.0253, 0.0242, 0.0246, 0.0231]` | valid UNSAT (format checked) |
| `cnf_training_extra__extra_cnf__planted3sat_n20_m85_001.cnf` | SAT | yes | 20 | 85 | 0.0298 | 0.0269 | 0.0220 | `[0.0269, 0.0334, 0.0246, 0.0220, 0.0422]` | valid SAT |
| `cnf_training_extra__extra_cnf__planted3sat_n20_m85_002.cnf` | SAT | yes | 20 | 85 | 0.0343 | 0.0338 | 0.0215 | `[0.0269, 0.0338, 0.0410, 0.0215, 0.0481]` | valid SAT |
| `cnf_training_extra__extra_cnf__planted3sat_n20_m85_003.cnf` | SAT | yes | 20 | 85 | 0.0310 | 0.0269 | 0.0260 | `[0.0333, 0.0426, 0.0269, 0.0263, 0.0260]` | valid SAT |
| `cnf_training_extra__extra_cnf__planted3sat_n20_m85_004.cnf` | SAT | yes | 20 | 85 | 0.0261 | 0.0258 | 0.0227 | `[0.0258, 0.0273, 0.0227, 0.0228, 0.0317]` | valid SAT |
| `cnf_training_extra__extra_cnf__planted3sat_n20_m85_005.cnf` | SAT | yes | 20 | 85 | 0.0256 | 0.0221 | 0.0213 | `[0.0213, 0.0216, 0.0221, 0.0277, 0.0351]` | valid SAT |
| `cnf_training_extra__extra_cnf__planted3sat_n20_m85_006.cnf` | SAT | yes | 20 | 85 | 0.0241 | 0.0237 | 0.0220 | `[0.0255, 0.0261, 0.0220, 0.0233, 0.0237]` | valid SAT |
| `cnf_training_extra__extra_cnf__planted3sat_n20_m85_007.cnf` | SAT | yes | 20 | 85 | 0.0301 | 0.0261 | 0.0257 | `[0.0261, 0.0257, 0.0391, 0.0336, 0.0258]` | valid SAT |
| `cnf_training_extra__extra_cnf__planted3sat_n20_m85_008.cnf` | SAT | yes | 20 | 85 | 0.0240 | 0.0245 | 0.0224 | `[0.0245, 0.0225, 0.0224, 0.0252, 0.0256]` | valid SAT |
| `cnf_training_extra__extra_cnf__planted3sat_n20_m85_009.cnf` | SAT | yes | 20 | 85 | 0.0301 | 0.0262 | 0.0230 | `[0.0262, 0.0382, 0.0384, 0.0230, 0.0248]` | valid SAT |
| `cnf_training_extra__extra_cnf__planted3sat_n20_m85_010.cnf` | SAT | yes | 20 | 85 | 0.0260 | 0.0242 | 0.0234 | `[0.0338, 0.0242, 0.0234, 0.0239, 0.0246]` | valid SAT |
| `cnf_training_extra__extra_cnf__planted3sat_n30_m128_001.cnf` | SAT | yes | 30 | 128 | 0.0270 | 0.0245 | 0.0223 | `[0.0230, 0.0292, 0.0245, 0.0223, 0.0359]` | valid SAT |
| `cnf_training_extra__extra_cnf__planted3sat_n30_m128_002.cnf` | SAT | yes | 30 | 128 | 0.0271 | 0.0249 | 0.0228 | `[0.0228, 0.0234, 0.0375, 0.0249, 0.0269]` | valid SAT |
| `cnf_training_extra__extra_cnf__planted3sat_n30_m128_003.cnf` | SAT | yes | 30 | 128 | 0.0263 | 0.0267 | 0.0238 | `[0.0253, 0.0238, 0.0267, 0.0283, 0.0276]` | valid SAT |
| `cnf_training_extra__extra_cnf__planted3sat_n30_m128_004.cnf` | SAT | yes | 30 | 128 | 0.0265 | 0.0260 | 0.0250 | `[0.0270, 0.0254, 0.0292, 0.0250, 0.0260]` | valid SAT |
| `cnf_training_extra__extra_cnf__planted3sat_n30_m128_005.cnf` | SAT | yes | 30 | 128 | 0.0292 | 0.0253 | 0.0243 | `[0.0253, 0.0357, 0.0243, 0.0354, 0.0250]` | valid SAT |
| `cnf_training_extra__extra_cnf__planted3sat_n30_m128_006.cnf` | SAT | yes | 30 | 128 | 0.0334 | 0.0332 | 0.0262 | `[0.0415, 0.0262, 0.0306, 0.0332, 0.0355]` | valid SAT |
| `cnf_training_extra__extra_cnf__planted3sat_n30_m128_007.cnf` | SAT | yes | 30 | 128 | 0.0311 | 0.0303 | 0.0287 | `[0.0304, 0.0287, 0.0303, 0.0293, 0.0367]` | valid SAT |
| `cnf_training_extra__extra_cnf__planted3sat_n30_m128_008.cnf` | SAT | yes | 30 | 128 | 0.0274 | 0.0256 | 0.0233 | `[0.0256, 0.0233, 0.0241, 0.0306, 0.0336]` | valid SAT |
| `cnf_training_extra__extra_cnf__planted3sat_n30_m128_009.cnf` | SAT | yes | 30 | 128 | 0.0310 | 0.0296 | 0.0210 | `[0.0455, 0.0233, 0.0355, 0.0296, 0.0210]` | valid SAT |
| `cnf_training_extra__extra_cnf__planted3sat_n30_m128_010.cnf` | SAT | yes | 30 | 128 | 0.0293 | 0.0318 | 0.0221 | `[0.0338, 0.0318, 0.0229, 0.0360, 0.0221]` | valid SAT |
| `cnf_training_extra__extra_cnf__planted3sat_n40_m170_001.cnf` | SAT | yes | 40 | 170 | 0.0280 | 0.0267 | 0.0230 | `[0.0348, 0.0267, 0.0230, 0.0323, 0.0233]` | valid SAT |
| `cnf_training_extra__extra_cnf__planted3sat_n40_m170_002.cnf` | SAT | yes | 40 | 170 | 0.0311 | 0.0308 | 0.0229 | `[0.0267, 0.0348, 0.0402, 0.0229, 0.0308]` | valid SAT |
| `cnf_training_extra__extra_cnf__planted3sat_n40_m170_003.cnf` | SAT | yes | 40 | 170 | 0.0300 | 0.0248 | 0.0230 | `[0.0230, 0.0248, 0.0236, 0.0368, 0.0420]` | valid SAT |
| `cnf_training_extra__extra_cnf__planted3sat_n40_m170_004.cnf` | SAT | yes | 40 | 170 | 0.0291 | 0.0268 | 0.0235 | `[0.0245, 0.0379, 0.0235, 0.0268, 0.0329]` | valid SAT |
| `cnf_training_extra__extra_cnf__planted3sat_n40_m170_005.cnf` | SAT | yes | 40 | 170 | 0.0266 | 0.0224 | 0.0214 | `[0.0224, 0.0340, 0.0220, 0.0214, 0.0333]` | valid SAT |
| `cnf_training_extra__extra_cnf__planted3sat_n40_m170_006.cnf` | SAT | yes | 40 | 170 | 0.0314 | 0.0307 | 0.0223 | `[0.0366, 0.0223, 0.0225, 0.0449, 0.0307]` | valid SAT |
| `cnf_training_extra__extra_cnf__planted3sat_n40_m170_007.cnf` | SAT | yes | 40 | 170 | 0.0301 | 0.0279 | 0.0230 | `[0.0230, 0.0464, 0.0238, 0.0279, 0.0296]` | valid SAT |
| `cnf_training_extra__extra_cnf__planted3sat_n40_m170_008.cnf` | SAT | yes | 40 | 170 | 0.0331 | 0.0339 | 0.0242 | `[0.0355, 0.0242, 0.0437, 0.0283, 0.0339]` | valid SAT |
| `cnf_training_extra__extra_cnf__planted3sat_n40_m170_009.cnf` | SAT | yes | 40 | 170 | 0.0303 | 0.0268 | 0.0237 | `[0.0399, 0.0248, 0.0237, 0.0364, 0.0268]` | valid SAT |
| `cnf_training_extra__extra_cnf__planted3sat_n40_m170_010.cnf` | SAT | yes | 40 | 170 | 0.0270 | 0.0243 | 0.0231 | `[0.0375, 0.0241, 0.0243, 0.0231, 0.0260]` | valid SAT |
| `cnf_training_extra__extra_cnf__planted3sat_n60_m255_001.cnf` | SAT | yes | 60 | 255 | 0.0331 | 0.0283 | 0.0262 | `[0.0443, 0.0266, 0.0399, 0.0262, 0.0283]` | valid SAT |
| `cnf_training_extra__extra_cnf__planted3sat_n60_m255_002.cnf` | SAT | yes | 60 | 255 | 0.0269 | 0.0248 | 0.0224 | `[0.0276, 0.0372, 0.0248, 0.0224, 0.0225]` | valid SAT |
| `cnf_training_extra__extra_cnf__planted3sat_n60_m255_003.cnf` | SAT | yes | 60 | 255 | 0.0278 | 0.0241 | 0.0236 | `[0.0331, 0.0239, 0.0236, 0.0241, 0.0345]` | valid SAT |
| `cnf_training_extra__extra_cnf__planted3sat_n60_m255_004.cnf` | SAT | yes | 60 | 255 | 0.0267 | 0.0227 | 0.0226 | `[0.0227, 0.0236, 0.0226, 0.0418, 0.0226]` | valid SAT |
| `cnf_training_extra__extra_cnf__planted3sat_n60_m255_005.cnf` | SAT | yes | 60 | 255 | 0.0264 | 0.0224 | 0.0219 | `[0.0219, 0.0356, 0.0298, 0.0221, 0.0224]` | valid SAT |
| `cnf_training_extra__extra_cnf__planted3sat_n60_m255_006.cnf` | SAT | yes | 60 | 255 | 0.0224 | 0.0224 | 0.0220 | `[0.0225, 0.0224, 0.0224, 0.0220, 0.0225]` | valid SAT |
| `cnf_training_extra__extra_cnf__planted3sat_n60_m255_007.cnf` | SAT | yes | 60 | 255 | 0.0321 | 0.0252 | 0.0237 | `[0.0237, 0.0434, 0.0252, 0.0440, 0.0241]` | valid SAT |
| `cnf_training_extra__extra_cnf__planted3sat_n60_m255_008.cnf` | SAT | yes | 60 | 255 | 0.0261 | 0.0262 | 0.0239 | `[0.0290, 0.0249, 0.0239, 0.0265, 0.0262]` | valid SAT |
| `cnf_training_extra__extra_cnf__planted3sat_n80_m340_001.cnf` | SAT | yes | 80 | 340 | 0.0360 | 0.0373 | 0.0282 | `[0.0405, 0.0345, 0.0394, 0.0373, 0.0282]` | valid SAT |
| `cnf_training_extra__extra_cnf__planted3sat_n80_m340_002.cnf` | SAT | yes | 80 | 340 | 0.0290 | 0.0266 | 0.0253 | `[0.0346, 0.0266, 0.0330, 0.0254, 0.0253]` | valid SAT |
| `cnf_training_extra__extra_cnf__planted3sat_n80_m340_003.cnf` | SAT | yes | 80 | 340 | 0.0279 | 0.0240 | 0.0234 | `[0.0373, 0.0240, 0.0234, 0.0239, 0.0308]` | valid SAT |
| `cnf_training_extra__extra_cnf__planted3sat_n80_m340_004.cnf` | SAT | yes | 80 | 340 | 0.0373 | 0.0431 | 0.0261 | `[0.0301, 0.0261, 0.0441, 0.0431, 0.0431]` | valid SAT |
| `cnf_training_extra__extra_cnf__planted3sat_n80_m340_005.cnf` | SAT | yes | 80 | 340 | 0.0309 | 0.0301 | 0.0278 | `[0.0308, 0.0301, 0.0376, 0.0280, 0.0278]` | valid SAT |
| `cnf_training_extra__extra_cnf__planted3sat_n80_m340_006.cnf` | SAT | yes | 80 | 340 | 0.0278 | 0.0253 | 0.0241 | `[0.0349, 0.0300, 0.0253, 0.0247, 0.0241]` | valid SAT |
| `cnf_training_extra__extra_cnf__xor_parity_sat_n18_eq18_w3_001.cnf` | SAT | yes | 18 | 72 | 0.0243 | 0.0226 | 0.0212 | `[0.0226, 0.0226, 0.0254, 0.0297, 0.0212]` | valid SAT |
| `cnf_training_extra__extra_cnf__xor_parity_sat_n24_eq24_w3_002.cnf` | SAT | yes | 24 | 96 | 0.0310 | 0.0331 | 0.0219 | `[0.0349, 0.0341, 0.0219, 0.0331, 0.0312]` | valid SAT |
| `cnf_training_extra__extra_cnf__xor_parity_sat_n30_eq30_w3_003.cnf` | SAT | yes | 30 | 120 | 0.0302 | 0.0339 | 0.0219 | `[0.0339, 0.0356, 0.0361, 0.0235, 0.0219]` | valid SAT |
| `cnf_training_extra__extra_cnf__xor_parity_sat_n32_eq20_w4_007.cnf` | SAT | yes | 32 | 160 | 0.0305 | 0.0302 | 0.0223 | `[0.0223, 0.0382, 0.0302, 0.0267, 0.0352]` | valid SAT |
| `cnf_training_extra__extra_cnf__xor_parity_sat_n40_eq35_w3_004.cnf` | SAT | yes | 40 | 140 | 0.0323 | 0.0339 | 0.0232 | `[0.0329, 0.0365, 0.0232, 0.0349, 0.0339]` | valid SAT |
| `cnf_training_extra__extra_cnf__xor_parity_sat_n48_eq28_w4_008.cnf` | SAT | yes | 48 | 224 | 0.0308 | 0.0321 | 0.0239 | `[0.0353, 0.0295, 0.0321, 0.0239, 0.0335]` | valid SAT |
| `cnf_training_extra__extra_cnf__xor_parity_sat_n60_eq45_w3_005.cnf` | SAT | yes | 60 | 180 | 0.0242 | 0.0236 | 0.0227 | `[0.0233, 0.0236, 0.0227, 0.0247, 0.0264]` | valid SAT |
| `cnf_training_extra__extra_cnf__xor_parity_sat_n80_eq55_w3_006.cnf` | SAT | yes | 80 | 220 | 0.0277 | 0.0246 | 0.0220 | `[0.0226, 0.0220, 0.0355, 0.0338, 0.0246]` | valid SAT |
| `cnf_training_extra__extra_cnf__xor_parity_unsat_n18_eq12_w3_001.cnf` | UNSAT | yes | 18 | 48 | 0.0251 | 0.0232 | 0.0230 | `[0.0230, 0.0231, 0.0232, 0.0317, 0.0245]` | valid UNSAT (format checked) |
| `cnf_training_extra__extra_cnf__xor_parity_unsat_n24_eq16_w3_002.cnf` | UNSAT | yes | 24 | 64 | 0.0251 | 0.0229 | 0.0217 | `[0.0357, 0.0234, 0.0219, 0.0229, 0.0217]` | valid UNSAT (format checked) |
| `cnf_training_extra__extra_cnf__xor_parity_unsat_n30_eq20_w3_003.cnf` | UNSAT | yes | 30 | 80 | 0.0292 | 0.0339 | 0.0205 | `[0.0339, 0.0205, 0.0350, 0.0225, 0.0339]` | valid UNSAT (format checked) |
| `cnf_training_extra__extra_cnf__xor_parity_unsat_n32_eq18_w4_006.cnf` | UNSAT | yes | 32 | 144 | 0.0265 | 0.0222 | 0.0216 | `[0.0222, 0.0217, 0.0345, 0.0216, 0.0326]` | valid UNSAT (format checked) |
| `cnf_training_extra__extra_cnf__xor_parity_unsat_n40_eq24_w3_004.cnf` | UNSAT | yes | 40 | 96 | 0.0270 | 0.0234 | 0.0208 | `[0.0208, 0.0222, 0.0247, 0.0234, 0.0438]` | valid UNSAT (format checked) |
| `cnf_training_extra__extra_cnf__xor_parity_unsat_n60_eq32_w3_005.cnf` | UNSAT | yes | 60 | 128 | 0.0320 | 0.0338 | 0.0221 | `[0.0361, 0.0338, 0.0378, 0.0221, 0.0302]` | valid UNSAT (format checked) |
| `large__test_1.cnf` | SAT | yes | 373 | 811 | 0.0417 | 0.0439 | 0.0297 | `[0.0451, 0.0318, 0.0439, 0.0297, 0.0580]` | valid SAT |
| `large__test_10.cnf` | UNSAT | yes | 229 | 1280 | 0.8546 | 0.8468 | 0.8234 | `[0.8234, 0.8387, 0.8468, 0.8618, 0.9023]` | valid UNSAT (format checked) |
| `large__test_2.cnf` | SAT | yes | 319 | 573 | 0.0355 | 0.0328 | 0.0311 | `[0.0404, 0.0326, 0.0328, 0.0311, 0.0408]` | valid SAT |
| `large__test_3.cnf` | UNSAT | yes | 227 | 1460 | 0.2853 | 0.2826 | 0.2764 | `[0.2991, 0.2826, 0.2812, 0.2764, 0.2872]` | valid UNSAT (format checked) |
| `large__test_4.cnf` | UNSAT | yes | 219 | 1363 | 0.2553 | 0.2523 | 0.2365 | `[0.2535, 0.2365, 0.2935, 0.2408, 0.2523]` | valid UNSAT (format checked) |
| `large__test_5.cnf` | SAT | yes | 244 | 772 | 0.0320 | 0.0303 | 0.0296 | `[0.0383, 0.0318, 0.0300, 0.0296, 0.0303]` | valid SAT |
| `large__test_6.cnf` | UNSAT | yes | 271 | 1393 | 3.4833 | 3.4581 | 3.4106 | `[3.5009, 3.4106, 3.6070, 3.4581, 3.4401]` | valid UNSAT (format checked) |
| `large__test_7.cnf` | SAT | yes | 389 | 863 | 0.0377 | 0.0345 | 0.0337 | `[0.0341, 0.0345, 0.0487, 0.0337, 0.0375]` | valid SAT |
| `large__test_8.cnf` | SAT | yes | 298 | 1210 | 0.1294 | 0.1200 | 0.1180 | `[0.1378, 0.1190, 0.1200, 0.1523, 0.1180]` | valid SAT |
| `large__test_9.cnf` | SAT | yes | 365 | 969 | 0.0323 | 0.0312 | 0.0295 | `[0.0312, 0.0295, 0.0301, 0.0319, 0.0386]` | valid SAT |
| `medium__test_1.cnf` | UNSAT | yes | 63 | 835 | 0.0357 | 0.0389 | 0.0269 | `[0.0311, 0.0389, 0.0269, 0.0404, 0.0411]` | valid UNSAT (format checked) |
| `medium__test_10.cnf` | UNSAT | yes | 68 | 822 | 0.0346 | 0.0335 | 0.0270 | `[0.0434, 0.0270, 0.0374, 0.0318, 0.0335]` | valid UNSAT (format checked) |
| `medium__test_2.cnf` | UNSAT | yes | 69 | 352 | 0.0412 | 0.0438 | 0.0331 | `[0.0438, 0.0512, 0.0443, 0.0339, 0.0331]` | valid UNSAT (format checked) |
| `medium__test_3.cnf` | UNSAT | yes | 172 | 774 | 0.5169 | 0.5134 | 0.4974 | `[0.5063, 0.4974, 0.5134, 0.5308, 0.5365]` | valid UNSAT (format checked) |
| `medium__test_4.cnf` | UNSAT | yes | 191 | 886 | 0.8882 | 0.8970 | 0.8534 | `[0.9225, 0.8665, 0.9016, 0.8970, 0.8534]` | valid UNSAT (format checked) |
| `medium__test_5.cnf` | UNSAT | yes | 55 | 713 | 0.0350 | 0.0315 | 0.0269 | `[0.0269, 0.0315, 0.0404, 0.0293, 0.0472]` | valid UNSAT (format checked) |
| `medium__test_6.cnf` | UNSAT | yes | 61 | 512 | 0.0399 | 0.0381 | 0.0344 | `[0.0376, 0.0399, 0.0493, 0.0381, 0.0344]` | valid UNSAT (format checked) |
| `medium__test_7.cnf` | UNSAT | yes | 75 | 562 | 0.0359 | 0.0370 | 0.0279 | `[0.0379, 0.0279, 0.0370, 0.0463, 0.0305]` | valid UNSAT (format checked) |
| `medium__test_8.cnf` | SAT | yes | 130 | 333 | 0.0350 | 0.0349 | 0.0297 | `[0.0297, 0.0381, 0.0332, 0.0349, 0.0391]` | valid SAT |
| `medium__test_9.cnf` | SAT | yes | 138 | 379 | 0.0336 | 0.0331 | 0.0262 | `[0.0291, 0.0389, 0.0262, 0.0331, 0.0410]` | valid SAT |
| `satlib_more__aim-100-1_6-no-1.cnf` | UNSAT | yes | 100 | 160 | 0.0317 | 0.0282 | 0.0238 | `[0.0282, 0.0269, 0.0379, 0.0238, 0.0414]` | valid UNSAT (format checked) |
| `satlib_more__aim-100-1_6-no-2.cnf` | UNSAT | yes | 100 | 160 | 0.0372 | 0.0288 | 0.0267 | `[0.0267, 0.0288, 0.0518, 0.0509, 0.0276]` | valid UNSAT (format checked) |
| `satlib_more__aim-100-1_6-yes1-1.cnf` | SAT | yes | 100 | 160 | 0.0324 | 0.0266 | 0.0253 | `[0.0428, 0.0266, 0.0261, 0.0253, 0.0411]` | valid SAT |
| `satlib_more__aim-100-1_6-yes1-2.cnf` | SAT | yes | 100 | 160 | 0.0369 | 0.0389 | 0.0272 | `[0.0272, 0.0416, 0.0389, 0.0447, 0.0319]` | valid SAT |
| `satlib_more__flat75-1.cnf` | SAT | yes | 225 | 840 | 0.0347 | 0.0304 | 0.0264 | `[0.0304, 0.0351, 0.0302, 0.0264, 0.0512]` | valid SAT |
| `satlib_more__flat75-10.cnf` | SAT | yes | 225 | 840 | 0.0415 | 0.0350 | 0.0311 | `[0.0336, 0.0311, 0.0350, 0.0554, 0.0522]` | valid SAT |
| `satlib_more__jnh1.cnf` | SAT | yes | 100 | 850 | 0.0420 | 0.0441 | 0.0367 | `[0.0390, 0.0367, 0.0442, 0.0457, 0.0441]` | valid SAT |
| `satlib_more__jnh10.cnf` | UNSAT | yes | 100 | 850 | 0.0377 | 0.0386 | 0.0301 | `[0.0304, 0.0456, 0.0386, 0.0436, 0.0301]` | valid UNSAT (format checked) |
| `satlib_more__uf125-01.cnf` | SAT | yes | 125 | 538 | 0.0334 | 0.0319 | 0.0300 | `[0.0350, 0.0397, 0.0303, 0.0300, 0.0319]` | valid SAT |
| `satlib_more__uf125-010.cnf` | SAT | yes | 125 | 538 | 0.0953 | 0.0974 | 0.0851 | `[0.1015, 0.0977, 0.0949, 0.0974, 0.0851]` | valid SAT |
| `satlib_more__uf150-01.cnf` | SAT | yes | 150 | 645 | 0.0499 | 0.0532 | 0.0422 | `[0.0440, 0.0534, 0.0569, 0.0532, 0.0422]` | valid SAT |
| `satlib_more__uuf125-01.cnf` | UNSAT | yes | 125 | 538 | 0.1022 | 0.1027 | 0.0965 | `[0.0999, 0.0965, 0.1056, 0.1027, 0.1060]` | valid UNSAT (format checked) |
| `satlib_more__uuf125-010.cnf` | UNSAT | yes | 125 | 538 | 0.1482 | 0.1468 | 0.1348 | `[0.1468, 0.1504, 0.1724, 0.1367, 0.1348]` | valid UNSAT (format checked) |
| `satlib_more__uuf150-01.cnf` | UNSAT | yes | 150 | 645 | 0.3745 | 0.3602 | 0.3413 | `[0.3711, 0.4556, 0.3602, 0.3413, 0.3443]` | valid UNSAT (format checked) |
| `satlib_subset__dubois20.cnf` | UNSAT | yes | 60 | 160 | 0.0267 | 0.0240 | 0.0222 | `[0.0278, 0.0362, 0.0240, 0.0234, 0.0222]` | valid UNSAT (format checked) |
| `satlib_subset__dubois21.cnf` | UNSAT | yes | 63 | 168 | 0.0285 | 0.0228 | 0.0227 | `[0.0280, 0.0227, 0.0462, 0.0228, 0.0227]` | valid UNSAT (format checked) |
| `satlib_subset__flat50-1.cnf` | SAT | yes | 150 | 545 | 0.0340 | 0.0342 | 0.0241 | `[0.0351, 0.0462, 0.0303, 0.0241, 0.0342]` | valid SAT |
| `satlib_subset__flat50-10.cnf` | SAT | yes | 150 | 545 | 0.0301 | 0.0259 | 0.0250 | `[0.0387, 0.0259, 0.0250, 0.0251, 0.0361]` | valid SAT |
| `satlib_subset__hole10.cnf` | UNSAT | yes | 110 | 561 | 0.0293 | 0.0238 | 0.0235 | `[0.0360, 0.0238, 0.0236, 0.0235, 0.0395]` | valid UNSAT (format checked) |
| `satlib_subset__hole8.cnf` | UNSAT | yes | 72 | 297 | 0.0218 | 0.0218 | 0.0202 | `[0.0211, 0.0202, 0.0218, 0.0229, 0.0232]` | valid UNSAT (format checked) |
| `satlib_subset__uf100-01.cnf` | SAT | yes | 100 | 430 | 0.0577 | 0.0550 | 0.0531 | `[0.0550, 0.0545, 0.0625, 0.0531, 0.0636]` | valid SAT |
| `satlib_subset__uf100-010.cnf` | SAT | yes | 100 | 430 | 0.0367 | 0.0296 | 0.0289 | `[0.0289, 0.0296, 0.0529, 0.0295, 0.0428]` | valid SAT |
| `satlib_subset__uuf100-01.cnf` | UNSAT | yes | 100 | 430 | 0.0494 | 0.0484 | 0.0470 | `[0.0471, 0.0484, 0.0554, 0.0493, 0.0470]` | valid UNSAT (format checked) |
| `satlib_subset__uuf100-010.cnf` | UNSAT | yes | 100 | 430 | 0.0667 | 0.0613 | 0.0570 | `[0.0583, 0.0613, 0.0823, 0.0746, 0.0570]` | valid UNSAT (format checked) |
| `small__test_1.cnf` | SAT | yes | 19 | 26 | 0.0302 | 0.0334 | 0.0224 | `[0.0359, 0.0228, 0.0366, 0.0224, 0.0334]` | valid SAT |
| `small__test_10.cnf` | UNSAT | yes | 22 | 174 | 0.0310 | 0.0271 | 0.0224 | `[0.0224, 0.0271, 0.0429, 0.0369, 0.0258]` | valid UNSAT (format checked) |
| `small__test_2.cnf` | SAT | yes | 46 | 176 | 0.0319 | 0.0266 | 0.0239 | `[0.0265, 0.0266, 0.0239, 0.0407, 0.0416]` | valid SAT |
| `small__test_3.cnf` | SAT | yes | 41 | 150 | 0.0326 | 0.0281 | 0.0230 | `[0.0236, 0.0388, 0.0281, 0.0230, 0.0495]` | valid SAT |
| `small__test_4.cnf` | UNSAT | yes | 30 | 167 | 0.0290 | 0.0277 | 0.0264 | `[0.0264, 0.0284, 0.0267, 0.0277, 0.0358]` | valid UNSAT (format checked) |
| `small__test_5.cnf` | SAT | yes | 20 | 40 | 0.0285 | 0.0254 | 0.0223 | `[0.0454, 0.0256, 0.0223, 0.0240, 0.0254]` | valid SAT |
| `small__test_6.cnf` | SAT | yes | 42 | 70 | 0.0307 | 0.0242 | 0.0225 | `[0.0314, 0.0225, 0.0511, 0.0242, 0.0242]` | valid SAT |
| `small__test_7.cnf` | SAT | yes | 49 | 167 | 0.0375 | 0.0350 | 0.0337 | `[0.0338, 0.0376, 0.0337, 0.0350, 0.0472]` | valid SAT |
| `small__test_8.cnf` | UNSAT | yes | 14 | 68 | 0.0344 | 0.0347 | 0.0323 | `[0.0347, 0.0339, 0.0323, 0.0353, 0.0358]` | valid UNSAT (brute-force checked) |
| `small__test_9.cnf` | SAT | yes | 40 | 100 | 0.0316 | 0.0274 | 0.0267 | `[0.0418, 0.0267, 0.0274, 0.0268, 0.0355]` | valid SAT |
| `special__dense.cnf` | UNSAT | yes | 200 | 1500 | 0.1286 | 0.1292 | 0.1172 | `[0.1273, 0.1292, 0.1367, 0.1328, 0.1172]` | valid UNSAT (format checked) |
| `special__easy.cnf` | SAT | yes | 200 | 400 | 0.0361 | 0.0399 | 0.0249 | `[0.0399, 0.0249, 0.0307, 0.0420, 0.0430]` | valid SAT |
| `special__hard.cnf` | UNSAT | yes | 200 | 850 | 2.6175 | 2.5953 | 2.5664 | `[2.5953, 2.6456, 2.5664, 2.6878, 2.5924]` | valid UNSAT (format checked) |
| `special__pigeonhole.cnf` | UNSAT | yes | 90 | 415 | 0.0330 | 0.0358 | 0.0216 | `[0.0358, 0.0406, 0.0216, 0.0421, 0.0249]` | valid UNSAT (format checked) |
| `special__tseitin.cnf` | UNSAT | yes | 40 | 160 | 0.0301 | 0.0329 | 0.0224 | `[0.0358, 0.0224, 0.0241, 0.0329, 0.0357]` | valid UNSAT (format checked) |
