# SAT Solver Course CNF Tests Avg5 Benchmark With Mycielski

Generated: 2026-05-31T22:49:39
Dataset: `course_cnf_tests scratch set, 279 CNF files`
Source benchmark output: `/tmp/satsolver_course_cnf_tests_all_avg5.txt`
Solver: `satsolver`
Mode: `cli`
CLI script: `/home/doomguy/Desktop/sat/satsolver/satsolver.py`
Python executable: `/usr/bin/python`
Repeats: `5`
Bruteforce var limit: `16`
Metric note: `avg5 total` is `measured total / 5`, i.e. the mean runtime over five CLI runs per case. `median total` is the benchmark harness representative median sum.
Note: New artifact with `cnf_training_complex__complex_cnf_hard__mycielski_iter4_color5_unsat.cnf` included.

## Overall

| cases | solved | errors | SAT | UNSAT | avg5 total s | median total s | avg/case s | median/case s | max median-case s | measured total s | wall clock s |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 279 | 279 | 0 | 157 | 122 | 26.4364 | 26.2183 | 0.0948 | 0.0305 | 3.4579 | 132.1822 | 141.5965 |

## Folder Summary

| folder | cases | solved | errors | SAT | UNSAT | avg5 total s | median total s | avg/case s | median/case s | max median-case s | measured total s |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| `.` | 279 | 279 | 0 | 157 | 122 | 26.4364 | 26.2183 | 0.0948 | 0.0305 | 3.4579 | 132.1822 |

## Highlight Case

| case | result | vars | clauses | avg5 s | median s | best s | samples | validation |
|---|---|---:|---:|---:|---:|---:|---|---|
| `cnf_training_complex__complex_cnf_hard__mycielski_iter4_color5_unsat.cnf` | UNSAT | 235 | 1697 | 0.0374 | 0.0409 | 0.0280 | `[0.0304, 0.0280, 0.0410, 0.0409, 0.0464]` | valid UNSAT (format checked) |

## Slowest Cases By Avg5

| case | result | vars | clauses | avg5 s | median s | best s | samples | validation |
|---|---|---:|---:|---:|---:|---:|---|---|
| `large__test_6.cnf` | UNSAT | 271 | 1393 | 3.4607 | 3.4579 | 3.4365 | `[3.4365, 3.4495, 3.4579, 3.4583, 3.5015]` | valid UNSAT (format checked) |
| `special__hard.cnf` | UNSAT | 200 | 850 | 2.5014 | 2.5018 | 2.4651 | `[2.5242, 2.4870, 2.5289, 2.5018, 2.4651]` | valid UNSAT (format checked) |
| `cnf_training_complex__complex_cnf_hard__planted3sat_balanced_n260_m1108_seed1.cnf` | SAT | 260 | 1108 | 1.5073 | 1.5066 | 1.4783 | `[1.4783, 1.5188, 1.4828, 1.5502, 1.5066]` | valid SAT |
| `cnf_training_complex__complex_cnf_hard__ramsey_R3_4_n11_unsat.cnf` | UNSAT | 55 | 495 | 1.1767 | 1.1774 | 1.1359 | `[1.1568, 1.1359, 1.2315, 1.1774, 1.1819]` | valid UNSAT (format checked) |
| `cnf_training_complex__complex_cnf_moderate__ramsey_R3_4_n9_unsat.cnf` | UNSAT | 36 | 210 | 1.1118 | 1.1185 | 1.0856 | `[1.0916, 1.1258, 1.0856, 1.1185, 1.1377]` | valid UNSAT (format checked) |
| `cnf_training_complex__complex_cnf_moderate__ramsey_R3_4_n10_unsat.cnf` | UNSAT | 45 | 330 | 1.0947 | 1.0922 | 1.0538 | `[1.0922, 1.0790, 1.0538, 1.1112, 1.1375]` | valid UNSAT (format checked) |
| `cnf_training_complex__complex_cnf_moderate__planted3sat_balanced_n200_m852_seed2.cnf` | SAT | 200 | 852 | 0.9474 | 0.9460 | 0.9361 | `[0.9669, 0.9476, 0.9361, 0.9406, 0.9460]` | valid SAT |
| `medium__test_4.cnf` | UNSAT | 191 | 886 | 0.8544 | 0.8662 | 0.8242 | `[0.8714, 0.8428, 0.8662, 0.8242, 0.8676]` | valid UNSAT (format checked) |
| `cnf_training_complex__complex_cnf_hard__planted3sat_balanced_n320_m1363_seed1.cnf` | SAT | 320 | 1363 | 0.8428 | 0.8452 | 0.8170 | `[0.8390, 0.8170, 0.8452, 0.8514, 0.8615]` | valid SAT |
| `large__test_10.cnf` | UNSAT | 229 | 1280 | 0.8393 | 0.8487 | 0.8121 | `[0.8121, 0.8316, 0.8518, 0.8522, 0.8487]` | valid UNSAT (format checked) |
| `cnf_training_complex__complex_cnf_hard__planted3sat_balanced_n260_m1108_seed2.cnf` | SAT | 260 | 1108 | 0.6374 | 0.6358 | 0.6254 | `[0.6581, 0.6389, 0.6358, 0.6254, 0.6288]` | valid SAT |
| `medium__test_3.cnf` | UNSAT | 172 | 774 | 0.5012 | 0.5024 | 0.4869 | `[0.4869, 0.5135, 0.5024, 0.5151, 0.4879]` | valid UNSAT (format checked) |
| `cnf_training_complex__complex_cnf_moderate__planted3sat_balanced_n200_m852_seed1.cnf` | SAT | 200 | 852 | 0.4515 | 0.4480 | 0.4348 | `[0.4480, 0.4502, 0.4348, 0.4446, 0.4799]` | valid SAT |
| `satlib_more__uuf150-01.cnf` | UNSAT | 150 | 645 | 0.3439 | 0.3444 | 0.3336 | `[0.3568, 0.3444, 0.3336, 0.3379, 0.3466]` | valid UNSAT (format checked) |
| `cnf_training_complex__complex_cnf_hard__planted3sat_balanced_n400_m1704_seed1.cnf` | SAT | 400 | 1704 | 0.3205 | 0.3178 | 0.3046 | `[0.3424, 0.3046, 0.3178, 0.3226, 0.3153]` | valid SAT |
| `large__test_3.cnf` | UNSAT | 227 | 1460 | 0.2905 | 0.2906 | 0.2745 | `[0.2892, 0.3040, 0.2906, 0.2745, 0.2940]` | valid UNSAT (format checked) |
| `cnf_training_complex__complex_cnf_hard__planted3sat_balanced_n320_m1363_seed2.cnf` | SAT | 320 | 1363 | 0.2889 | 0.2846 | 0.2758 | `[0.3024, 0.2758, 0.2846, 0.2826, 0.2989]` | valid SAT |
| `large__test_4.cnf` | UNSAT | 219 | 1363 | 0.2539 | 0.2464 | 0.2441 | `[0.2689, 0.2657, 0.2464, 0.2445, 0.2441]` | valid UNSAT (format checked) |
| `cnf_training_complex__complex_cnf_moderate__xor_sparse_sat_n128_eq165_w3-4_seed3.cnf` | SAT | 128 | 1000 | 0.2442 | 0.2485 | 0.2302 | `[0.2485, 0.2302, 0.2339, 0.2599, 0.2487]` | valid SAT |
| `satlib_more__uuf125-010.cnf` | UNSAT | 125 | 538 | 0.1518 | 0.1523 | 0.1401 | `[0.1462, 0.1401, 0.1567, 0.1523, 0.1636]` | valid UNSAT (format checked) |

## All Cases

| case | result | ok | vars | clauses | avg5 s | median s | best s | samples | validation |
|---|---|---:|---:|---:|---:|---:|---:|---|---|
| `cnf_training_complex__complex_cnf_hard__mycielski_iter4_color5_unsat.cnf` | UNSAT | yes | 235 | 1697 | 0.0374 | 0.0409 | 0.0280 | `[0.0304, 0.0280, 0.0410, 0.0409, 0.0464]` | valid UNSAT (format checked) |
| `cnf_training_complex__complex_cnf_hard__planted3sat_balanced_n260_m1108_seed1.cnf` | SAT | yes | 260 | 1108 | 1.5073 | 1.5066 | 1.4783 | `[1.4783, 1.5188, 1.4828, 1.5502, 1.5066]` | valid SAT |
| `cnf_training_complex__complex_cnf_hard__planted3sat_balanced_n260_m1108_seed2.cnf` | SAT | yes | 260 | 1108 | 0.6374 | 0.6358 | 0.6254 | `[0.6581, 0.6389, 0.6358, 0.6254, 0.6288]` | valid SAT |
| `cnf_training_complex__complex_cnf_hard__planted3sat_balanced_n320_m1363_seed1.cnf` | SAT | yes | 320 | 1363 | 0.8428 | 0.8452 | 0.8170 | `[0.8390, 0.8170, 0.8452, 0.8514, 0.8615]` | valid SAT |
| `cnf_training_complex__complex_cnf_hard__planted3sat_balanced_n320_m1363_seed2.cnf` | SAT | yes | 320 | 1363 | 0.2889 | 0.2846 | 0.2758 | `[0.3024, 0.2758, 0.2846, 0.2826, 0.2989]` | valid SAT |
| `cnf_training_complex__complex_cnf_hard__planted3sat_balanced_n400_m1704_seed1.cnf` | SAT | yes | 400 | 1704 | 0.3205 | 0.3178 | 0.3046 | `[0.3424, 0.3046, 0.3178, 0.3226, 0.3153]` | valid SAT |
| `cnf_training_complex__complex_cnf_hard__ramsey_R3_4_n11_unsat.cnf` | UNSAT | yes | 55 | 495 | 1.1767 | 1.1774 | 1.1359 | `[1.1568, 1.1359, 1.2315, 1.1774, 1.1819]` | valid UNSAT (format checked) |
| `cnf_training_complex__complex_cnf_hard__tseitin_deg3_v100_sat.cnf` | SAT | yes | 150 | 400 | 0.0359 | 0.0315 | 0.0260 | `[0.0544, 0.0315, 0.0279, 0.0397, 0.0260]` | valid SAT |
| `cnf_training_complex__complex_cnf_hard__tseitin_deg3_v100_unsat.cnf` | UNSAT | yes | 150 | 400 | 0.0259 | 0.0227 | 0.0221 | `[0.0221, 0.0227, 0.0222, 0.0235, 0.0389]` | valid UNSAT (format checked) |
| `cnf_training_complex__complex_cnf_hard__tseitin_deg3_v120_sat.cnf` | SAT | yes | 180 | 480 | 0.0313 | 0.0290 | 0.0272 | `[0.0272, 0.0334, 0.0395, 0.0275, 0.0290]` | valid SAT |
| `cnf_training_complex__complex_cnf_hard__tseitin_deg3_v120_unsat.cnf` | UNSAT | yes | 180 | 480 | 0.0311 | 0.0285 | 0.0234 | `[0.0234, 0.0391, 0.0401, 0.0285, 0.0244]` | valid UNSAT (format checked) |
| `cnf_training_complex__complex_cnf_hard__tseitin_deg3_v160_sat.cnf` | SAT | yes | 240 | 640 | 0.0454 | 0.0433 | 0.0420 | `[0.0429, 0.0455, 0.0433, 0.0535, 0.0420]` | valid SAT |
| `cnf_training_complex__complex_cnf_hard__tseitin_deg3_v160_unsat.cnf` | UNSAT | yes | 240 | 640 | 0.0272 | 0.0245 | 0.0236 | `[0.0236, 0.0344, 0.0237, 0.0296, 0.0245]` | valid UNSAT (format checked) |
| `cnf_training_complex__complex_cnf_hard__tseitin_deg4_v64_sat.cnf` | SAT | yes | 128 | 512 | 0.0459 | 0.0418 | 0.0405 | `[0.0418, 0.0406, 0.0532, 0.0534, 0.0405]` | valid SAT |
| `cnf_training_complex__complex_cnf_hard__tseitin_deg4_v64_unsat.cnf` | UNSAT | yes | 128 | 512 | 0.0314 | 0.0344 | 0.0246 | `[0.0354, 0.0345, 0.0282, 0.0246, 0.0344]` | valid UNSAT (format checked) |
| `cnf_training_complex__complex_cnf_hard__tseitin_deg4_v96_sat.cnf` | SAT | yes | 192 | 768 | 0.0455 | 0.0458 | 0.0325 | `[0.0458, 0.0325, 0.0421, 0.0605, 0.0463]` | valid SAT |
| `cnf_training_complex__complex_cnf_hard__tseitin_deg4_v96_unsat.cnf` | UNSAT | yes | 192 | 768 | 0.0304 | 0.0270 | 0.0257 | `[0.0363, 0.0264, 0.0257, 0.0367, 0.0270]` | valid UNSAT (format checked) |
| `cnf_training_complex__complex_cnf_hard__vdw_2color_k4_n45_unsat.cnf` | UNSAT | yes | 45 | 630 | 0.0516 | 0.0503 | 0.0446 | `[0.0503, 0.0467, 0.0606, 0.0560, 0.0446]` | valid UNSAT (format checked) |
| `cnf_training_complex__complex_cnf_hard__vdw_2color_k4_n60_unsat.cnf` | UNSAT | yes | 60 | 1140 | 0.0619 | 0.0628 | 0.0540 | `[0.0628, 0.0672, 0.0540, 0.0687, 0.0571]` | valid UNSAT (format checked) |
| `cnf_training_complex__complex_cnf_hard__xor_sparse_unsat_n100_eq135_w3-4_seed4.cnf` | UNSAT | yes | 100 | 828 | 0.0312 | 0.0290 | 0.0265 | `[0.0265, 0.0390, 0.0267, 0.0348, 0.0290]` | valid UNSAT (format checked) |
| `cnf_training_complex__complex_cnf_hard__xor_sparse_unsat_n140_eq190_w3-4_seed5.cnf` | UNSAT | yes | 140 | 1104 | 0.0346 | 0.0266 | 0.0252 | `[0.0440, 0.0252, 0.0255, 0.0266, 0.0517]` | valid UNSAT (format checked) |
| `cnf_training_complex__complex_cnf_hard__xor_sparse_unsat_n180_eq250_w3-4_seed6.cnf` | UNSAT | yes | 180 | 1544 | 0.0324 | 0.0298 | 0.0281 | `[0.0437, 0.0315, 0.0281, 0.0298, 0.0288]` | valid UNSAT (format checked) |
| `cnf_training_complex__complex_cnf_moderate__mycielski_iter2_color3_unsat.cnf` | UNSAT | yes | 33 | 104 | 0.0259 | 0.0243 | 0.0227 | `[0.0227, 0.0243, 0.0236, 0.0247, 0.0345]` | valid UNSAT (format checked) |
| `cnf_training_complex__complex_cnf_moderate__mycielski_iter2_color4_sat.cnf` | SAT | yes | 44 | 157 | 0.0261 | 0.0253 | 0.0236 | `[0.0318, 0.0253, 0.0254, 0.0236, 0.0241]` | valid SAT |
| `cnf_training_complex__complex_cnf_moderate__mycielski_iter3_color4_unsat.cnf` | UNSAT | yes | 92 | 445 | 0.0300 | 0.0264 | 0.0249 | `[0.0249, 0.0273, 0.0264, 0.0466, 0.0249]` | valid UNSAT (format checked) |
| `cnf_training_complex__complex_cnf_moderate__mycielski_iter3_color5_sat.cnf` | SAT | yes | 115 | 608 | 0.0369 | 0.0381 | 0.0280 | `[0.0381, 0.0434, 0.0280, 0.0445, 0.0305]` | valid SAT |
| `cnf_training_complex__complex_cnf_moderate__ordering_no_minimum_n10.cnf` | UNSAT | yes | 45 | 730 | 0.0485 | 0.0500 | 0.0373 | `[0.0560, 0.0481, 0.0373, 0.0510, 0.0500]` | valid UNSAT (format checked) |
| `cnf_training_complex__complex_cnf_moderate__ordering_no_minimum_n12.cnf` | UNSAT | yes | 66 | 1332 | 0.0676 | 0.0698 | 0.0600 | `[0.0711, 0.0715, 0.0698, 0.0600, 0.0656]` | valid UNSAT (format checked) |
| `cnf_training_complex__complex_cnf_moderate__ordering_no_minimum_n8.cnf` | UNSAT | yes | 28 | 344 | 0.0369 | 0.0404 | 0.0296 | `[0.0296, 0.0302, 0.0404, 0.0422, 0.0422]` | valid UNSAT (format checked) |
| `cnf_training_complex__complex_cnf_moderate__orthogonal_latin_squares_order3_sat.cnf` | SAT | yes | 81 | 1998 | 0.0380 | 0.0346 | 0.0327 | `[0.0342, 0.0444, 0.0327, 0.0440, 0.0346]` | valid SAT |
| `cnf_training_complex__complex_cnf_moderate__pigeonhole_php_11_into_10.cnf` | UNSAT | yes | 110 | 1056 | 0.0340 | 0.0367 | 0.0245 | `[0.0353, 0.0368, 0.0367, 0.0245, 0.0368]` | valid UNSAT (format checked) |
| `cnf_training_complex__complex_cnf_moderate__pigeonhole_php_13_into_12.cnf` | UNSAT | yes | 156 | 1807 | 0.0253 | 0.0253 | 0.0248 | `[0.0252, 0.0257, 0.0248, 0.0253, 0.0255]` | valid UNSAT (format checked) |
| `cnf_training_complex__complex_cnf_moderate__pigeonhole_php_9_into_8.cnf` | UNSAT | yes | 72 | 549 | 0.0242 | 0.0238 | 0.0232 | `[0.0238, 0.0237, 0.0264, 0.0232, 0.0238]` | valid UNSAT (format checked) |
| `cnf_training_complex__complex_cnf_moderate__planted3sat_balanced_n120_m511_seed1.cnf` | SAT | yes | 120 | 511 | 0.0352 | 0.0322 | 0.0291 | `[0.0391, 0.0439, 0.0317, 0.0291, 0.0322]` | valid SAT |
| `cnf_training_complex__complex_cnf_moderate__planted3sat_balanced_n120_m511_seed2.cnf` | SAT | yes | 120 | 511 | 0.0352 | 0.0373 | 0.0294 | `[0.0373, 0.0377, 0.0395, 0.0322, 0.0294]` | valid SAT |
| `cnf_training_complex__complex_cnf_moderate__planted3sat_balanced_n160_m682_seed1.cnf` | SAT | yes | 160 | 682 | 0.0355 | 0.0354 | 0.0343 | `[0.0343, 0.0373, 0.0354, 0.0345, 0.0362]` | valid SAT |
| `cnf_training_complex__complex_cnf_moderate__planted3sat_balanced_n160_m682_seed2.cnf` | SAT | yes | 160 | 682 | 0.0450 | 0.0387 | 0.0376 | `[0.0387, 0.0376, 0.0611, 0.0494, 0.0381]` | valid SAT |
| `cnf_training_complex__complex_cnf_moderate__planted3sat_balanced_n200_m852_seed1.cnf` | SAT | yes | 200 | 852 | 0.4515 | 0.4480 | 0.4348 | `[0.4480, 0.4502, 0.4348, 0.4446, 0.4799]` | valid SAT |
| `cnf_training_complex__complex_cnf_moderate__planted3sat_balanced_n200_m852_seed2.cnf` | SAT | yes | 200 | 852 | 0.9474 | 0.9460 | 0.9361 | `[0.9669, 0.9476, 0.9361, 0.9406, 0.9460]` | valid SAT |
| `cnf_training_complex__complex_cnf_moderate__ramsey_R3_3_n6_unsat.cnf` | UNSAT | yes | 15 | 40 | 0.0332 | 0.0331 | 0.0242 | `[0.0331, 0.0360, 0.0308, 0.0242, 0.0418]` | valid UNSAT (brute-force checked) |
| `cnf_training_complex__complex_cnf_moderate__ramsey_R3_3_n7_unsat.cnf` | UNSAT | yes | 21 | 70 | 0.0360 | 0.0379 | 0.0254 | `[0.0460, 0.0452, 0.0257, 0.0254, 0.0379]` | valid UNSAT (format checked) |
| `cnf_training_complex__complex_cnf_moderate__ramsey_R3_3_n8_unsat.cnf` | UNSAT | yes | 28 | 112 | 0.0298 | 0.0287 | 0.0234 | `[0.0343, 0.0365, 0.0263, 0.0234, 0.0287]` | valid UNSAT (format checked) |
| `cnf_training_complex__complex_cnf_moderate__ramsey_R3_4_n10_unsat.cnf` | UNSAT | yes | 45 | 330 | 1.0947 | 1.0922 | 1.0538 | `[1.0922, 1.0790, 1.0538, 1.1112, 1.1375]` | valid UNSAT (format checked) |
| `cnf_training_complex__complex_cnf_moderate__ramsey_R3_4_n9_unsat.cnf` | UNSAT | yes | 36 | 210 | 1.1118 | 1.1185 | 1.0856 | `[1.0916, 1.1258, 1.0856, 1.1185, 1.1377]` | valid UNSAT (format checked) |
| `cnf_training_complex__complex_cnf_moderate__tseitin_deg3_v40_sat.cnf` | SAT | yes | 60 | 160 | 0.0288 | 0.0239 | 0.0223 | `[0.0343, 0.0223, 0.0238, 0.0396, 0.0239]` | valid SAT |
| `cnf_training_complex__complex_cnf_moderate__tseitin_deg3_v40_unsat.cnf` | UNSAT | yes | 60 | 160 | 0.0322 | 0.0373 | 0.0240 | `[0.0244, 0.0378, 0.0373, 0.0240, 0.0376]` | valid UNSAT (format checked) |
| `cnf_training_complex__complex_cnf_moderate__tseitin_deg3_v60_sat.cnf` | SAT | yes | 90 | 240 | 0.0280 | 0.0268 | 0.0252 | `[0.0267, 0.0288, 0.0252, 0.0325, 0.0268]` | valid SAT |
| `cnf_training_complex__complex_cnf_moderate__tseitin_deg3_v60_unsat.cnf` | UNSAT | yes | 90 | 240 | 0.0303 | 0.0278 | 0.0235 | `[0.0278, 0.0425, 0.0235, 0.0339, 0.0239]` | valid UNSAT (format checked) |
| `cnf_training_complex__complex_cnf_moderate__tseitin_deg3_v80_sat.cnf` | SAT | yes | 120 | 320 | 0.0319 | 0.0302 | 0.0255 | `[0.0255, 0.0438, 0.0292, 0.0302, 0.0308]` | valid SAT |
| `cnf_training_complex__complex_cnf_moderate__tseitin_deg3_v80_unsat.cnf` | UNSAT | yes | 120 | 320 | 0.0264 | 0.0252 | 0.0228 | `[0.0252, 0.0256, 0.0349, 0.0237, 0.0228]` | valid UNSAT (format checked) |
| `cnf_training_complex__complex_cnf_moderate__vdw_2color_k3_n16_unsat.cnf` | UNSAT | yes | 16 | 112 | 0.0365 | 0.0379 | 0.0217 | `[0.0490, 0.0379, 0.0397, 0.0217, 0.0343]` | valid UNSAT (brute-force checked) |
| `cnf_training_complex__complex_cnf_moderate__vdw_2color_k3_n9_unsat.cnf` | UNSAT | yes | 9 | 32 | 0.0313 | 0.0348 | 0.0223 | `[0.0375, 0.0348, 0.0223, 0.0361, 0.0256]` | valid UNSAT (brute-force checked) |
| `cnf_training_complex__complex_cnf_moderate__vdw_2color_k4_n35_unsat.cnf` | UNSAT | yes | 35 | 374 | 0.0430 | 0.0432 | 0.0424 | `[0.0432, 0.0433, 0.0434, 0.0424, 0.0428]` | valid UNSAT (format checked) |
| `cnf_training_complex__complex_cnf_moderate__xor_sparse_sat_n128_eq165_w3-4_seed3.cnf` | SAT | yes | 128 | 1000 | 0.2442 | 0.2485 | 0.2302 | `[0.2485, 0.2302, 0.2339, 0.2599, 0.2487]` | valid SAT |
| `cnf_training_complex__complex_cnf_moderate__xor_sparse_sat_n64_eq82_w3_seed1.cnf` | SAT | yes | 64 | 328 | 0.0316 | 0.0281 | 0.0233 | `[0.0403, 0.0386, 0.0233, 0.0281, 0.0280]` | valid SAT |
| `cnf_training_complex__complex_cnf_moderate__xor_sparse_sat_n96_eq125_w3_seed2.cnf` | SAT | yes | 96 | 500 | 0.0378 | 0.0409 | 0.0299 | `[0.0312, 0.0445, 0.0427, 0.0299, 0.0409]` | valid SAT |
| `cnf_training_complex__complex_cnf_moderate__xor_sparse_unsat_n48_eq62_w3_seed1.cnf` | UNSAT | yes | 48 | 248 | 0.0324 | 0.0366 | 0.0237 | `[0.0381, 0.0366, 0.0251, 0.0385, 0.0237]` | valid UNSAT (format checked) |
| `cnf_training_complex__complex_cnf_moderate__xor_sparse_unsat_n64_eq86_w3_seed2.cnf` | UNSAT | yes | 64 | 344 | 0.0243 | 0.0240 | 0.0236 | `[0.0239, 0.0236, 0.0255, 0.0240, 0.0244]` | valid UNSAT (format checked) |
| `cnf_training_complex__complex_cnf_moderate__xor_sparse_unsat_n80_eq108_w3-4_seed3.cnf` | UNSAT | yes | 80 | 608 | 0.0297 | 0.0275 | 0.0245 | `[0.0347, 0.0245, 0.0367, 0.0275, 0.0251]` | valid UNSAT (format checked) |
| `cnf_training_complex__complex_cnf_stress__tseitin_deg3_v240_unsat.cnf` | UNSAT | yes | 360 | 960 | 0.0374 | 0.0402 | 0.0269 | `[0.0404, 0.0429, 0.0366, 0.0402, 0.0269]` | valid UNSAT (format checked) |
| `cnf_training_complex__complex_cnf_stress__tseitin_deg4_v160_unsat.cnf` | UNSAT | yes | 320 | 1280 | 0.0324 | 0.0326 | 0.0274 | `[0.0274, 0.0389, 0.0326, 0.0330, 0.0299]` | valid UNSAT (format checked) |
| `cnf_training_complex__complex_cnf_stress__xor_sparse_unsat_n240_eq330_w3-4_seed1.cnf` | UNSAT | yes | 240 | 1996 | 0.0378 | 0.0350 | 0.0336 | `[0.0336, 0.0440, 0.0350, 0.0347, 0.0419]` | valid UNSAT (format checked) |
| `cnf_training_extra__extra_cnf__cardinality_exactly_one_sat_g10_s5_004.cnf` | SAT | yes | 50 | 110 | 0.0280 | 0.0260 | 0.0215 | `[0.0247, 0.0215, 0.0260, 0.0394, 0.0287]` | valid SAT |
| `cnf_training_extra__extra_cnf__cardinality_exactly_one_sat_g12_s6_005.cnf` | SAT | yes | 72 | 192 | 0.0345 | 0.0334 | 0.0260 | `[0.0385, 0.0270, 0.0334, 0.0477, 0.0260]` | valid SAT |
| `cnf_training_extra__extra_cnf__cardinality_exactly_one_sat_g16_s4_006.cnf` | SAT | yes | 64 | 112 | 0.0305 | 0.0339 | 0.0221 | `[0.0365, 0.0223, 0.0339, 0.0221, 0.0378]` | valid SAT |
| `cnf_training_extra__extra_cnf__cardinality_exactly_one_sat_g4_s4_001.cnf` | SAT | yes | 16 | 28 | 0.0319 | 0.0352 | 0.0250 | `[0.0364, 0.0352, 0.0367, 0.0250, 0.0264]` | valid SAT |
| `cnf_training_extra__extra_cnf__cardinality_exactly_one_sat_g5_s5_002.cnf` | SAT | yes | 25 | 55 | 0.0289 | 0.0257 | 0.0233 | `[0.0357, 0.0242, 0.0355, 0.0257, 0.0233]` | valid SAT |
| `cnf_training_extra__extra_cnf__cardinality_exactly_one_sat_g8_s4_003.cnf` | SAT | yes | 32 | 56 | 0.0278 | 0.0247 | 0.0216 | `[0.0230, 0.0216, 0.0247, 0.0328, 0.0371]` | valid SAT |
| `cnf_training_extra__extra_cnf__cardinality_exactly_one_unsat_g10_s6_005.cnf` | UNSAT | yes | 60 | 162 | 0.0273 | 0.0250 | 0.0233 | `[0.0243, 0.0250, 0.0375, 0.0264, 0.0233]` | valid UNSAT (format checked) |
| `cnf_training_extra__extra_cnf__cardinality_exactly_one_unsat_g12_s4_006.cnf` | UNSAT | yes | 48 | 86 | 0.0318 | 0.0296 | 0.0241 | `[0.0241, 0.0483, 0.0312, 0.0296, 0.0260]` | valid UNSAT (format checked) |
| `cnf_training_extra__extra_cnf__cardinality_exactly_one_unsat_g3_s4_001.cnf` | UNSAT | yes | 12 | 23 | 0.0307 | 0.0297 | 0.0229 | `[0.0362, 0.0369, 0.0280, 0.0297, 0.0229]` | valid UNSAT (brute-force checked) |
| `cnf_training_extra__extra_cnf__cardinality_exactly_one_unsat_g4_s5_002.cnf` | UNSAT | yes | 20 | 46 | 0.0251 | 0.0223 | 0.0211 | `[0.0235, 0.0223, 0.0223, 0.0211, 0.0365]` | valid UNSAT (format checked) |
| `cnf_training_extra__extra_cnf__cardinality_exactly_one_unsat_g6_s4_003.cnf` | UNSAT | yes | 24 | 44 | 0.0308 | 0.0294 | 0.0238 | `[0.0238, 0.0294, 0.0350, 0.0401, 0.0257]` | valid UNSAT (format checked) |
| `cnf_training_extra__extra_cnf__cardinality_exactly_one_unsat_g8_s5_004.cnf` | UNSAT | yes | 40 | 90 | 0.0331 | 0.0351 | 0.0233 | `[0.0404, 0.0365, 0.0233, 0.0351, 0.0303]` | valid UNSAT (format checked) |
| `cnf_training_extra__extra_cnf__equivalence_chain_len10_sat.cnf` | SAT | yes | 10 | 20 | 0.0290 | 0.0256 | 0.0223 | `[0.0361, 0.0256, 0.0223, 0.0356, 0.0252]` | valid SAT |
| `cnf_training_extra__extra_cnf__equivalence_chain_len10_unsat.cnf` | UNSAT | yes | 10 | 20 | 0.0261 | 0.0248 | 0.0229 | `[0.0248, 0.0310, 0.0229, 0.0284, 0.0235]` | valid UNSAT (brute-force checked) |
| `cnf_training_extra__extra_cnf__equivalence_chain_len120_sat.cnf` | SAT | yes | 120 | 240 | 0.0296 | 0.0275 | 0.0243 | `[0.0281, 0.0435, 0.0275, 0.0243, 0.0244]` | valid SAT |
| `cnf_training_extra__extra_cnf__equivalence_chain_len120_unsat.cnf` | UNSAT | yes | 120 | 240 | 0.0317 | 0.0343 | 0.0251 | `[0.0344, 0.0363, 0.0251, 0.0282, 0.0343]` | valid UNSAT (format checked) |
| `cnf_training_extra__extra_cnf__equivalence_chain_len20_sat.cnf` | SAT | yes | 20 | 40 | 0.0268 | 0.0248 | 0.0227 | `[0.0242, 0.0227, 0.0256, 0.0369, 0.0248]` | valid SAT |
| `cnf_training_extra__extra_cnf__equivalence_chain_len20_unsat.cnf` | UNSAT | yes | 20 | 40 | 0.0305 | 0.0343 | 0.0216 | `[0.0216, 0.0343, 0.0231, 0.0363, 0.0372]` | valid UNSAT (format checked) |
| `cnf_training_extra__extra_cnf__equivalence_chain_len40_sat.cnf` | SAT | yes | 40 | 80 | 0.0321 | 0.0289 | 0.0240 | `[0.0289, 0.0244, 0.0513, 0.0240, 0.0320]` | valid SAT |
| `cnf_training_extra__extra_cnf__equivalence_chain_len40_unsat.cnf` | UNSAT | yes | 40 | 80 | 0.0277 | 0.0251 | 0.0238 | `[0.0251, 0.0380, 0.0238, 0.0239, 0.0276]` | valid UNSAT (format checked) |
| `cnf_training_extra__extra_cnf__equivalence_chain_len80_sat.cnf` | SAT | yes | 80 | 160 | 0.0296 | 0.0280 | 0.0234 | `[0.0243, 0.0234, 0.0360, 0.0280, 0.0361]` | valid SAT |
| `cnf_training_extra__extra_cnf__equivalence_chain_len80_unsat.cnf` | UNSAT | yes | 80 | 160 | 0.0254 | 0.0245 | 0.0239 | `[0.0239, 0.0245, 0.0250, 0.0240, 0.0293]` | valid UNSAT (format checked) |
| `cnf_training_extra__extra_cnf__exact_random3sat_sat_n10_m49_008.cnf` | SAT | yes | 10 | 49 | 0.0312 | 0.0307 | 0.0260 | `[0.0260, 0.0323, 0.0379, 0.0293, 0.0307]` | valid SAT |
| `cnf_training_extra__extra_cnf__exact_random3sat_sat_n11_m40_017.cnf` | SAT | yes | 11 | 40 | 0.0315 | 0.0346 | 0.0244 | `[0.0354, 0.0255, 0.0377, 0.0346, 0.0244]` | valid SAT |
| `cnf_training_extra__extra_cnf__exact_random3sat_sat_n11_m46_001.cnf` | SAT | yes | 11 | 46 | 0.0255 | 0.0232 | 0.0225 | `[0.0225, 0.0230, 0.0232, 0.0240, 0.0349]` | valid SAT |
| `cnf_training_extra__extra_cnf__exact_random3sat_sat_n12_m43_012.cnf` | SAT | yes | 12 | 43 | 0.0302 | 0.0315 | 0.0263 | `[0.0344, 0.0263, 0.0269, 0.0318, 0.0315]` | valid SAT |
| `cnf_training_extra__extra_cnf__exact_random3sat_sat_n12_m47_006.cnf` | SAT | yes | 12 | 47 | 0.0232 | 0.0234 | 0.0221 | `[0.0221, 0.0234, 0.0238, 0.0226, 0.0241]` | valid SAT |
| `cnf_training_extra__extra_cnf__exact_random3sat_sat_n12_m47_013.cnf` | SAT | yes | 12 | 47 | 0.0281 | 0.0262 | 0.0222 | `[0.0230, 0.0273, 0.0262, 0.0417, 0.0222]` | valid SAT |
| `cnf_training_extra__extra_cnf__exact_random3sat_sat_n13_m47_011.cnf` | SAT | yes | 13 | 47 | 0.0264 | 0.0243 | 0.0221 | `[0.0259, 0.0221, 0.0243, 0.0236, 0.0363]` | valid SAT |
| `cnf_training_extra__extra_cnf__exact_random3sat_sat_n13_m64_004.cnf` | SAT | yes | 13 | 64 | 0.0311 | 0.0266 | 0.0238 | `[0.0433, 0.0266, 0.0243, 0.0374, 0.0238]` | valid SAT |
| `cnf_training_extra__extra_cnf__exact_random3sat_sat_n14_m50_015.cnf` | SAT | yes | 14 | 50 | 0.0291 | 0.0281 | 0.0230 | `[0.0345, 0.0281, 0.0230, 0.0360, 0.0238]` | valid SAT |
| `cnf_training_extra__extra_cnf__exact_random3sat_sat_n15_m68_014.cnf` | SAT | yes | 15 | 68 | 0.0228 | 0.0230 | 0.0218 | `[0.0236, 0.0230, 0.0222, 0.0218, 0.0232]` | valid SAT |
| `cnf_training_extra__extra_cnf__exact_random3sat_sat_n16_m62_016.cnf` | SAT | yes | 16 | 62 | 0.0287 | 0.0278 | 0.0229 | `[0.0278, 0.0241, 0.0313, 0.0229, 0.0372]` | valid SAT |
| `cnf_training_extra__extra_cnf__exact_random3sat_sat_n16_m72_003.cnf` | SAT | yes | 16 | 72 | 0.0303 | 0.0330 | 0.0234 | `[0.0339, 0.0330, 0.0250, 0.0234, 0.0361]` | valid SAT |
| `cnf_training_extra__extra_cnf__exact_random3sat_sat_n8_m31_007.cnf` | SAT | yes | 8 | 31 | 0.0295 | 0.0255 | 0.0234 | `[0.0239, 0.0379, 0.0234, 0.0370, 0.0255]` | valid SAT |
| `cnf_training_extra__extra_cnf__exact_random3sat_sat_n8_m31_009.cnf` | SAT | yes | 8 | 31 | 0.0279 | 0.0235 | 0.0228 | `[0.0354, 0.0235, 0.0228, 0.0231, 0.0349]` | valid SAT |
| `cnf_training_extra__extra_cnf__exact_random3sat_sat_n8_m36_002.cnf` | SAT | yes | 8 | 36 | 0.0286 | 0.0251 | 0.0223 | `[0.0236, 0.0223, 0.0346, 0.0251, 0.0372]` | valid SAT |
| `cnf_training_extra__extra_cnf__exact_random3sat_sat_n8_m36_005.cnf` | SAT | yes | 8 | 36 | 0.0306 | 0.0252 | 0.0238 | `[0.0242, 0.0238, 0.0397, 0.0252, 0.0403]` | valid SAT |
| `cnf_training_extra__extra_cnf__exact_random3sat_sat_n9_m32_018.cnf` | SAT | yes | 9 | 32 | 0.0325 | 0.0352 | 0.0241 | `[0.0352, 0.0371, 0.0258, 0.0406, 0.0241]` | valid SAT |
| `cnf_training_extra__extra_cnf__exact_random3sat_sat_n9_m38_010.cnf` | SAT | yes | 9 | 38 | 0.0316 | 0.0356 | 0.0240 | `[0.0240, 0.0371, 0.0242, 0.0356, 0.0371]` | valid SAT |
| `cnf_training_extra__extra_cnf__exact_random3sat_unsat_n10_m49_015.cnf` | UNSAT | yes | 10 | 49 | 0.0309 | 0.0348 | 0.0228 | `[0.0241, 0.0365, 0.0361, 0.0348, 0.0228]` | valid UNSAT (brute-force checked) |
| `cnf_training_extra__extra_cnf__exact_random3sat_unsat_n11_m54_012.cnf` | UNSAT | yes | 11 | 54 | 0.0312 | 0.0286 | 0.0232 | `[0.0371, 0.0232, 0.0386, 0.0284, 0.0286]` | valid UNSAT (brute-force checked) |
| `cnf_training_extra__extra_cnf__exact_random3sat_unsat_n12_m64_007.cnf` | UNSAT | yes | 12 | 64 | 0.0364 | 0.0362 | 0.0351 | `[0.0355, 0.0384, 0.0362, 0.0365, 0.0351]` | valid UNSAT (brute-force checked) |
| `cnf_training_extra__extra_cnf__exact_random3sat_unsat_n12_m64_013.cnf` | UNSAT | yes | 12 | 64 | 0.0319 | 0.0344 | 0.0237 | `[0.0380, 0.0237, 0.0250, 0.0344, 0.0385]` | valid UNSAT (brute-force checked) |
| `cnf_training_extra__extra_cnf__exact_random3sat_unsat_n13_m69_006.cnf` | UNSAT | yes | 13 | 69 | 0.0261 | 0.0234 | 0.0231 | `[0.0232, 0.0231, 0.0287, 0.0320, 0.0234]` | valid UNSAT (brute-force checked) |
| `cnf_training_extra__extra_cnf__exact_random3sat_unsat_n13_m69_010.cnf` | UNSAT | yes | 13 | 69 | 0.0290 | 0.0245 | 0.0225 | `[0.0372, 0.0245, 0.0225, 0.0227, 0.0383]` | valid UNSAT (brute-force checked) |
| `cnf_training_extra__extra_cnf__exact_random3sat_unsat_n14_m74_017.cnf` | UNSAT | yes | 14 | 74 | 0.0342 | 0.0364 | 0.0249 | `[0.0370, 0.0367, 0.0249, 0.0360, 0.0364]` | valid UNSAT (brute-force checked) |
| `cnf_training_extra__extra_cnf__exact_random3sat_unsat_n15_m68_011.cnf` | UNSAT | yes | 15 | 68 | 0.0285 | 0.0240 | 0.0223 | `[0.0223, 0.0364, 0.0225, 0.0372, 0.0240]` | valid UNSAT (brute-force checked) |
| `cnf_training_extra__extra_cnf__exact_random3sat_unsat_n15_m68_018.cnf` | UNSAT | yes | 15 | 68 | 0.0357 | 0.0338 | 0.0287 | `[0.0338, 0.0287, 0.0444, 0.0294, 0.0422]` | valid UNSAT (brute-force checked) |
| `cnf_training_extra__extra_cnf__exact_random3sat_unsat_n15_m80_014.cnf` | UNSAT | yes | 15 | 80 | 0.0297 | 0.0285 | 0.0229 | `[0.0365, 0.0366, 0.0285, 0.0229, 0.0241]` | valid UNSAT (brute-force checked) |
| `cnf_training_extra__extra_cnf__exact_random3sat_unsat_n16_m78_005.cnf` | UNSAT | yes | 16 | 78 | 0.0243 | 0.0236 | 0.0222 | `[0.0275, 0.0222, 0.0231, 0.0252, 0.0236]` | valid UNSAT (brute-force checked) |
| `cnf_training_extra__extra_cnf__exact_random3sat_unsat_n16_m78_008.cnf` | UNSAT | yes | 16 | 78 | 0.0299 | 0.0285 | 0.0238 | `[0.0238, 0.0354, 0.0285, 0.0366, 0.0251]` | valid UNSAT (brute-force checked) |
| `cnf_training_extra__extra_cnf__exact_random3sat_unsat_n16_m85_002.cnf` | UNSAT | yes | 16 | 85 | 0.0253 | 0.0248 | 0.0223 | `[0.0276, 0.0273, 0.0244, 0.0248, 0.0223]` | valid UNSAT (brute-force checked) |
| `cnf_training_extra__extra_cnf__exact_random3sat_unsat_n16_m85_003.cnf` | UNSAT | yes | 16 | 85 | 0.0274 | 0.0241 | 0.0225 | `[0.0241, 0.0289, 0.0225, 0.0239, 0.0376]` | valid UNSAT (brute-force checked) |
| `cnf_training_extra__extra_cnf__exact_random3sat_unsat_n8_m31_016.cnf` | UNSAT | yes | 8 | 31 | 0.0261 | 0.0242 | 0.0208 | `[0.0213, 0.0392, 0.0242, 0.0249, 0.0208]` | valid UNSAT (brute-force checked) |
| `cnf_training_extra__extra_cnf__exact_random3sat_unsat_n8_m34_009.cnf` | UNSAT | yes | 8 | 34 | 0.0286 | 0.0226 | 0.0218 | `[0.0218, 0.0362, 0.0397, 0.0225, 0.0226]` | valid UNSAT (brute-force checked) |
| `cnf_training_extra__extra_cnf__exact_random3sat_unsat_n9_m38_004.cnf` | UNSAT | yes | 9 | 38 | 0.0293 | 0.0245 | 0.0226 | `[0.0243, 0.0226, 0.0373, 0.0245, 0.0376]` | valid UNSAT (brute-force checked) |
| `cnf_training_extra__extra_cnf__exact_random3sat_unsat_n9_m44_001.cnf` | UNSAT | yes | 9 | 44 | 0.0298 | 0.0271 | 0.0230 | `[0.0247, 0.0356, 0.0230, 0.0271, 0.0387]` | valid UNSAT (brute-force checked) |
| `cnf_training_extra__extra_cnf__graphcolor_k3_complete_K4_unsat.cnf` | UNSAT | yes | 12 | 34 | 0.0293 | 0.0324 | 0.0213 | `[0.0324, 0.0355, 0.0346, 0.0224, 0.0213]` | valid UNSAT (brute-force checked) |
| `cnf_training_extra__extra_cnf__graphcolor_k3_complete_K5_unsat.cnf` | UNSAT | yes | 15 | 50 | 0.0306 | 0.0350 | 0.0220 | `[0.0369, 0.0220, 0.0237, 0.0350, 0.0354]` | valid UNSAT (brute-force checked) |
| `cnf_training_extra__extra_cnf__graphcolor_k3_complete_K6_unsat.cnf` | UNSAT | yes | 18 | 69 | 0.0260 | 0.0232 | 0.0215 | `[0.0232, 0.0253, 0.0223, 0.0378, 0.0215]` | valid UNSAT (format checked) |
| `cnf_training_extra__extra_cnf__graphcolor_k3_planted_v12_e26_001.cnf` | SAT | yes | 36 | 126 | 0.0329 | 0.0345 | 0.0253 | `[0.0253, 0.0347, 0.0345, 0.0338, 0.0361]` | valid SAT |
| `cnf_training_extra__extra_cnf__graphcolor_k3_planted_v16_e35_002.cnf` | SAT | yes | 48 | 169 | 0.0290 | 0.0322 | 0.0218 | `[0.0368, 0.0322, 0.0218, 0.0322, 0.0218]` | valid SAT |
| `cnf_training_extra__extra_cnf__graphcolor_k3_planted_v20_e44_003.cnf` | SAT | yes | 60 | 212 | 0.0348 | 0.0343 | 0.0300 | `[0.0343, 0.0417, 0.0300, 0.0344, 0.0334]` | valid SAT |
| `cnf_training_extra__extra_cnf__graphcolor_k3_planted_v24_e53_004.cnf` | SAT | yes | 72 | 255 | 0.0295 | 0.0278 | 0.0215 | `[0.0373, 0.0265, 0.0342, 0.0215, 0.0278]` | valid SAT |
| `cnf_training_extra__extra_cnf__graphcolor_k3_planted_v30_e66_005.cnf` | SAT | yes | 90 | 318 | 0.0315 | 0.0310 | 0.0229 | `[0.0233, 0.0436, 0.0368, 0.0310, 0.0229]` | valid SAT |
| `cnf_training_extra__extra_cnf__graphcolor_k3_planted_v36_e79_006.cnf` | SAT | yes | 108 | 381 | 0.0372 | 0.0365 | 0.0357 | `[0.0365, 0.0373, 0.0405, 0.0357, 0.0359]` | valid SAT |
| `cnf_training_extra__extra_cnf__graphcolor_k3_planted_v42_e92_007.cnf` | SAT | yes | 126 | 444 | 0.0342 | 0.0378 | 0.0237 | `[0.0237, 0.0421, 0.0405, 0.0378, 0.0267]` | valid SAT |
| `cnf_training_extra__extra_cnf__graphcolor_k3_planted_v50_e110_008.cnf` | SAT | yes | 150 | 530 | 0.0325 | 0.0285 | 0.0268 | `[0.0268, 0.0405, 0.0285, 0.0384, 0.0281]` | valid SAT |
| `cnf_training_extra__extra_cnf__graphcolor_k3_planted_v60_e132_009.cnf` | SAT | yes | 180 | 636 | 0.0348 | 0.0391 | 0.0266 | `[0.0266, 0.0391, 0.0405, 0.0405, 0.0275]` | valid SAT |
| `cnf_training_extra__extra_cnf__graphcolor_k3_planted_v72_e158_010.cnf` | SAT | yes | 216 | 762 | 0.0384 | 0.0419 | 0.0297 | `[0.0297, 0.0427, 0.0304, 0.0419, 0.0475]` | valid SAT |
| `cnf_training_extra__extra_cnf__horn_chain_len12_sat.cnf` | SAT | yes | 12 | 12 | 0.0252 | 0.0230 | 0.0222 | `[0.0237, 0.0230, 0.0222, 0.0229, 0.0344]` | valid SAT |
| `cnf_training_extra__extra_cnf__horn_chain_len12_unsat.cnf` | UNSAT | yes | 12 | 13 | 0.0313 | 0.0326 | 0.0220 | `[0.0357, 0.0360, 0.0220, 0.0326, 0.0302]` | valid UNSAT (brute-force checked) |
| `cnf_training_extra__extra_cnf__horn_chain_len16_sat.cnf` | SAT | yes | 16 | 16 | 0.0258 | 0.0235 | 0.0214 | `[0.0257, 0.0235, 0.0358, 0.0223, 0.0214]` | valid SAT |
| `cnf_training_extra__extra_cnf__horn_chain_len16_unsat.cnf` | UNSAT | yes | 16 | 17 | 0.0325 | 0.0357 | 0.0252 | `[0.0252, 0.0367, 0.0357, 0.0287, 0.0363]` | valid UNSAT (brute-force checked) |
| `cnf_training_extra__extra_cnf__horn_chain_len24_sat.cnf` | SAT | yes | 24 | 24 | 0.0251 | 0.0263 | 0.0217 | `[0.0240, 0.0264, 0.0263, 0.0217, 0.0271]` | valid SAT |
| `cnf_training_extra__extra_cnf__horn_chain_len24_unsat.cnf` | UNSAT | yes | 24 | 25 | 0.0240 | 0.0226 | 0.0201 | `[0.0240, 0.0226, 0.0321, 0.0212, 0.0201]` | valid UNSAT (format checked) |
| `cnf_training_extra__extra_cnf__horn_chain_len32_sat.cnf` | SAT | yes | 32 | 32 | 0.0209 | 0.0201 | 0.0197 | `[0.0201, 0.0201, 0.0197, 0.0219, 0.0230]` | valid SAT |
| `cnf_training_extra__extra_cnf__horn_chain_len32_unsat.cnf` | UNSAT | yes | 32 | 33 | 0.0295 | 0.0277 | 0.0221 | `[0.0342, 0.0260, 0.0277, 0.0221, 0.0376]` | valid UNSAT (format checked) |
| `cnf_training_extra__extra_cnf__horn_chain_len48_sat.cnf` | SAT | yes | 48 | 48 | 0.0310 | 0.0321 | 0.0221 | `[0.0323, 0.0321, 0.0255, 0.0221, 0.0430]` | valid SAT |
| `cnf_training_extra__extra_cnf__horn_chain_len48_unsat.cnf` | UNSAT | yes | 48 | 49 | 0.0215 | 0.0217 | 0.0208 | `[0.0208, 0.0211, 0.0217, 0.0221, 0.0220]` | valid UNSAT (format checked) |
| `cnf_training_extra__extra_cnf__horn_chain_len64_sat.cnf` | SAT | yes | 64 | 64 | 0.0285 | 0.0259 | 0.0221 | `[0.0235, 0.0221, 0.0376, 0.0259, 0.0333]` | valid SAT |
| `cnf_training_extra__extra_cnf__horn_chain_len64_unsat.cnf` | UNSAT | yes | 64 | 65 | 0.0283 | 0.0246 | 0.0231 | `[0.0329, 0.0375, 0.0236, 0.0246, 0.0231]` | valid UNSAT (format checked) |
| `cnf_training_extra__extra_cnf__horn_chain_len8_sat.cnf` | SAT | yes | 8 | 8 | 0.0279 | 0.0236 | 0.0214 | `[0.0236, 0.0214, 0.0360, 0.0236, 0.0350]` | valid SAT |
| `cnf_training_extra__extra_cnf__horn_chain_len8_unsat.cnf` | UNSAT | yes | 8 | 9 | 0.0262 | 0.0236 | 0.0225 | `[0.0381, 0.0245, 0.0236, 0.0225, 0.0225]` | valid UNSAT (brute-force checked) |
| `cnf_training_extra__extra_cnf__nqueens_2x2_unsat.cnf` | UNSAT | yes | 4 | 8 | 0.0253 | 0.0236 | 0.0229 | `[0.0229, 0.0232, 0.0236, 0.0282, 0.0288]` | valid UNSAT (brute-force checked) |
| `cnf_training_extra__extra_cnf__nqueens_3x3_unsat.cnf` | UNSAT | yes | 9 | 31 | 0.0299 | 0.0263 | 0.0235 | `[0.0241, 0.0235, 0.0263, 0.0383, 0.0372]` | valid UNSAT (brute-force checked) |
| `cnf_training_extra__extra_cnf__nqueens_4x4_sat.cnf` | SAT | yes | 16 | 80 | 0.0252 | 0.0238 | 0.0230 | `[0.0315, 0.0235, 0.0238, 0.0230, 0.0241]` | valid SAT |
| `cnf_training_extra__extra_cnf__nqueens_5x5_sat.cnf` | SAT | yes | 25 | 165 | 0.0289 | 0.0237 | 0.0232 | `[0.0352, 0.0233, 0.0237, 0.0232, 0.0393]` | valid SAT |
| `cnf_training_extra__extra_cnf__nqueens_6x6_sat.cnf` | SAT | yes | 36 | 296 | 0.0305 | 0.0282 | 0.0240 | `[0.0361, 0.0282, 0.0246, 0.0396, 0.0240]` | valid SAT |
| `cnf_training_extra__extra_cnf__nqueens_7x7_sat.cnf` | SAT | yes | 49 | 483 | 0.0283 | 0.0263 | 0.0252 | `[0.0370, 0.0252, 0.0266, 0.0263, 0.0263]` | valid SAT |
| `cnf_training_extra__extra_cnf__nqueens_8x8_sat.cnf` | SAT | yes | 64 | 736 | 0.0309 | 0.0297 | 0.0268 | `[0.0407, 0.0301, 0.0273, 0.0297, 0.0268]` | valid SAT |
| `cnf_training_extra__extra_cnf__nqueens_9x9_sat.cnf` | SAT | yes | 81 | 1065 | 0.0384 | 0.0345 | 0.0311 | `[0.0435, 0.0311, 0.0345, 0.0503, 0.0325]` | valid SAT |
| `cnf_training_extra__extra_cnf__pigeonhole_php_10_into_9.cnf` | UNSAT | yes | 90 | 415 | 0.0326 | 0.0352 | 0.0238 | `[0.0352, 0.0238, 0.0360, 0.0370, 0.0310]` | valid UNSAT (format checked) |
| `cnf_training_extra__extra_cnf__pigeonhole_php_4_into_3.cnf` | UNSAT | yes | 12 | 22 | 0.0274 | 0.0292 | 0.0214 | `[0.0292, 0.0226, 0.0313, 0.0323, 0.0214]` | valid UNSAT (brute-force checked) |
| `cnf_training_extra__extra_cnf__pigeonhole_php_5_into_4.cnf` | UNSAT | yes | 20 | 45 | 0.0262 | 0.0217 | 0.0205 | `[0.0329, 0.0217, 0.0217, 0.0342, 0.0205]` | valid UNSAT (format checked) |
| `cnf_training_extra__extra_cnf__pigeonhole_php_6_into_5.cnf` | UNSAT | yes | 30 | 81 | 0.0250 | 0.0223 | 0.0209 | `[0.0218, 0.0223, 0.0228, 0.0209, 0.0373]` | valid UNSAT (format checked) |
| `cnf_training_extra__extra_cnf__pigeonhole_php_7_into_6.cnf` | UNSAT | yes | 42 | 133 | 0.0296 | 0.0296 | 0.0222 | `[0.0265, 0.0343, 0.0222, 0.0354, 0.0296]` | valid UNSAT (format checked) |
| `cnf_training_extra__extra_cnf__pigeonhole_php_8_into_7.cnf` | UNSAT | yes | 56 | 204 | 0.0259 | 0.0241 | 0.0224 | `[0.0241, 0.0264, 0.0231, 0.0336, 0.0224]` | valid UNSAT (format checked) |
| `cnf_training_extra__extra_cnf__pigeonhole_php_9_into_8.cnf` | UNSAT | yes | 72 | 297 | 0.0314 | 0.0350 | 0.0253 | `[0.0253, 0.0359, 0.0351, 0.0350, 0.0258]` | valid UNSAT (format checked) |
| `cnf_training_extra__extra_cnf__planted3sat_n20_m85_001.cnf` | SAT | yes | 20 | 85 | 0.0331 | 0.0357 | 0.0244 | `[0.0357, 0.0392, 0.0244, 0.0377, 0.0284]` | valid SAT |
| `cnf_training_extra__extra_cnf__planted3sat_n20_m85_002.cnf` | SAT | yes | 20 | 85 | 0.0317 | 0.0356 | 0.0227 | `[0.0356, 0.0227, 0.0234, 0.0387, 0.0381]` | valid SAT |
| `cnf_training_extra__extra_cnf__planted3sat_n20_m85_003.cnf` | SAT | yes | 20 | 85 | 0.0330 | 0.0354 | 0.0221 | `[0.0326, 0.0221, 0.0396, 0.0355, 0.0354]` | valid SAT |
| `cnf_training_extra__extra_cnf__planted3sat_n20_m85_004.cnf` | SAT | yes | 20 | 85 | 0.0253 | 0.0237 | 0.0220 | `[0.0329, 0.0237, 0.0220, 0.0245, 0.0236]` | valid SAT |
| `cnf_training_extra__extra_cnf__planted3sat_n20_m85_005.cnf` | SAT | yes | 20 | 85 | 0.0259 | 0.0233 | 0.0213 | `[0.0231, 0.0233, 0.0241, 0.0213, 0.0379]` | valid SAT |
| `cnf_training_extra__extra_cnf__planted3sat_n20_m85_006.cnf` | SAT | yes | 20 | 85 | 0.0290 | 0.0253 | 0.0234 | `[0.0370, 0.0253, 0.0239, 0.0234, 0.0355]` | valid SAT |
| `cnf_training_extra__extra_cnf__planted3sat_n20_m85_007.cnf` | SAT | yes | 20 | 85 | 0.0270 | 0.0262 | 0.0248 | `[0.0262, 0.0288, 0.0252, 0.0248, 0.0303]` | valid SAT |
| `cnf_training_extra__extra_cnf__planted3sat_n20_m85_008.cnf` | SAT | yes | 20 | 85 | 0.0283 | 0.0248 | 0.0234 | `[0.0330, 0.0365, 0.0248, 0.0234, 0.0239]` | valid SAT |
| `cnf_training_extra__extra_cnf__planted3sat_n20_m85_009.cnf` | SAT | yes | 20 | 85 | 0.0311 | 0.0290 | 0.0235 | `[0.0281, 0.0384, 0.0290, 0.0367, 0.0235]` | valid SAT |
| `cnf_training_extra__extra_cnf__planted3sat_n20_m85_010.cnf` | SAT | yes | 20 | 85 | 0.0282 | 0.0238 | 0.0220 | `[0.0339, 0.0220, 0.0234, 0.0380, 0.0238]` | valid SAT |
| `cnf_training_extra__extra_cnf__planted3sat_n30_m128_001.cnf` | SAT | yes | 30 | 128 | 0.0303 | 0.0249 | 0.0242 | `[0.0520, 0.0249, 0.0242, 0.0242, 0.0264]` | valid SAT |
| `cnf_training_extra__extra_cnf__planted3sat_n30_m128_002.cnf` | SAT | yes | 30 | 128 | 0.0276 | 0.0247 | 0.0235 | `[0.0235, 0.0242, 0.0393, 0.0247, 0.0262]` | valid SAT |
| `cnf_training_extra__extra_cnf__planted3sat_n30_m128_003.cnf` | SAT | yes | 30 | 128 | 0.0292 | 0.0254 | 0.0232 | `[0.0254, 0.0368, 0.0232, 0.0252, 0.0356]` | valid SAT |
| `cnf_training_extra__extra_cnf__planted3sat_n30_m128_004.cnf` | SAT | yes | 30 | 128 | 0.0282 | 0.0255 | 0.0242 | `[0.0273, 0.0392, 0.0255, 0.0242, 0.0247]` | valid SAT |
| `cnf_training_extra__extra_cnf__planted3sat_n30_m128_005.cnf` | SAT | yes | 30 | 128 | 0.0347 | 0.0370 | 0.0245 | `[0.0387, 0.0245, 0.0359, 0.0376, 0.0370]` | valid SAT |
| `cnf_training_extra__extra_cnf__planted3sat_n30_m128_006.cnf` | SAT | yes | 30 | 128 | 0.0306 | 0.0342 | 0.0237 | `[0.0342, 0.0237, 0.0238, 0.0361, 0.0354]` | valid SAT |
| `cnf_training_extra__extra_cnf__planted3sat_n30_m128_007.cnf` | SAT | yes | 30 | 128 | 0.0301 | 0.0264 | 0.0230 | `[0.0230, 0.0264, 0.0376, 0.0258, 0.0376]` | valid SAT |
| `cnf_training_extra__extra_cnf__planted3sat_n30_m128_008.cnf` | SAT | yes | 30 | 128 | 0.0293 | 0.0256 | 0.0237 | `[0.0372, 0.0356, 0.0237, 0.0242, 0.0256]` | valid SAT |
| `cnf_training_extra__extra_cnf__planted3sat_n30_m128_009.cnf` | SAT | yes | 30 | 128 | 0.0333 | 0.0353 | 0.0232 | `[0.0376, 0.0355, 0.0232, 0.0348, 0.0353]` | valid SAT |
| `cnf_training_extra__extra_cnf__planted3sat_n30_m128_010.cnf` | SAT | yes | 30 | 128 | 0.0309 | 0.0263 | 0.0242 | `[0.0401, 0.0263, 0.0260, 0.0242, 0.0379]` | valid SAT |
| `cnf_training_extra__extra_cnf__planted3sat_n40_m170_001.cnf` | SAT | yes | 40 | 170 | 0.0309 | 0.0305 | 0.0249 | `[0.0305, 0.0387, 0.0249, 0.0349, 0.0257]` | valid SAT |
| `cnf_training_extra__extra_cnf__planted3sat_n40_m170_002.cnf` | SAT | yes | 40 | 170 | 0.0304 | 0.0239 | 0.0231 | `[0.0414, 0.0401, 0.0231, 0.0239, 0.0234]` | valid SAT |
| `cnf_training_extra__extra_cnf__planted3sat_n40_m170_003.cnf` | SAT | yes | 40 | 170 | 0.0308 | 0.0284 | 0.0226 | `[0.0231, 0.0396, 0.0226, 0.0401, 0.0284]` | valid SAT |
| `cnf_training_extra__extra_cnf__planted3sat_n40_m170_004.cnf` | SAT | yes | 40 | 170 | 0.0332 | 0.0357 | 0.0256 | `[0.0281, 0.0357, 0.0371, 0.0256, 0.0394]` | valid SAT |
| `cnf_training_extra__extra_cnf__planted3sat_n40_m170_005.cnf` | SAT | yes | 40 | 170 | 0.0289 | 0.0258 | 0.0253 | `[0.0289, 0.0254, 0.0389, 0.0258, 0.0253]` | valid SAT |
| `cnf_training_extra__extra_cnf__planted3sat_n40_m170_006.cnf` | SAT | yes | 40 | 170 | 0.0322 | 0.0302 | 0.0247 | `[0.0426, 0.0302, 0.0253, 0.0247, 0.0382]` | valid SAT |
| `cnf_training_extra__extra_cnf__planted3sat_n40_m170_007.cnf` | SAT | yes | 40 | 170 | 0.0377 | 0.0389 | 0.0328 | `[0.0366, 0.0396, 0.0389, 0.0328, 0.0408]` | valid SAT |
| `cnf_training_extra__extra_cnf__planted3sat_n40_m170_008.cnf` | SAT | yes | 40 | 170 | 0.0311 | 0.0307 | 0.0244 | `[0.0246, 0.0307, 0.0369, 0.0388, 0.0244]` | valid SAT |
| `cnf_training_extra__extra_cnf__planted3sat_n40_m170_009.cnf` | SAT | yes | 40 | 170 | 0.0311 | 0.0343 | 0.0221 | `[0.0343, 0.0221, 0.0392, 0.0252, 0.0349]` | valid SAT |
| `cnf_training_extra__extra_cnf__planted3sat_n40_m170_010.cnf` | SAT | yes | 40 | 170 | 0.0290 | 0.0245 | 0.0229 | `[0.0229, 0.0367, 0.0236, 0.0245, 0.0373]` | valid SAT |
| `cnf_training_extra__extra_cnf__planted3sat_n60_m255_001.cnf` | SAT | yes | 60 | 255 | 0.0332 | 0.0330 | 0.0274 | `[0.0330, 0.0274, 0.0292, 0.0388, 0.0378]` | valid SAT |
| `cnf_training_extra__extra_cnf__planted3sat_n60_m255_002.cnf` | SAT | yes | 60 | 255 | 0.0334 | 0.0366 | 0.0248 | `[0.0403, 0.0273, 0.0366, 0.0378, 0.0248]` | valid SAT |
| `cnf_training_extra__extra_cnf__planted3sat_n60_m255_003.cnf` | SAT | yes | 60 | 255 | 0.0326 | 0.0309 | 0.0246 | `[0.0403, 0.0400, 0.0272, 0.0309, 0.0246]` | valid SAT |
| `cnf_training_extra__extra_cnf__planted3sat_n60_m255_004.cnf` | SAT | yes | 60 | 255 | 0.0319 | 0.0275 | 0.0251 | `[0.0391, 0.0251, 0.0275, 0.0415, 0.0265]` | valid SAT |
| `cnf_training_extra__extra_cnf__planted3sat_n60_m255_005.cnf` | SAT | yes | 60 | 255 | 0.0303 | 0.0295 | 0.0254 | `[0.0254, 0.0321, 0.0295, 0.0367, 0.0276]` | valid SAT |
| `cnf_training_extra__extra_cnf__planted3sat_n60_m255_006.cnf` | SAT | yes | 60 | 255 | 0.0273 | 0.0287 | 0.0229 | `[0.0293, 0.0307, 0.0248, 0.0229, 0.0287]` | valid SAT |
| `cnf_training_extra__extra_cnf__planted3sat_n60_m255_007.cnf` | SAT | yes | 60 | 255 | 0.0382 | 0.0389 | 0.0330 | `[0.0387, 0.0330, 0.0390, 0.0415, 0.0389]` | valid SAT |
| `cnf_training_extra__extra_cnf__planted3sat_n60_m255_008.cnf` | SAT | yes | 60 | 255 | 0.0293 | 0.0267 | 0.0264 | `[0.0267, 0.0269, 0.0266, 0.0401, 0.0264]` | valid SAT |
| `cnf_training_extra__extra_cnf__planted3sat_n80_m340_001.cnf` | SAT | yes | 80 | 340 | 0.0400 | 0.0428 | 0.0331 | `[0.0355, 0.0436, 0.0331, 0.0428, 0.0448]` | valid SAT |
| `cnf_training_extra__extra_cnf__planted3sat_n80_m340_002.cnf` | SAT | yes | 80 | 340 | 0.0373 | 0.0379 | 0.0284 | `[0.0379, 0.0284, 0.0327, 0.0447, 0.0429]` | valid SAT |
| `cnf_training_extra__extra_cnf__planted3sat_n80_m340_003.cnf` | SAT | yes | 80 | 340 | 0.0316 | 0.0299 | 0.0243 | `[0.0299, 0.0388, 0.0397, 0.0255, 0.0243]` | valid SAT |
| `cnf_training_extra__extra_cnf__planted3sat_n80_m340_004.cnf` | SAT | yes | 80 | 340 | 0.0258 | 0.0254 | 0.0241 | `[0.0254, 0.0254, 0.0267, 0.0241, 0.0272]` | valid SAT |
| `cnf_training_extra__extra_cnf__planted3sat_n80_m340_005.cnf` | SAT | yes | 80 | 340 | 0.0293 | 0.0275 | 0.0247 | `[0.0308, 0.0275, 0.0387, 0.0247, 0.0247]` | valid SAT |
| `cnf_training_extra__extra_cnf__planted3sat_n80_m340_006.cnf` | SAT | yes | 80 | 340 | 0.0311 | 0.0303 | 0.0238 | `[0.0347, 0.0290, 0.0377, 0.0303, 0.0238]` | valid SAT |
| `cnf_training_extra__extra_cnf__xor_parity_sat_n18_eq18_w3_001.cnf` | SAT | yes | 18 | 72 | 0.0265 | 0.0250 | 0.0220 | `[0.0220, 0.0304, 0.0226, 0.0325, 0.0250]` | valid SAT |
| `cnf_training_extra__extra_cnf__xor_parity_sat_n24_eq24_w3_002.cnf` | SAT | yes | 24 | 96 | 0.0240 | 0.0218 | 0.0214 | `[0.0218, 0.0216, 0.0214, 0.0328, 0.0224]` | valid SAT |
| `cnf_training_extra__extra_cnf__xor_parity_sat_n30_eq30_w3_003.cnf` | SAT | yes | 30 | 120 | 0.0229 | 0.0226 | 0.0218 | `[0.0218, 0.0224, 0.0226, 0.0239, 0.0239]` | valid SAT |
| `cnf_training_extra__extra_cnf__xor_parity_sat_n32_eq20_w4_007.cnf` | SAT | yes | 32 | 160 | 0.0273 | 0.0232 | 0.0226 | `[0.0228, 0.0251, 0.0232, 0.0428, 0.0226]` | valid SAT |
| `cnf_training_extra__extra_cnf__xor_parity_sat_n40_eq35_w3_004.cnf` | SAT | yes | 40 | 140 | 0.0336 | 0.0361 | 0.0251 | `[0.0361, 0.0391, 0.0251, 0.0286, 0.0392]` | valid SAT |
| `cnf_training_extra__extra_cnf__xor_parity_sat_n48_eq28_w4_008.cnf` | SAT | yes | 48 | 224 | 0.0301 | 0.0257 | 0.0252 | `[0.0255, 0.0252, 0.0381, 0.0257, 0.0360]` | valid SAT |
| `cnf_training_extra__extra_cnf__xor_parity_sat_n60_eq45_w3_005.cnf` | SAT | yes | 60 | 180 | 0.0336 | 0.0371 | 0.0265 | `[0.0371, 0.0265, 0.0385, 0.0275, 0.0385]` | valid SAT |
| `cnf_training_extra__extra_cnf__xor_parity_sat_n80_eq55_w3_006.cnf` | SAT | yes | 80 | 220 | 0.0322 | 0.0279 | 0.0257 | `[0.0395, 0.0266, 0.0279, 0.0257, 0.0413]` | valid SAT |
| `cnf_training_extra__extra_cnf__xor_parity_unsat_n18_eq12_w3_001.cnf` | UNSAT | yes | 18 | 48 | 0.0267 | 0.0236 | 0.0228 | `[0.0235, 0.0352, 0.0228, 0.0236, 0.0286]` | valid UNSAT (format checked) |
| `cnf_training_extra__extra_cnf__xor_parity_unsat_n24_eq16_w3_002.cnf` | UNSAT | yes | 24 | 64 | 0.0307 | 0.0273 | 0.0242 | `[0.0418, 0.0259, 0.0343, 0.0242, 0.0273]` | valid UNSAT (format checked) |
| `cnf_training_extra__extra_cnf__xor_parity_unsat_n30_eq20_w3_003.cnf` | UNSAT | yes | 30 | 80 | 0.0281 | 0.0239 | 0.0226 | `[0.0226, 0.0239, 0.0344, 0.0363, 0.0236]` | valid UNSAT (format checked) |
| `cnf_training_extra__extra_cnf__xor_parity_unsat_n32_eq18_w4_006.cnf` | UNSAT | yes | 32 | 144 | 0.0350 | 0.0368 | 0.0265 | `[0.0338, 0.0368, 0.0265, 0.0409, 0.0372]` | valid UNSAT (format checked) |
| `cnf_training_extra__extra_cnf__xor_parity_unsat_n40_eq24_w3_004.cnf` | UNSAT | yes | 40 | 96 | 0.0335 | 0.0366 | 0.0264 | `[0.0264, 0.0265, 0.0411, 0.0366, 0.0369]` | valid UNSAT (format checked) |
| `cnf_training_extra__extra_cnf__xor_parity_unsat_n60_eq32_w3_005.cnf` | UNSAT | yes | 60 | 128 | 0.0252 | 0.0253 | 0.0225 | `[0.0253, 0.0225, 0.0281, 0.0254, 0.0246]` | valid UNSAT (format checked) |
| `large__test_1.cnf` | SAT | yes | 373 | 811 | 0.0428 | 0.0433 | 0.0341 | `[0.0508, 0.0498, 0.0360, 0.0341, 0.0433]` | valid SAT |
| `large__test_10.cnf` | UNSAT | yes | 229 | 1280 | 0.8393 | 0.8487 | 0.8121 | `[0.8121, 0.8316, 0.8518, 0.8522, 0.8487]` | valid UNSAT (format checked) |
| `large__test_2.cnf` | SAT | yes | 319 | 573 | 0.0368 | 0.0397 | 0.0311 | `[0.0323, 0.0311, 0.0411, 0.0399, 0.0397]` | valid SAT |
| `large__test_3.cnf` | UNSAT | yes | 227 | 1460 | 0.2905 | 0.2906 | 0.2745 | `[0.2892, 0.3040, 0.2906, 0.2745, 0.2940]` | valid UNSAT (format checked) |
| `large__test_4.cnf` | UNSAT | yes | 219 | 1363 | 0.2539 | 0.2464 | 0.2441 | `[0.2689, 0.2657, 0.2464, 0.2445, 0.2441]` | valid UNSAT (format checked) |
| `large__test_5.cnf` | SAT | yes | 244 | 772 | 0.0300 | 0.0287 | 0.0273 | `[0.0273, 0.0345, 0.0274, 0.0287, 0.0321]` | valid SAT |
| `large__test_6.cnf` | UNSAT | yes | 271 | 1393 | 3.4607 | 3.4579 | 3.4365 | `[3.4365, 3.4495, 3.4579, 3.4583, 3.5015]` | valid UNSAT (format checked) |
| `large__test_7.cnf` | SAT | yes | 389 | 863 | 0.0461 | 0.0496 | 0.0331 | `[0.0351, 0.0496, 0.0331, 0.0590, 0.0538]` | valid SAT |
| `large__test_8.cnf` | SAT | yes | 298 | 1210 | 0.1318 | 0.1256 | 0.1228 | `[0.1407, 0.1460, 0.1256, 0.1228, 0.1238]` | valid SAT |
| `large__test_9.cnf` | SAT | yes | 365 | 969 | 0.0365 | 0.0344 | 0.0327 | `[0.0327, 0.0344, 0.0336, 0.0445, 0.0376]` | valid SAT |
| `medium__test_1.cnf` | UNSAT | yes | 63 | 835 | 0.0364 | 0.0311 | 0.0301 | `[0.0426, 0.0479, 0.0304, 0.0301, 0.0311]` | valid UNSAT (format checked) |
| `medium__test_10.cnf` | UNSAT | yes | 68 | 822 | 0.0354 | 0.0304 | 0.0302 | `[0.0427, 0.0303, 0.0436, 0.0304, 0.0302]` | valid UNSAT (format checked) |
| `medium__test_2.cnf` | UNSAT | yes | 69 | 352 | 0.0346 | 0.0344 | 0.0298 | `[0.0397, 0.0344, 0.0299, 0.0298, 0.0393]` | valid UNSAT (format checked) |
| `medium__test_3.cnf` | UNSAT | yes | 172 | 774 | 0.5012 | 0.5024 | 0.4869 | `[0.4869, 0.5135, 0.5024, 0.5151, 0.4879]` | valid UNSAT (format checked) |
| `medium__test_4.cnf` | UNSAT | yes | 191 | 886 | 0.8544 | 0.8662 | 0.8242 | `[0.8714, 0.8428, 0.8662, 0.8242, 0.8676]` | valid UNSAT (format checked) |
| `medium__test_5.cnf` | UNSAT | yes | 55 | 713 | 0.0344 | 0.0310 | 0.0287 | `[0.0287, 0.0404, 0.0290, 0.0431, 0.0310]` | valid UNSAT (format checked) |
| `medium__test_6.cnf` | UNSAT | yes | 61 | 512 | 0.0380 | 0.0365 | 0.0344 | `[0.0365, 0.0458, 0.0382, 0.0344, 0.0351]` | valid UNSAT (format checked) |
| `medium__test_7.cnf` | UNSAT | yes | 75 | 562 | 0.0364 | 0.0385 | 0.0270 | `[0.0385, 0.0410, 0.0332, 0.0270, 0.0422]` | valid UNSAT (format checked) |
| `medium__test_8.cnf` | SAT | yes | 130 | 333 | 0.0305 | 0.0262 | 0.0247 | `[0.0383, 0.0247, 0.0383, 0.0262, 0.0252]` | valid SAT |
| `medium__test_9.cnf` | SAT | yes | 138 | 379 | 0.0409 | 0.0405 | 0.0266 | `[0.0443, 0.0266, 0.0397, 0.0534, 0.0405]` | valid SAT |
| `satlib_more__aim-100-1_6-no-1.cnf` | UNSAT | yes | 100 | 160 | 0.0383 | 0.0414 | 0.0263 | `[0.0414, 0.0330, 0.0461, 0.0447, 0.0263]` | valid UNSAT (format checked) |
| `satlib_more__aim-100-1_6-no-2.cnf` | UNSAT | yes | 100 | 160 | 0.0312 | 0.0280 | 0.0246 | `[0.0280, 0.0398, 0.0248, 0.0385, 0.0246]` | valid UNSAT (format checked) |
| `satlib_more__aim-100-1_6-yes1-1.cnf` | SAT | yes | 100 | 160 | 0.0319 | 0.0307 | 0.0255 | `[0.0390, 0.0255, 0.0260, 0.0307, 0.0384]` | valid SAT |
| `satlib_more__aim-100-1_6-yes1-2.cnf` | SAT | yes | 100 | 160 | 0.0355 | 0.0385 | 0.0253 | `[0.0385, 0.0253, 0.0412, 0.0291, 0.0432]` | valid SAT |
| `satlib_more__flat75-1.cnf` | SAT | yes | 225 | 840 | 0.0410 | 0.0418 | 0.0322 | `[0.0418, 0.0418, 0.0438, 0.0452, 0.0322]` | valid SAT |
| `satlib_more__flat75-10.cnf` | SAT | yes | 225 | 840 | 0.0332 | 0.0336 | 0.0312 | `[0.0312, 0.0342, 0.0321, 0.0336, 0.0350]` | valid SAT |
| `satlib_more__jnh1.cnf` | SAT | yes | 100 | 850 | 0.0372 | 0.0339 | 0.0313 | `[0.0313, 0.0462, 0.0414, 0.0339, 0.0332]` | valid SAT |
| `satlib_more__jnh10.cnf` | UNSAT | yes | 100 | 850 | 0.0396 | 0.0416 | 0.0328 | `[0.0474, 0.0420, 0.0416, 0.0340, 0.0328]` | valid UNSAT (format checked) |
| `satlib_more__uf125-01.cnf` | SAT | yes | 125 | 538 | 0.0354 | 0.0311 | 0.0295 | `[0.0295, 0.0402, 0.0306, 0.0458, 0.0311]` | valid SAT |
| `satlib_more__uf125-010.cnf` | SAT | yes | 125 | 538 | 0.0872 | 0.0834 | 0.0786 | `[0.0793, 0.0953, 0.0993, 0.0834, 0.0786]` | valid SAT |
| `satlib_more__uf150-01.cnf` | SAT | yes | 150 | 645 | 0.0533 | 0.0509 | 0.0465 | `[0.0465, 0.0606, 0.0509, 0.0509, 0.0575]` | valid SAT |
| `satlib_more__uuf125-01.cnf` | UNSAT | yes | 125 | 538 | 0.0954 | 0.0918 | 0.0877 | `[0.0877, 0.0913, 0.1035, 0.0918, 0.1027]` | valid UNSAT (format checked) |
| `satlib_more__uuf125-010.cnf` | UNSAT | yes | 125 | 538 | 0.1518 | 0.1523 | 0.1401 | `[0.1462, 0.1401, 0.1567, 0.1523, 0.1636]` | valid UNSAT (format checked) |
| `satlib_more__uuf150-01.cnf` | UNSAT | yes | 150 | 645 | 0.3439 | 0.3444 | 0.3336 | `[0.3568, 0.3444, 0.3336, 0.3379, 0.3466]` | valid UNSAT (format checked) |
| `satlib_subset__dubois20.cnf` | UNSAT | yes | 60 | 160 | 0.0247 | 0.0224 | 0.0203 | `[0.0219, 0.0225, 0.0363, 0.0224, 0.0203]` | valid UNSAT (format checked) |
| `satlib_subset__dubois21.cnf` | UNSAT | yes | 63 | 168 | 0.0278 | 0.0238 | 0.0215 | `[0.0379, 0.0332, 0.0215, 0.0238, 0.0227]` | valid UNSAT (format checked) |
| `satlib_subset__flat50-1.cnf` | SAT | yes | 150 | 545 | 0.0484 | 0.0463 | 0.0393 | `[0.0393, 0.0422, 0.0619, 0.0520, 0.0463]` | valid SAT |
| `satlib_subset__flat50-10.cnf` | SAT | yes | 150 | 545 | 0.0328 | 0.0344 | 0.0284 | `[0.0353, 0.0295, 0.0284, 0.0344, 0.0364]` | valid SAT |
| `satlib_subset__hole10.cnf` | UNSAT | yes | 110 | 561 | 0.0279 | 0.0248 | 0.0234 | `[0.0382, 0.0248, 0.0234, 0.0286, 0.0244]` | valid UNSAT (format checked) |
| `satlib_subset__hole8.cnf` | UNSAT | yes | 72 | 297 | 0.0291 | 0.0246 | 0.0230 | `[0.0385, 0.0239, 0.0353, 0.0230, 0.0246]` | valid UNSAT (format checked) |
| `satlib_subset__uf100-01.cnf` | SAT | yes | 100 | 430 | 0.0581 | 0.0610 | 0.0512 | `[0.0610, 0.0621, 0.0524, 0.0512, 0.0637]` | valid SAT |
| `satlib_subset__uf100-010.cnf` | SAT | yes | 100 | 430 | 0.0314 | 0.0285 | 0.0267 | `[0.0275, 0.0346, 0.0285, 0.0267, 0.0399]` | valid SAT |
| `satlib_subset__uuf100-01.cnf` | UNSAT | yes | 100 | 430 | 0.0533 | 0.0510 | 0.0433 | `[0.0433, 0.0510, 0.0665, 0.0601, 0.0453]` | valid UNSAT (format checked) |
| `satlib_subset__uuf100-010.cnf` | UNSAT | yes | 100 | 430 | 0.0633 | 0.0590 | 0.0581 | `[0.0728, 0.0581, 0.0581, 0.0590, 0.0686]` | valid UNSAT (format checked) |
| `small__test_1.cnf` | SAT | yes | 19 | 26 | 0.0264 | 0.0237 | 0.0231 | `[0.0237, 0.0247, 0.0233, 0.0373, 0.0231]` | valid SAT |
| `small__test_10.cnf` | UNSAT | yes | 22 | 174 | 0.0362 | 0.0392 | 0.0248 | `[0.0258, 0.0512, 0.0397, 0.0392, 0.0248]` | valid UNSAT (format checked) |
| `small__test_2.cnf` | SAT | yes | 46 | 176 | 0.0349 | 0.0355 | 0.0271 | `[0.0348, 0.0381, 0.0355, 0.0271, 0.0393]` | valid SAT |
| `small__test_3.cnf` | SAT | yes | 41 | 150 | 0.0357 | 0.0391 | 0.0252 | `[0.0391, 0.0252, 0.0346, 0.0396, 0.0400]` | valid SAT |
| `small__test_4.cnf` | UNSAT | yes | 30 | 167 | 0.0314 | 0.0345 | 0.0253 | `[0.0254, 0.0345, 0.0347, 0.0253, 0.0373]` | valid UNSAT (format checked) |
| `small__test_5.cnf` | SAT | yes | 20 | 40 | 0.0318 | 0.0335 | 0.0255 | `[0.0362, 0.0381, 0.0257, 0.0255, 0.0335]` | valid SAT |
| `small__test_6.cnf` | SAT | yes | 42 | 70 | 0.0313 | 0.0314 | 0.0247 | `[0.0247, 0.0314, 0.0372, 0.0373, 0.0259]` | valid SAT |
| `small__test_7.cnf` | SAT | yes | 49 | 167 | 0.0319 | 0.0346 | 0.0245 | `[0.0346, 0.0387, 0.0245, 0.0368, 0.0246]` | valid SAT |
| `small__test_8.cnf` | UNSAT | yes | 14 | 68 | 0.0294 | 0.0264 | 0.0223 | `[0.0264, 0.0370, 0.0365, 0.0246, 0.0223]` | valid UNSAT (brute-force checked) |
| `small__test_9.cnf` | SAT | yes | 40 | 100 | 0.0333 | 0.0301 | 0.0269 | `[0.0387, 0.0301, 0.0269, 0.0294, 0.0413]` | valid SAT |
| `special__dense.cnf` | UNSAT | yes | 200 | 1500 | 0.1283 | 0.1341 | 0.1141 | `[0.1367, 0.1341, 0.1367, 0.1198, 0.1141]` | valid UNSAT (format checked) |
| `special__easy.cnf` | SAT | yes | 200 | 400 | 0.0361 | 0.0394 | 0.0273 | `[0.0273, 0.0413, 0.0406, 0.0394, 0.0318]` | valid SAT |
| `special__hard.cnf` | UNSAT | yes | 200 | 850 | 2.5014 | 2.5018 | 2.4651 | `[2.5242, 2.4870, 2.5289, 2.5018, 2.4651]` | valid UNSAT (format checked) |
| `special__pigeonhole.cnf` | UNSAT | yes | 90 | 415 | 0.0317 | 0.0369 | 0.0223 | `[0.0390, 0.0225, 0.0369, 0.0223, 0.0377]` | valid UNSAT (format checked) |
| `special__tseitin.cnf` | UNSAT | yes | 40 | 160 | 0.0274 | 0.0241 | 0.0232 | `[0.0367, 0.0241, 0.0289, 0.0240, 0.0232]` | valid UNSAT (format checked) |
