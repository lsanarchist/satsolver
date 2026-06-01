# SAT Solver Formulae Avg5 Benchmark Current

Generated: 2026-05-31T22:49:39
Dataset: `formulae current solver after the Mycielski detector`
Source benchmark output: `/tmp/satsolver_formulae_avg5.txt`
Solver: `satsolver`
Mode: `cli`
CLI script: `/home/doomguy/Desktop/sat/satsolver/satsolver.py`
Python executable: `/usr/bin/python`
Repeats: `5`
Bruteforce var limit: `16`
Metric note: `avg5 total` is `measured total / 5`, i.e. the mean runtime over five CLI runs per case. `median total` is the benchmark harness representative median sum.

## Overall

| cases | solved | errors | SAT | UNSAT | avg5 total s | median total s | avg/case s | median/case s | max median-case s | measured total s | wall clock s |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 35 | 35 | 0 | 16 | 19 | 10.0218 | 9.9223 | 0.2863 | 0.0329 | 3.4841 | 50.1091 | 50.5158 |

## Folder Summary

| folder | cases | solved | errors | SAT | UNSAT | avg5 total s | median total s | avg/case s | median/case s | max median-case s | measured total s |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| `small` | 10 | 10 | 0 | 7 | 3 | 0.2921 | 0.2767 | 0.0292 | 0.0271 | 0.0352 | 1.4606 |
| `medium` | 10 | 10 | 0 | 2 | 8 | 1.6634 | 1.6523 | 0.1663 | 0.0381 | 0.8714 | 8.3172 |
| `large` | 10 | 10 | 0 | 6 | 4 | 5.2608 | 5.1713 | 0.5261 | 0.0889 | 3.4841 | 26.3039 |
| `special` | 5 | 5 | 0 | 1 | 4 | 2.8055 | 2.8220 | 0.5611 | 0.0291 | 2.6231 | 14.0274 |

## Slowest Cases By Avg5

| case | result | vars | clauses | avg5 s | median s | best s | samples | validation |
|---|---|---:|---:|---:|---:|---:|---|---|
| `large/test_6.cnf` | UNSAT | 271 | 1393 | 3.5338 | 3.4841 | 3.3731 | `[3.3731, 3.4841, 3.4745, 3.7079, 3.6295]` | valid UNSAT (format checked) |
| `special/hard.cnf` | UNSAT | 200 | 850 | 2.5972 | 2.6231 | 2.4641 | `[2.4641, 2.6231, 2.6529, 2.6614, 2.5846]` | valid UNSAT (format checked) |
| `medium/test_4.cnf` | UNSAT | 191 | 886 | 0.8800 | 0.8714 | 0.8585 | `[0.8585, 0.9213, 0.8818, 0.8671, 0.8714]` | valid UNSAT (format checked) |
| `large/test_10.cnf` | UNSAT | 229 | 1280 | 0.8642 | 0.8374 | 0.8253 | `[0.8374, 0.9685, 0.8253, 0.8584, 0.8315]` | valid UNSAT (format checked) |
| `medium/test_3.cnf` | UNSAT | 172 | 774 | 0.4964 | 0.4950 | 0.4722 | `[0.4907, 0.5142, 0.4722, 0.4950, 0.5101]` | valid UNSAT (format checked) |
| `large/test_3.cnf` | UNSAT | 227 | 1460 | 0.2937 | 0.2891 | 0.2788 | `[0.3006, 0.2852, 0.3145, 0.2891, 0.2788]` | valid UNSAT (format checked) |
| `large/test_4.cnf` | UNSAT | 219 | 1363 | 0.2498 | 0.2470 | 0.2299 | `[0.2299, 0.2416, 0.2715, 0.2589, 0.2470]` | valid UNSAT (format checked) |
| `large/test_8.cnf` | SAT | 298 | 1210 | 0.1265 | 0.1293 | 0.1115 | `[0.1263, 0.1358, 0.1115, 0.1293, 0.1294]` | valid SAT |
| `special/dense.cnf` | UNSAT | 200 | 1500 | 0.1214 | 0.1199 | 0.1161 | `[0.1304, 0.1213, 0.1191, 0.1199, 0.1161]` | valid UNSAT (format checked) |
| `large/test_1.cnf` | SAT | 373 | 811 | 0.0467 | 0.0484 | 0.0393 | `[0.0484, 0.0496, 0.0488, 0.0393, 0.0474]` | valid SAT |
| `medium/test_6.cnf` | UNSAT | 61 | 512 | 0.0391 | 0.0417 | 0.0288 | `[0.0417, 0.0430, 0.0368, 0.0452, 0.0288]` | valid UNSAT (format checked) |
| `large/test_7.cnf` | SAT | 389 | 863 | 0.0390 | 0.0360 | 0.0332 | `[0.0360, 0.0417, 0.0353, 0.0488, 0.0332]` | valid SAT |
| `medium/test_10.cnf` | UNSAT | 68 | 822 | 0.0386 | 0.0406 | 0.0292 | `[0.0292, 0.0406, 0.0414, 0.0405, 0.0411]` | valid UNSAT (format checked) |
| `large/test_9.cnf` | SAT | 365 | 969 | 0.0382 | 0.0362 | 0.0332 | `[0.0362, 0.0362, 0.0453, 0.0400, 0.0332]` | valid SAT |
| `large/test_2.cnf` | SAT | 319 | 573 | 0.0373 | 0.0329 | 0.0306 | `[0.0329, 0.0448, 0.0306, 0.0465, 0.0315]` | valid SAT |
| `medium/test_7.cnf` | UNSAT | 75 | 562 | 0.0363 | 0.0318 | 0.0293 | `[0.0318, 0.0449, 0.0296, 0.0461, 0.0293]` | valid UNSAT (format checked) |
| `medium/test_5.cnf` | UNSAT | 55 | 713 | 0.0358 | 0.0385 | 0.0284 | `[0.0385, 0.0320, 0.0284, 0.0407, 0.0392]` | valid UNSAT (format checked) |
| `medium/test_9.cnf` | SAT | 138 | 379 | 0.0346 | 0.0324 | 0.0271 | `[0.0324, 0.0408, 0.0414, 0.0313, 0.0271]` | valid SAT |
| `medium/test_8.cnf` | SAT | 130 | 333 | 0.0345 | 0.0378 | 0.0274 | `[0.0398, 0.0277, 0.0378, 0.0398, 0.0274]` | valid SAT |
| `medium/test_1.cnf` | UNSAT | 63 | 835 | 0.0342 | 0.0309 | 0.0289 | `[0.0390, 0.0309, 0.0422, 0.0297, 0.0289]` | valid UNSAT (format checked) |

## All Cases

| case | result | ok | vars | clauses | avg5 s | median s | best s | samples | validation |
|---|---|---:|---:|---:|---:|---:|---:|---|---|
| `small/test_1.cnf` | SAT | yes | 19 | 26 | 0.0281 | 0.0243 | 0.0224 | `[0.0229, 0.0345, 0.0243, 0.0364, 0.0224]` | valid SAT |
| `small/test_10.cnf` | UNSAT | yes | 22 | 174 | 0.0276 | 0.0263 | 0.0243 | `[0.0243, 0.0263, 0.0342, 0.0254, 0.0274]` | valid UNSAT (format checked) |
| `small/test_2.cnf` | SAT | yes | 46 | 176 | 0.0297 | 0.0284 | 0.0222 | `[0.0247, 0.0353, 0.0222, 0.0379, 0.0284]` | valid SAT |
| `small/test_3.cnf` | SAT | yes | 41 | 150 | 0.0294 | 0.0271 | 0.0250 | `[0.0260, 0.0250, 0.0271, 0.0382, 0.0305]` | valid SAT |
| `small/test_4.cnf` | UNSAT | yes | 30 | 167 | 0.0287 | 0.0263 | 0.0230 | `[0.0353, 0.0343, 0.0263, 0.0244, 0.0230]` | valid UNSAT (format checked) |
| `small/test_5.cnf` | SAT | yes | 20 | 40 | 0.0310 | 0.0352 | 0.0236 | `[0.0352, 0.0372, 0.0355, 0.0236, 0.0237]` | valid SAT |
| `small/test_6.cnf` | SAT | yes | 42 | 70 | 0.0279 | 0.0269 | 0.0234 | `[0.0238, 0.0370, 0.0234, 0.0269, 0.0283]` | valid SAT |
| `small/test_7.cnf` | SAT | yes | 49 | 167 | 0.0288 | 0.0273 | 0.0255 | `[0.0255, 0.0373, 0.0262, 0.0275, 0.0273]` | valid SAT |
| `small/test_8.cnf` | UNSAT | yes | 14 | 68 | 0.0314 | 0.0272 | 0.0262 | `[0.0262, 0.0272, 0.0272, 0.0393, 0.0373]` | valid UNSAT (brute-force checked) |
| `small/test_9.cnf` | SAT | yes | 40 | 100 | 0.0296 | 0.0277 | 0.0230 | `[0.0385, 0.0230, 0.0357, 0.0277, 0.0234]` | valid SAT |
| `medium/test_1.cnf` | UNSAT | yes | 63 | 835 | 0.0342 | 0.0309 | 0.0289 | `[0.0390, 0.0309, 0.0422, 0.0297, 0.0289]` | valid UNSAT (format checked) |
| `medium/test_10.cnf` | UNSAT | yes | 68 | 822 | 0.0386 | 0.0406 | 0.0292 | `[0.0292, 0.0406, 0.0414, 0.0405, 0.0411]` | valid UNSAT (format checked) |
| `medium/test_2.cnf` | UNSAT | yes | 69 | 352 | 0.0340 | 0.0322 | 0.0305 | `[0.0305, 0.0305, 0.0322, 0.0354, 0.0415]` | valid UNSAT (format checked) |
| `medium/test_3.cnf` | UNSAT | yes | 172 | 774 | 0.4964 | 0.4950 | 0.4722 | `[0.4907, 0.5142, 0.4722, 0.4950, 0.5101]` | valid UNSAT (format checked) |
| `medium/test_4.cnf` | UNSAT | yes | 191 | 886 | 0.8800 | 0.8714 | 0.8585 | `[0.8585, 0.9213, 0.8818, 0.8671, 0.8714]` | valid UNSAT (format checked) |
| `medium/test_5.cnf` | UNSAT | yes | 55 | 713 | 0.0358 | 0.0385 | 0.0284 | `[0.0385, 0.0320, 0.0284, 0.0407, 0.0392]` | valid UNSAT (format checked) |
| `medium/test_6.cnf` | UNSAT | yes | 61 | 512 | 0.0391 | 0.0417 | 0.0288 | `[0.0417, 0.0430, 0.0368, 0.0452, 0.0288]` | valid UNSAT (format checked) |
| `medium/test_7.cnf` | UNSAT | yes | 75 | 562 | 0.0363 | 0.0318 | 0.0293 | `[0.0318, 0.0449, 0.0296, 0.0461, 0.0293]` | valid UNSAT (format checked) |
| `medium/test_8.cnf` | SAT | yes | 130 | 333 | 0.0345 | 0.0378 | 0.0274 | `[0.0398, 0.0277, 0.0378, 0.0398, 0.0274]` | valid SAT |
| `medium/test_9.cnf` | SAT | yes | 138 | 379 | 0.0346 | 0.0324 | 0.0271 | `[0.0324, 0.0408, 0.0414, 0.0313, 0.0271]` | valid SAT |
| `large/test_1.cnf` | SAT | yes | 373 | 811 | 0.0467 | 0.0484 | 0.0393 | `[0.0484, 0.0496, 0.0488, 0.0393, 0.0474]` | valid SAT |
| `large/test_10.cnf` | UNSAT | yes | 229 | 1280 | 0.8642 | 0.8374 | 0.8253 | `[0.8374, 0.9685, 0.8253, 0.8584, 0.8315]` | valid UNSAT (format checked) |
| `large/test_2.cnf` | SAT | yes | 319 | 573 | 0.0373 | 0.0329 | 0.0306 | `[0.0329, 0.0448, 0.0306, 0.0465, 0.0315]` | valid SAT |
| `large/test_3.cnf` | UNSAT | yes | 227 | 1460 | 0.2937 | 0.2891 | 0.2788 | `[0.3006, 0.2852, 0.3145, 0.2891, 0.2788]` | valid UNSAT (format checked) |
| `large/test_4.cnf` | UNSAT | yes | 219 | 1363 | 0.2498 | 0.2470 | 0.2299 | `[0.2299, 0.2416, 0.2715, 0.2589, 0.2470]` | valid UNSAT (format checked) |
| `large/test_5.cnf` | SAT | yes | 244 | 772 | 0.0317 | 0.0309 | 0.0296 | `[0.0309, 0.0314, 0.0302, 0.0296, 0.0364]` | valid SAT |
| `large/test_6.cnf` | UNSAT | yes | 271 | 1393 | 3.5338 | 3.4841 | 3.3731 | `[3.3731, 3.4841, 3.4745, 3.7079, 3.6295]` | valid UNSAT (format checked) |
| `large/test_7.cnf` | SAT | yes | 389 | 863 | 0.0390 | 0.0360 | 0.0332 | `[0.0360, 0.0417, 0.0353, 0.0488, 0.0332]` | valid SAT |
| `large/test_8.cnf` | SAT | yes | 298 | 1210 | 0.1265 | 0.1293 | 0.1115 | `[0.1263, 0.1358, 0.1115, 0.1293, 0.1294]` | valid SAT |
| `large/test_9.cnf` | SAT | yes | 365 | 969 | 0.0382 | 0.0362 | 0.0332 | `[0.0362, 0.0362, 0.0453, 0.0400, 0.0332]` | valid SAT |
| `special/dense.cnf` | UNSAT | yes | 200 | 1500 | 0.1214 | 0.1199 | 0.1161 | `[0.1304, 0.1213, 0.1191, 0.1199, 0.1161]` | valid UNSAT (format checked) |
| `special/easy.cnf` | SAT | yes | 200 | 400 | 0.0291 | 0.0291 | 0.0272 | `[0.0312, 0.0279, 0.0272, 0.0302, 0.0291]` | valid SAT |
| `special/hard.cnf` | UNSAT | yes | 200 | 850 | 2.5972 | 2.6231 | 2.4641 | `[2.4641, 2.6231, 2.6529, 2.6614, 2.5846]` | valid UNSAT (format checked) |
| `special/pigeonhole.cnf` | UNSAT | yes | 90 | 415 | 0.0283 | 0.0242 | 0.0230 | `[0.0356, 0.0230, 0.0232, 0.0242, 0.0354]` | valid UNSAT (format checked) |
| `special/tseitin.cnf` | UNSAT | yes | 40 | 160 | 0.0295 | 0.0256 | 0.0214 | `[0.0233, 0.0351, 0.0420, 0.0256, 0.0214]` | valid UNSAT (format checked) |
