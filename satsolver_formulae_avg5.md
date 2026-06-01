# SAT Solver Formulae Avg5 Benchmark

Generated: 2026-05-31T22:49:39
Dataset: `formulae baseline from git HEAD before the Mycielski detector`
Source benchmark output: `/tmp/satsolver_formulae_old_head_avg5.txt`
Solver: `satsolver`
Mode: `cli`
CLI script: `/tmp/satsolver_old_formulae_baseline.K9rGcy/satsolver.py`
Python executable: `/usr/bin/python`
Repeats: `5`
Bruteforce var limit: `16`
Metric note: `avg5 total` is `measured total / 5`, i.e. the mean runtime over five CLI runs per case. `median total` is the benchmark harness representative median sum.
Note: Restored old-baseline slot by rerunning the pre-detector solver from git HEAD, because the original formulae raw output had been overwritten.

## Overall

| cases | solved | errors | SAT | UNSAT | avg5 total s | median total s | avg/case s | median/case s | max median-case s | measured total s | wall clock s |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 35 | 35 | 0 | 16 | 19 | 11.1095 | 11.1369 | 0.3174 | 0.0365 | 3.9378 | 55.5474 | 55.9444 |

## Folder Summary

| folder | cases | solved | errors | SAT | UNSAT | avg5 total s | median total s | avg/case s | median/case s | max median-case s | measured total s |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| `small` | 10 | 10 | 0 | 7 | 3 | 0.3456 | 0.3349 | 0.0346 | 0.0331 | 0.0365 | 1.7279 |
| `medium` | 10 | 10 | 0 | 2 | 8 | 1.9071 | 1.9101 | 0.1907 | 0.0372 | 1.0350 | 9.5353 |
| `large` | 10 | 10 | 0 | 6 | 4 | 5.8950 | 5.9301 | 0.5895 | 0.0939 | 3.9378 | 29.4751 |
| `special` | 5 | 5 | 0 | 1 | 4 | 2.9618 | 2.9618 | 0.5924 | 0.0309 | 2.7370 | 14.8091 |

## Slowest Cases By Avg5

| case | result | vars | clauses | avg5 s | median s | best s | samples | validation |
|---|---|---:|---:|---:|---:|---:|---|---|
| `large/test_6.cnf` | UNSAT | 271 | 1393 | 3.8848 | 3.9378 | 3.6987 | `[3.9378, 3.7975, 3.6987, 3.9979, 3.9920]` | valid UNSAT (format checked) |
| `special/hard.cnf` | UNSAT | 200 | 850 | 2.7312 | 2.7370 | 2.6696 | `[2.7413, 2.7370, 2.7292, 2.6696, 2.7788]` | valid UNSAT (format checked) |
| `large/test_10.cnf` | UNSAT | 229 | 1280 | 1.0196 | 1.0076 | 0.9764 | `[1.0076, 1.0428, 0.9764, 1.0784, 0.9929]` | valid UNSAT (format checked) |
| `medium/test_4.cnf` | UNSAT | 191 | 886 | 1.0160 | 1.0350 | 0.9693 | `[0.9693, 1.0350, 0.9864, 1.0454, 1.0439]` | valid UNSAT (format checked) |
| `medium/test_3.cnf` | UNSAT | 172 | 774 | 0.5769 | 0.5759 | 0.5685 | `[0.5798, 0.5851, 0.5753, 0.5685, 0.5759]` | valid UNSAT (format checked) |
| `large/test_3.cnf` | UNSAT | 227 | 1460 | 0.3427 | 0.3434 | 0.3269 | `[0.3631, 0.3514, 0.3287, 0.3434, 0.3269]` | valid UNSAT (format checked) |
| `large/test_4.cnf` | UNSAT | 219 | 1363 | 0.2848 | 0.2852 | 0.2639 | `[0.2801, 0.2973, 0.2852, 0.2639, 0.2977]` | valid UNSAT (format checked) |
| `large/test_8.cnf` | SAT | 298 | 1210 | 0.1402 | 0.1376 | 0.1262 | `[0.1384, 0.1262, 0.1376, 0.1618, 0.1370]` | valid SAT |
| `special/dense.cnf` | UNSAT | 200 | 1500 | 0.1362 | 0.1378 | 0.1215 | `[0.1378, 0.1215, 0.1483, 0.1411, 0.1322]` | valid UNSAT (format checked) |
| `large/test_7.cnf` | SAT | 389 | 863 | 0.0471 | 0.0501 | 0.0337 | `[0.0501, 0.0337, 0.0607, 0.0367, 0.0542]` | valid SAT |
| `medium/test_2.cnf` | UNSAT | 69 | 352 | 0.0465 | 0.0460 | 0.0416 | `[0.0513, 0.0452, 0.0460, 0.0416, 0.0483]` | valid UNSAT (format checked) |
| `large/test_5.cnf` | SAT | 244 | 772 | 0.0451 | 0.0424 | 0.0413 | `[0.0417, 0.0527, 0.0413, 0.0472, 0.0424]` | valid SAT |
| `large/test_2.cnf` | SAT | 319 | 573 | 0.0449 | 0.0425 | 0.0383 | `[0.0503, 0.0399, 0.0425, 0.0383, 0.0537]` | valid SAT |
| `medium/test_10.cnf` | UNSAT | 68 | 822 | 0.0447 | 0.0420 | 0.0346 | `[0.0533, 0.0420, 0.0355, 0.0346, 0.0582]` | valid UNSAT (format checked) |
| `large/test_1.cnf` | SAT | 373 | 811 | 0.0438 | 0.0429 | 0.0404 | `[0.0442, 0.0429, 0.0413, 0.0404, 0.0501]` | valid SAT |
| `large/test_9.cnf` | SAT | 365 | 969 | 0.0420 | 0.0406 | 0.0341 | `[0.0406, 0.0341, 0.0371, 0.0548, 0.0435]` | valid SAT |
| `medium/test_1.cnf` | UNSAT | 63 | 835 | 0.0402 | 0.0386 | 0.0366 | `[0.0366, 0.0386, 0.0454, 0.0433, 0.0370]` | valid UNSAT (format checked) |
| `medium/test_6.cnf` | UNSAT | 61 | 512 | 0.0383 | 0.0343 | 0.0315 | `[0.0343, 0.0315, 0.0449, 0.0320, 0.0485]` | valid UNSAT (format checked) |
| `medium/test_9.cnf` | SAT | 138 | 379 | 0.0378 | 0.0338 | 0.0317 | `[0.0338, 0.0317, 0.0324, 0.0488, 0.0421]` | valid SAT |
| `medium/test_8.cnf` | SAT | 130 | 333 | 0.0369 | 0.0350 | 0.0310 | `[0.0316, 0.0350, 0.0436, 0.0310, 0.0435]` | valid SAT |

## All Cases

| case | result | ok | vars | clauses | avg5 s | median s | best s | samples | validation |
|---|---|---:|---:|---:|---:|---:|---:|---|---|
| `small/test_1.cnf` | SAT | yes | 19 | 26 | 0.0358 | 0.0330 | 0.0304 | `[0.0458, 0.0373, 0.0323, 0.0330, 0.0304]` | valid SAT |
| `small/test_10.cnf` | UNSAT | yes | 22 | 174 | 0.0368 | 0.0365 | 0.0328 | `[0.0328, 0.0358, 0.0377, 0.0365, 0.0413]` | valid UNSAT (format checked) |
| `small/test_2.cnf` | SAT | yes | 46 | 176 | 0.0330 | 0.0331 | 0.0320 | `[0.0330, 0.0339, 0.0331, 0.0333, 0.0320]` | valid SAT |
| `small/test_3.cnf` | SAT | yes | 41 | 150 | 0.0351 | 0.0342 | 0.0306 | `[0.0342, 0.0435, 0.0310, 0.0306, 0.0364]` | valid SAT |
| `small/test_4.cnf` | UNSAT | yes | 30 | 167 | 0.0347 | 0.0322 | 0.0282 | `[0.0347, 0.0322, 0.0321, 0.0282, 0.0461]` | valid UNSAT (format checked) |
| `small/test_5.cnf` | SAT | yes | 20 | 40 | 0.0368 | 0.0351 | 0.0292 | `[0.0443, 0.0292, 0.0331, 0.0351, 0.0423]` | valid SAT |
| `small/test_6.cnf` | SAT | yes | 42 | 70 | 0.0357 | 0.0345 | 0.0325 | `[0.0398, 0.0325, 0.0373, 0.0345, 0.0343]` | valid SAT |
| `small/test_7.cnf` | SAT | yes | 49 | 167 | 0.0320 | 0.0314 | 0.0300 | `[0.0348, 0.0312, 0.0314, 0.0328, 0.0300]` | valid SAT |
| `small/test_8.cnf` | UNSAT | yes | 14 | 68 | 0.0330 | 0.0323 | 0.0288 | `[0.0359, 0.0323, 0.0392, 0.0291, 0.0288]` | valid UNSAT (brute-force checked) |
| `small/test_9.cnf` | SAT | yes | 40 | 100 | 0.0326 | 0.0326 | 0.0295 | `[0.0326, 0.0333, 0.0350, 0.0326, 0.0295]` | valid SAT |
| `medium/test_1.cnf` | UNSAT | yes | 63 | 835 | 0.0402 | 0.0386 | 0.0366 | `[0.0366, 0.0386, 0.0454, 0.0433, 0.0370]` | valid UNSAT (format checked) |
| `medium/test_10.cnf` | UNSAT | yes | 68 | 822 | 0.0447 | 0.0420 | 0.0346 | `[0.0533, 0.0420, 0.0355, 0.0346, 0.0582]` | valid UNSAT (format checked) |
| `medium/test_2.cnf` | UNSAT | yes | 69 | 352 | 0.0465 | 0.0460 | 0.0416 | `[0.0513, 0.0452, 0.0460, 0.0416, 0.0483]` | valid UNSAT (format checked) |
| `medium/test_3.cnf` | UNSAT | yes | 172 | 774 | 0.5769 | 0.5759 | 0.5685 | `[0.5798, 0.5851, 0.5753, 0.5685, 0.5759]` | valid UNSAT (format checked) |
| `medium/test_4.cnf` | UNSAT | yes | 191 | 886 | 1.0160 | 1.0350 | 0.9693 | `[0.9693, 1.0350, 0.9864, 1.0454, 1.0439]` | valid UNSAT (format checked) |
| `medium/test_5.cnf` | UNSAT | yes | 55 | 713 | 0.0335 | 0.0337 | 0.0315 | `[0.0346, 0.0315, 0.0337, 0.0331, 0.0344]` | valid UNSAT (format checked) |
| `medium/test_6.cnf` | UNSAT | yes | 61 | 512 | 0.0383 | 0.0343 | 0.0315 | `[0.0343, 0.0315, 0.0449, 0.0320, 0.0485]` | valid UNSAT (format checked) |
| `medium/test_7.cnf` | UNSAT | yes | 75 | 562 | 0.0363 | 0.0358 | 0.0311 | `[0.0322, 0.0311, 0.0413, 0.0358, 0.0410]` | valid UNSAT (format checked) |
| `medium/test_8.cnf` | SAT | yes | 130 | 333 | 0.0369 | 0.0350 | 0.0310 | `[0.0316, 0.0350, 0.0436, 0.0310, 0.0435]` | valid SAT |
| `medium/test_9.cnf` | SAT | yes | 138 | 379 | 0.0378 | 0.0338 | 0.0317 | `[0.0338, 0.0317, 0.0324, 0.0488, 0.0421]` | valid SAT |
| `large/test_1.cnf` | SAT | yes | 373 | 811 | 0.0438 | 0.0429 | 0.0404 | `[0.0442, 0.0429, 0.0413, 0.0404, 0.0501]` | valid SAT |
| `large/test_10.cnf` | UNSAT | yes | 229 | 1280 | 1.0196 | 1.0076 | 0.9764 | `[1.0076, 1.0428, 0.9764, 1.0784, 0.9929]` | valid UNSAT (format checked) |
| `large/test_2.cnf` | SAT | yes | 319 | 573 | 0.0449 | 0.0425 | 0.0383 | `[0.0503, 0.0399, 0.0425, 0.0383, 0.0537]` | valid SAT |
| `large/test_3.cnf` | UNSAT | yes | 227 | 1460 | 0.3427 | 0.3434 | 0.3269 | `[0.3631, 0.3514, 0.3287, 0.3434, 0.3269]` | valid UNSAT (format checked) |
| `large/test_4.cnf` | UNSAT | yes | 219 | 1363 | 0.2848 | 0.2852 | 0.2639 | `[0.2801, 0.2973, 0.2852, 0.2639, 0.2977]` | valid UNSAT (format checked) |
| `large/test_5.cnf` | SAT | yes | 244 | 772 | 0.0451 | 0.0424 | 0.0413 | `[0.0417, 0.0527, 0.0413, 0.0472, 0.0424]` | valid SAT |
| `large/test_6.cnf` | UNSAT | yes | 271 | 1393 | 3.8848 | 3.9378 | 3.6987 | `[3.9378, 3.7975, 3.6987, 3.9979, 3.9920]` | valid UNSAT (format checked) |
| `large/test_7.cnf` | SAT | yes | 389 | 863 | 0.0471 | 0.0501 | 0.0337 | `[0.0501, 0.0337, 0.0607, 0.0367, 0.0542]` | valid SAT |
| `large/test_8.cnf` | SAT | yes | 298 | 1210 | 0.1402 | 0.1376 | 0.1262 | `[0.1384, 0.1262, 0.1376, 0.1618, 0.1370]` | valid SAT |
| `large/test_9.cnf` | SAT | yes | 365 | 969 | 0.0420 | 0.0406 | 0.0341 | `[0.0406, 0.0341, 0.0371, 0.0548, 0.0435]` | valid SAT |
| `special/dense.cnf` | UNSAT | yes | 200 | 1500 | 0.1362 | 0.1378 | 0.1215 | `[0.1378, 0.1215, 0.1483, 0.1411, 0.1322]` | valid UNSAT (format checked) |
| `special/easy.cnf` | SAT | yes | 200 | 400 | 0.0349 | 0.0309 | 0.0290 | `[0.0290, 0.0300, 0.0309, 0.0429, 0.0419]` | valid SAT |
| `special/hard.cnf` | UNSAT | yes | 200 | 850 | 2.7312 | 2.7370 | 2.6696 | `[2.7413, 2.7370, 2.7292, 2.6696, 2.7788]` | valid UNSAT (format checked) |
| `special/pigeonhole.cnf` | UNSAT | yes | 90 | 415 | 0.0290 | 0.0269 | 0.0228 | `[0.0360, 0.0228, 0.0269, 0.0343, 0.0247]` | valid UNSAT (format checked) |
| `special/tseitin.cnf` | UNSAT | yes | 40 | 160 | 0.0306 | 0.0293 | 0.0257 | `[0.0322, 0.0278, 0.0257, 0.0293, 0.0379]` | valid UNSAT (format checked) |
