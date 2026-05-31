# SAT Solver Formulae Benchmark

Generated: 2026-05-31T20:46:10
Dataset: `formulae (small, medium, large, special)`
Source benchmark output: `/tmp/phase_formulae_candidate_final.txt`
Solver: `satsolver`
Mode: `cli`
CLI script: `/home/doomguy/Desktop/sat/satsolver/satsolver.py`
Python executable: `/usr/bin/python`
Repeats: `2`
Bruteforce var limit: `16`

## Overall

| cases | solved | errors | SAT | UNSAT | total s | avg s | median s | max s | measured total s | wall clock s |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 35 | 35 | 0 | 16 | 19 | 10.0431 | 0.2869 | 0.0347 | 3.4779 | 20.0862 | 20.2474 |

## Folder Summary

| folder | cases | solved | errors | SAT | UNSAT | total s | avg s | median s | max s | measured total s |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| `small` | 10 | 10 | 0 | 7 | 3 | 0.3000 | 0.0300 | 0.0309 | 0.0340 | 0.6000 |
| `medium` | 10 | 10 | 0 | 2 | 8 | 1.6412 | 0.1641 | 0.0367 | 0.8632 | 3.2824 |
| `large` | 10 | 10 | 0 | 6 | 4 | 5.2460 | 0.5246 | 0.0922 | 3.4779 | 10.4920 |
| `special` | 5 | 5 | 0 | 1 | 4 | 2.8559 | 0.5712 | 0.0338 | 2.6314 | 5.7118 |

## Slowest Cases

| case | result | vars | clauses | time s | best s | median s | samples | validation |
|---|---|---:|---:|---:|---:|---:|---|---|
| `large/test_6.cnf` | UNSAT | 271 | 1393 | 3.4779 | 3.4690 | 3.4779 | `[3.4690, 3.4869]` | valid UNSAT (format checked) |
| `special/hard.cnf` | UNSAT | 200 | 850 | 2.6314 | 2.5451 | 2.6314 | `[2.7178, 2.5451]` | valid UNSAT (format checked) |
| `large/test_10.cnf` | UNSAT | 229 | 1280 | 0.8680 | 0.8560 | 0.8680 | `[0.8560, 0.8800]` | valid UNSAT (format checked) |
| `medium/test_4.cnf` | UNSAT | 191 | 886 | 0.8632 | 0.8411 | 0.8632 | `[0.8411, 0.8853]` | valid UNSAT (format checked) |
| `medium/test_3.cnf` | UNSAT | 172 | 774 | 0.4981 | 0.4737 | 0.4981 | `[0.5225, 0.4737]` | valid UNSAT (format checked) |
| `large/test_3.cnf` | UNSAT | 227 | 1460 | 0.3142 | 0.3072 | 0.3142 | `[0.3072, 0.3213]` | valid UNSAT (format checked) |
| `large/test_4.cnf` | UNSAT | 219 | 1363 | 0.2305 | 0.2195 | 0.2305 | `[0.2415, 0.2195]` | valid UNSAT (format checked) |
| `large/test_8.cnf` | SAT | 298 | 1210 | 0.1340 | 0.1192 | 0.1340 | `[0.1192, 0.1488]` | valid SAT |
| `special/dense.cnf` | UNSAT | 200 | 1500 | 0.1284 | 0.1190 | 0.1284 | `[0.1378, 0.1190]` | valid UNSAT (format checked) |
| `large/test_5.cnf` | SAT | 244 | 772 | 0.0504 | 0.0432 | 0.0504 | `[0.0575, 0.0432]` | valid SAT |
| `large/test_2.cnf` | SAT | 319 | 573 | 0.0469 | 0.0345 | 0.0469 | `[0.0345, 0.0593]` | valid SAT |
| `medium/test_6.cnf` | UNSAT | 61 | 512 | 0.0465 | 0.0458 | 0.0465 | `[0.0458, 0.0473]` | valid UNSAT (format checked) |
| `large/test_7.cnf` | SAT | 389 | 863 | 0.0442 | 0.0353 | 0.0442 | `[0.0353, 0.0531]` | valid SAT |
| `medium/test_2.cnf` | UNSAT | 69 | 352 | 0.0432 | 0.0431 | 0.0432 | `[0.0431, 0.0433]` | valid UNSAT (format checked) |
| `large/test_9.cnf` | SAT | 365 | 969 | 0.0404 | 0.0351 | 0.0404 | `[0.0456, 0.0351]` | valid SAT |
| `large/test_1.cnf` | SAT | 373 | 811 | 0.0394 | 0.0320 | 0.0394 | `[0.0320, 0.0468]` | valid SAT |
| `medium/test_9.cnf` | SAT | 138 | 379 | 0.0388 | 0.0281 | 0.0388 | `[0.0494, 0.0281]` | valid SAT |
| `medium/test_1.cnf` | UNSAT | 63 | 835 | 0.0347 | 0.0311 | 0.0347 | `[0.0311, 0.0383]` | valid UNSAT (format checked) |
| `small/test_4.cnf` | UNSAT | 30 | 167 | 0.0340 | 0.0258 | 0.0340 | `[0.0258, 0.0422]` | valid UNSAT (format checked) |
| `special/easy.cnf` | SAT | 200 | 400 | 0.0338 | 0.0299 | 0.0338 | `[0.0299, 0.0378]` | valid SAT |

## All Cases

| case | result | ok | vars | clauses | time s | best s | median s | samples | validation |
|---|---|---:|---:|---:|---:|---:|---:|---|---|
| `small/test_1.cnf` | SAT | yes | 19 | 26 | 0.0231 | 0.0220 | 0.0231 | `[0.0242, 0.0220]` | valid SAT |
| `small/test_10.cnf` | UNSAT | yes | 22 | 174 | 0.0302 | 0.0252 | 0.0302 | `[0.0252, 0.0351]` | valid UNSAT (format checked) |
| `small/test_2.cnf` | SAT | yes | 46 | 176 | 0.0309 | 0.0281 | 0.0309 | `[0.0281, 0.0336]` | valid SAT |
| `small/test_3.cnf` | SAT | yes | 41 | 150 | 0.0280 | 0.0253 | 0.0280 | `[0.0307, 0.0253]` | valid SAT |
| `small/test_4.cnf` | UNSAT | yes | 30 | 167 | 0.0340 | 0.0258 | 0.0340 | `[0.0258, 0.0422]` | valid UNSAT (format checked) |
| `small/test_5.cnf` | SAT | yes | 20 | 40 | 0.0318 | 0.0260 | 0.0318 | `[0.0260, 0.0377]` | valid SAT |
| `small/test_6.cnf` | SAT | yes | 42 | 70 | 0.0310 | 0.0226 | 0.0310 | `[0.0226, 0.0394]` | valid SAT |
| `small/test_7.cnf` | SAT | yes | 49 | 167 | 0.0320 | 0.0278 | 0.0320 | `[0.0278, 0.0362]` | valid SAT |
| `small/test_8.cnf` | UNSAT | yes | 14 | 68 | 0.0266 | 0.0249 | 0.0266 | `[0.0282, 0.0249]` | valid UNSAT (brute-force checked) |
| `small/test_9.cnf` | SAT | yes | 40 | 100 | 0.0325 | 0.0225 | 0.0325 | `[0.0426, 0.0225]` | valid SAT |
| `medium/test_1.cnf` | UNSAT | yes | 63 | 835 | 0.0347 | 0.0311 | 0.0347 | `[0.0311, 0.0383]` | valid UNSAT (format checked) |
| `medium/test_10.cnf` | UNSAT | yes | 68 | 822 | 0.0299 | 0.0295 | 0.0299 | `[0.0295, 0.0303]` | valid UNSAT (format checked) |
| `medium/test_2.cnf` | UNSAT | yes | 69 | 352 | 0.0432 | 0.0431 | 0.0432 | `[0.0431, 0.0433]` | valid UNSAT (format checked) |
| `medium/test_3.cnf` | UNSAT | yes | 172 | 774 | 0.4981 | 0.4737 | 0.4981 | `[0.5225, 0.4737]` | valid UNSAT (format checked) |
| `medium/test_4.cnf` | UNSAT | yes | 191 | 886 | 0.8632 | 0.8411 | 0.8632 | `[0.8411, 0.8853]` | valid UNSAT (format checked) |
| `medium/test_5.cnf` | UNSAT | yes | 55 | 713 | 0.0249 | 0.0245 | 0.0249 | `[0.0253, 0.0245]` | valid UNSAT (format checked) |
| `medium/test_6.cnf` | UNSAT | yes | 61 | 512 | 0.0465 | 0.0458 | 0.0465 | `[0.0458, 0.0473]` | valid UNSAT (format checked) |
| `medium/test_7.cnf` | UNSAT | yes | 75 | 562 | 0.0288 | 0.0286 | 0.0288 | `[0.0286, 0.0291]` | valid UNSAT (format checked) |
| `medium/test_8.cnf` | SAT | yes | 130 | 333 | 0.0331 | 0.0289 | 0.0331 | `[0.0289, 0.0372]` | valid SAT |
| `medium/test_9.cnf` | SAT | yes | 138 | 379 | 0.0388 | 0.0281 | 0.0388 | `[0.0494, 0.0281]` | valid SAT |
| `large/test_1.cnf` | SAT | yes | 373 | 811 | 0.0394 | 0.0320 | 0.0394 | `[0.0320, 0.0468]` | valid SAT |
| `large/test_10.cnf` | UNSAT | yes | 229 | 1280 | 0.8680 | 0.8560 | 0.8680 | `[0.8560, 0.8800]` | valid UNSAT (format checked) |
| `large/test_2.cnf` | SAT | yes | 319 | 573 | 0.0469 | 0.0345 | 0.0469 | `[0.0345, 0.0593]` | valid SAT |
| `large/test_3.cnf` | UNSAT | yes | 227 | 1460 | 0.3142 | 0.3072 | 0.3142 | `[0.3072, 0.3213]` | valid UNSAT (format checked) |
| `large/test_4.cnf` | UNSAT | yes | 219 | 1363 | 0.2305 | 0.2195 | 0.2305 | `[0.2415, 0.2195]` | valid UNSAT (format checked) |
| `large/test_5.cnf` | SAT | yes | 244 | 772 | 0.0504 | 0.0432 | 0.0504 | `[0.0575, 0.0432]` | valid SAT |
| `large/test_6.cnf` | UNSAT | yes | 271 | 1393 | 3.4779 | 3.4690 | 3.4779 | `[3.4690, 3.4869]` | valid UNSAT (format checked) |
| `large/test_7.cnf` | SAT | yes | 389 | 863 | 0.0442 | 0.0353 | 0.0442 | `[0.0353, 0.0531]` | valid SAT |
| `large/test_8.cnf` | SAT | yes | 298 | 1210 | 0.1340 | 0.1192 | 0.1340 | `[0.1192, 0.1488]` | valid SAT |
| `large/test_9.cnf` | SAT | yes | 365 | 969 | 0.0404 | 0.0351 | 0.0404 | `[0.0456, 0.0351]` | valid SAT |
| `special/dense.cnf` | UNSAT | yes | 200 | 1500 | 0.1284 | 0.1190 | 0.1284 | `[0.1378, 0.1190]` | valid UNSAT (format checked) |
| `special/easy.cnf` | SAT | yes | 200 | 400 | 0.0338 | 0.0299 | 0.0338 | `[0.0299, 0.0378]` | valid SAT |
| `special/hard.cnf` | UNSAT | yes | 200 | 850 | 2.6314 | 2.5451 | 2.6314 | `[2.7178, 2.5451]` | valid UNSAT (format checked) |
| `special/pigeonhole.cnf` | UNSAT | yes | 90 | 415 | 0.0288 | 0.0228 | 0.0288 | `[0.0228, 0.0349]` | valid UNSAT (format checked) |
| `special/tseitin.cnf` | UNSAT | yes | 40 | 160 | 0.0334 | 0.0306 | 0.0334 | `[0.0362, 0.0306]` | valid UNSAT (format checked) |
