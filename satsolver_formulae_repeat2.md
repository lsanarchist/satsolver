# satsolver.py formulae repeat2

Generated: 2026-05-31T17:36:43
Solver command: `python satsolver.py <input.cnf> <output.txt>`
Dataset: `formulae`
Repeats per case: `2`
Per-run timeout: `60s`
Validation: `tools/checker.py`.

## Summary

- Cases tested: `35`
- Correct/valid: `35/35`
- Timeout cases: `0`
- SAT cases: `16`
- UNSAT cases: `19`
- Avg-total: `11.5190s`
- Median-total: `11.5190s`
- Wall time: `26.7936s`

## By Category

| category | cases | avg-total s |
|---|---:|---:|
| `small` | 10 | 0.3404 |
| `medium` | 10 | 1.7998 |
| `large` | 10 | 6.6300 |
| `special` | 5 | 2.7488 |

## Slowest Cases By Avg

| case | result | avg s | median s | min s | max s | runs s | status |
|---|---|---:|---:|---:|---:|---|---|
| `large/test_6.cnf` | UNSAT | 3.3864 | 3.3864 | 3.3197 | 3.4531 | `[3.4531, 3.3197]` | OK,OK |
| `special/hard.cnf` | UNSAT | 2.5204 | 2.5204 | 2.4505 | 2.5904 | `[2.5904, 2.4505]` | OK,OK |
| `large/test_8.cnf` | SAT | 1.6651 | 1.6651 | 1.5937 | 1.7366 | `[1.5937, 1.7366]` | OK,OK |
| `medium/test_4.cnf` | UNSAT | 0.9794 | 0.9794 | 0.9734 | 0.9854 | `[0.9734, 0.9854]` | OK,OK |
| `large/test_10.cnf` | UNSAT | 0.8602 | 0.8602 | 0.8565 | 0.8640 | `[0.8565, 0.8640]` | OK,OK |
| `medium/test_3.cnf` | UNSAT | 0.5169 | 0.5169 | 0.5047 | 0.5291 | `[0.5291, 0.5047]` | OK,OK |
| `large/test_3.cnf` | UNSAT | 0.2847 | 0.2847 | 0.2846 | 0.2848 | `[0.2848, 0.2846]` | OK,OK |
| `large/test_4.cnf` | UNSAT | 0.2374 | 0.2374 | 0.2344 | 0.2403 | `[0.2344, 0.2403]` | OK,OK |
| `special/dense.cnf` | UNSAT | 0.1297 | 0.1297 | 0.1238 | 0.1356 | `[0.1356, 0.1238]` | OK,OK |
| `medium/test_1.cnf` | UNSAT | 0.0467 | 0.0467 | 0.0461 | 0.0473 | `[0.0461, 0.0473]` | OK,OK |

## All Cases

| case | result | avg s | median s | min s | max s | runs s | status |
|---|---|---:|---:|---:|---:|---|---|
| `small/test_1.cnf` | SAT | 0.0380 | 0.0380 | 0.0323 | 0.0438 | `[0.0323, 0.0438]` | OK,OK |
| `small/test_2.cnf` | SAT | 0.0258 | 0.0258 | 0.0251 | 0.0266 | `[0.0251, 0.0266]` | OK,OK |
| `small/test_3.cnf` | SAT | 0.0289 | 0.0289 | 0.0263 | 0.0316 | `[0.0263, 0.0316]` | OK,OK |
| `small/test_4.cnf` | UNSAT | 0.0376 | 0.0376 | 0.0283 | 0.0469 | `[0.0283, 0.0469]` | OK,OK |
| `small/test_5.cnf` | SAT | 0.0303 | 0.0303 | 0.0235 | 0.0370 | `[0.0235, 0.0370]` | OK,OK |
| `small/test_6.cnf` | SAT | 0.0359 | 0.0359 | 0.0240 | 0.0477 | `[0.0240, 0.0477]` | OK,OK |
| `small/test_7.cnf` | SAT | 0.0328 | 0.0328 | 0.0289 | 0.0367 | `[0.0289, 0.0367]` | OK,OK |
| `small/test_8.cnf` | UNSAT | 0.0301 | 0.0301 | 0.0230 | 0.0371 | `[0.0230, 0.0371]` | OK,OK |
| `small/test_9.cnf` | SAT | 0.0347 | 0.0347 | 0.0286 | 0.0407 | `[0.0286, 0.0407]` | OK,OK |
| `small/test_10.cnf` | UNSAT | 0.0463 | 0.0463 | 0.0388 | 0.0539 | `[0.0388, 0.0539]` | OK,OK |
| `medium/test_1.cnf` | UNSAT | 0.0467 | 0.0467 | 0.0461 | 0.0473 | `[0.0461, 0.0473]` | OK,OK |
| `medium/test_2.cnf` | UNSAT | 0.0415 | 0.0415 | 0.0377 | 0.0454 | `[0.0377, 0.0454]` | OK,OK |
| `medium/test_3.cnf` | UNSAT | 0.5169 | 0.5169 | 0.5047 | 0.5291 | `[0.5291, 0.5047]` | OK,OK |
| `medium/test_4.cnf` | UNSAT | 0.9794 | 0.9794 | 0.9734 | 0.9854 | `[0.9734, 0.9854]` | OK,OK |
| `medium/test_5.cnf` | UNSAT | 0.0319 | 0.0319 | 0.0292 | 0.0346 | `[0.0292, 0.0346]` | OK,OK |
| `medium/test_6.cnf` | UNSAT | 0.0378 | 0.0378 | 0.0316 | 0.0440 | `[0.0316, 0.0440]` | OK,OK |
| `medium/test_7.cnf` | UNSAT | 0.0289 | 0.0289 | 0.0270 | 0.0308 | `[0.0308, 0.0270]` | OK,OK |
| `medium/test_8.cnf` | SAT | 0.0381 | 0.0381 | 0.0355 | 0.0407 | `[0.0355, 0.0407]` | OK,OK |
| `medium/test_9.cnf` | SAT | 0.0376 | 0.0376 | 0.0374 | 0.0378 | `[0.0374, 0.0378]` | OK,OK |
| `medium/test_10.cnf` | UNSAT | 0.0409 | 0.0409 | 0.0329 | 0.0490 | `[0.0329, 0.0490]` | OK,OK |
| `large/test_1.cnf` | SAT | 0.0385 | 0.0385 | 0.0380 | 0.0390 | `[0.0390, 0.0380]` | OK,OK |
| `large/test_2.cnf` | SAT | 0.0326 | 0.0326 | 0.0319 | 0.0334 | `[0.0319, 0.0334]` | OK,OK |
| `large/test_3.cnf` | UNSAT | 0.2847 | 0.2847 | 0.2846 | 0.2848 | `[0.2848, 0.2846]` | OK,OK |
| `large/test_4.cnf` | UNSAT | 0.2374 | 0.2374 | 0.2344 | 0.2403 | `[0.2344, 0.2403]` | OK,OK |
| `large/test_5.cnf` | SAT | 0.0435 | 0.0435 | 0.0395 | 0.0475 | `[0.0395, 0.0475]` | OK,OK |
| `large/test_6.cnf` | UNSAT | 3.3864 | 3.3864 | 3.3197 | 3.4531 | `[3.4531, 3.3197]` | OK,OK |
| `large/test_7.cnf` | SAT | 0.0417 | 0.0417 | 0.0323 | 0.0511 | `[0.0323, 0.0511]` | OK,OK |
| `large/test_8.cnf` | SAT | 1.6651 | 1.6651 | 1.5937 | 1.7366 | `[1.5937, 1.7366]` | OK,OK |
| `large/test_9.cnf` | SAT | 0.0398 | 0.0398 | 0.0337 | 0.0459 | `[0.0337, 0.0459]` | OK,OK |
| `large/test_10.cnf` | UNSAT | 0.8602 | 0.8602 | 0.8565 | 0.8640 | `[0.8565, 0.8640]` | OK,OK |
| `special/dense.cnf` | UNSAT | 0.1297 | 0.1297 | 0.1238 | 0.1356 | `[0.1356, 0.1238]` | OK,OK |
| `special/easy.cnf` | SAT | 0.0362 | 0.0362 | 0.0357 | 0.0368 | `[0.0368, 0.0357]` | OK,OK |
| `special/hard.cnf` | UNSAT | 2.5204 | 2.5204 | 2.4505 | 2.5904 | `[2.5904, 2.4505]` | OK,OK |
| `special/pigeonhole.cnf` | UNSAT | 0.0386 | 0.0386 | 0.0324 | 0.0448 | `[0.0448, 0.0324]` | OK,OK |
| `special/tseitin.cnf` | UNSAT | 0.0239 | 0.0239 | 0.0232 | 0.0245 | `[0.0245, 0.0232]` | OK,OK |
