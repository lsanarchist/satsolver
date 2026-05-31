# SAT Solver Variants Formulae Benchmark

Generated: 2026-05-31T18:53:57
Dataset: `formulae`
Cases: `35`
Repeats per solver per case: `2`
Per-run timeout: `60s`
Validation: `tools/checker.py`.

Compared CLI solvers:
- `satsolver`: `python satsolver.py <input.cnf> <output.txt>` (standard-library submission CLI)
- `satsolver_fast`: `python satsolver_fast.py <input.cnf> <output.txt>` (standard-library alternate wrapper)
- `satsolver_blaze`: `python satsolver_blaze.py <input.cnf> <output.txt>` (legacy standard-library comparison)
- `satsolver_pysat`: `.venv-external-sat/bin/python satsolver_pysat.py <input.cnf> <output.txt>` (external PySAT reference, not allowed for submission)

Note: PySAT external env version: `1.9.dev2`. `satsolver_pysat.py` uses an external SAT library and is included only as a reference; it is forbidden for the course submission path.

## Summary

- Cases tested per solver: `35`
- Best avg-total solver: `satsolver_pysat`
- Benchmark wall time: `140.4394s`

| solver | valid | timeouts | SAT | UNSAT | avg-total s | median-case s | delta vs satsolver s | best-case count | max case s |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| `satsolver` | 35/35 | 0 | 16 | 19 | 11.6509 | 0.0358 | +0.0000 | 9 | 3.5244 |
| `satsolver_fast` | 35/35 | 0 | 16 | 19 | 11.6925 | 0.0366 | +0.0416 | 17 | 3.5256 |
| `satsolver_blaze` | 35/35 | 0 | 16 | 19 | 39.8946 | 0.0705 | +28.2437 | 0 | 15.9033 |
| `satsolver_pysat` | 35/35 | 0 | 16 | 19 | 6.6776 | 0.0625 | -4.9733 | 9 | 2.8382 |

## Most Sensitive Cases

| case | satsolver avg s | satsolver_fast avg s | satsolver_blaze avg s | satsolver_pysat avg s | spread s | best solver |
|---|---:|---:|---:|---:|---:|---|
| `large/test_6.cnf` | 3.5244 | 3.5256 | 15.9033 | 0.3841 | 15.5192 | `satsolver_pysat` |
| `special/hard.cnf` | 2.6295 | 2.6193 | 11.0030 | 0.2908 | 10.7122 | `satsolver_pysat` |
| `large/test_8.cnf` | 1.7304 | 1.7927 | 4.7999 | 0.3674 | 4.4325 | `satsolver_pysat` |
| `special/pigeonhole.cnf` | 0.0322 | 0.0290 | 0.0547 | 2.8382 | 2.8092 | `satsolver_fast` |
| `medium/test_4.cnf` | 0.8626 | 0.8494 | 2.3128 | 0.1115 | 2.2012 | `satsolver_pysat` |
| `large/test_10.cnf` | 0.8615 | 0.8734 | 2.2164 | 0.0960 | 2.1204 | `satsolver_pysat` |
| `medium/test_3.cnf` | 0.5006 | 0.4894 | 0.9838 | 0.0940 | 0.8898 | `satsolver_pysat` |
| `special/tseitin.cnf` | 0.0316 | 0.0274 | 0.0625 | 0.8694 | 0.8421 | `satsolver_fast` |
| `large/test_3.cnf` | 0.2854 | 0.2876 | 0.4306 | 0.0770 | 0.3536 | `satsolver_pysat` |
| `large/test_4.cnf` | 0.2262 | 0.2426 | 0.3573 | 0.0638 | 0.2935 | `satsolver_pysat` |
| `special/dense.cnf` | 0.1335 | 0.1307 | 0.1806 | 0.0692 | 0.1113 | `satsolver_pysat` |
| `special/easy.cnf` | 0.0297 | 0.0414 | 0.0662 | 0.0895 | 0.0599 | `satsolver` |
| `small/test_4.cnf` | 0.0286 | 0.0266 | 0.0777 | 0.0551 | 0.0511 | `satsolver_fast` |
| `small/test_2.cnf` | 0.0245 | 0.0387 | 0.0715 | 0.0556 | 0.0470 | `satsolver` |
| `small/test_5.cnf` | 0.0395 | 0.0309 | 0.0734 | 0.0538 | 0.0424 | `satsolver_fast` |

## Slowest Cases Per Solver

### satsolver

| case | result | avg s | median s | min s | max s | runs s | status |
|---|---|---:|---:|---:|---:|---|---|
| `large/test_6.cnf` | UNSAT | 3.5244 | 3.5244 | 3.4992 | 3.5496 | `[3.5496, 3.4992]` | OK,OK |
| `special/hard.cnf` | UNSAT | 2.6295 | 2.6295 | 2.5769 | 2.6821 | `[2.5769, 2.6821]` | OK,OK |
| `large/test_8.cnf` | SAT | 1.7304 | 1.7304 | 1.7273 | 1.7336 | `[1.7336, 1.7273]` | OK,OK |
| `medium/test_4.cnf` | UNSAT | 0.8626 | 0.8626 | 0.8220 | 0.9032 | `[0.8220, 0.9032]` | OK,OK |
| `large/test_10.cnf` | UNSAT | 0.8615 | 0.8615 | 0.8363 | 0.8867 | `[0.8363, 0.8867]` | OK,OK |
| `medium/test_3.cnf` | UNSAT | 0.5006 | 0.5006 | 0.4888 | 0.5123 | `[0.5123, 0.4888]` | OK,OK |
| `large/test_3.cnf` | UNSAT | 0.2854 | 0.2854 | 0.2733 | 0.2975 | `[0.2975, 0.2733]` | OK,OK |
| `large/test_4.cnf` | UNSAT | 0.2262 | 0.2262 | 0.2221 | 0.2303 | `[0.2221, 0.2303]` | OK,OK |
| `special/dense.cnf` | UNSAT | 0.1335 | 0.1335 | 0.1273 | 0.1397 | `[0.1397, 0.1273]` | OK,OK |
| `large/test_1.cnf` | SAT | 0.0480 | 0.0480 | 0.0472 | 0.0488 | `[0.0488, 0.0472]` | OK,OK |

### satsolver_fast

| case | result | avg s | median s | min s | max s | runs s | status |
|---|---|---:|---:|---:|---:|---|---|
| `large/test_6.cnf` | UNSAT | 3.5256 | 3.5256 | 3.4625 | 3.5887 | `[3.4625, 3.5887]` | OK,OK |
| `special/hard.cnf` | UNSAT | 2.6193 | 2.6193 | 2.6058 | 2.6328 | `[2.6058, 2.6328]` | OK,OK |
| `large/test_8.cnf` | SAT | 1.7927 | 1.7927 | 1.7795 | 1.8060 | `[1.7795, 1.8060]` | OK,OK |
| `large/test_10.cnf` | UNSAT | 0.8734 | 0.8734 | 0.8644 | 0.8824 | `[0.8644, 0.8824]` | OK,OK |
| `medium/test_4.cnf` | UNSAT | 0.8494 | 0.8494 | 0.8474 | 0.8514 | `[0.8514, 0.8474]` | OK,OK |
| `medium/test_3.cnf` | UNSAT | 0.4894 | 0.4894 | 0.4620 | 0.5167 | `[0.5167, 0.4620]` | OK,OK |
| `large/test_3.cnf` | UNSAT | 0.2876 | 0.2876 | 0.2758 | 0.2993 | `[0.2758, 0.2993]` | OK,OK |
| `large/test_4.cnf` | UNSAT | 0.2426 | 0.2426 | 0.2362 | 0.2490 | `[0.2362, 0.2490]` | OK,OK |
| `special/dense.cnf` | UNSAT | 0.1307 | 0.1307 | 0.1225 | 0.1389 | `[0.1389, 0.1225]` | OK,OK |
| `large/test_7.cnf` | SAT | 0.0472 | 0.0472 | 0.0428 | 0.0516 | `[0.0516, 0.0428]` | OK,OK |

### satsolver_blaze

| case | result | avg s | median s | min s | max s | runs s | status |
|---|---|---:|---:|---:|---:|---|---|
| `large/test_6.cnf` | UNSAT | 15.9033 | 15.9033 | 15.8167 | 15.9900 | `[15.8167, 15.9900]` | OK,OK |
| `special/hard.cnf` | UNSAT | 11.0030 | 11.0030 | 10.7085 | 11.2976 | `[10.7085, 11.2976]` | OK,OK |
| `large/test_8.cnf` | SAT | 4.7999 | 4.7999 | 4.6900 | 4.9099 | `[4.9099, 4.6900]` | OK,OK |
| `medium/test_4.cnf` | UNSAT | 2.3128 | 2.3128 | 2.2472 | 2.3783 | `[2.3783, 2.2472]` | OK,OK |
| `large/test_10.cnf` | UNSAT | 2.2164 | 2.2164 | 2.1225 | 2.3104 | `[2.1225, 2.3104]` | OK,OK |
| `medium/test_3.cnf` | UNSAT | 0.9838 | 0.9838 | 0.9152 | 1.0523 | `[1.0523, 0.9152]` | OK,OK |
| `large/test_3.cnf` | UNSAT | 0.4306 | 0.4306 | 0.4264 | 0.4347 | `[0.4347, 0.4264]` | OK,OK |
| `large/test_4.cnf` | UNSAT | 0.3573 | 0.3573 | 0.3560 | 0.3586 | `[0.3560, 0.3586]` | OK,OK |
| `special/dense.cnf` | UNSAT | 0.1806 | 0.1806 | 0.1700 | 0.1911 | `[0.1911, 0.1700]` | OK,OK |
| `small/test_4.cnf` | UNSAT | 0.0777 | 0.0777 | 0.0613 | 0.0942 | `[0.0613, 0.0942]` | OK,OK |

### satsolver_pysat

| case | result | avg s | median s | min s | max s | runs s | status |
|---|---|---:|---:|---:|---:|---|---|
| `special/pigeonhole.cnf` | UNSAT | 2.8382 | 2.8382 | 2.8209 | 2.8556 | `[2.8556, 2.8209]` | OK,OK |
| `special/tseitin.cnf` | UNSAT | 0.8694 | 0.8694 | 0.8539 | 0.8849 | `[0.8539, 0.8849]` | OK,OK |
| `large/test_6.cnf` | UNSAT | 0.3841 | 0.3841 | 0.3836 | 0.3847 | `[0.3836, 0.3847]` | OK,OK |
| `large/test_8.cnf` | SAT | 0.3674 | 0.3674 | 0.3506 | 0.3842 | `[0.3842, 0.3506]` | OK,OK |
| `special/hard.cnf` | UNSAT | 0.2908 | 0.2908 | 0.2764 | 0.3052 | `[0.3052, 0.2764]` | OK,OK |
| `medium/test_4.cnf` | UNSAT | 0.1115 | 0.1115 | 0.1103 | 0.1128 | `[0.1128, 0.1103]` | OK,OK |
| `large/test_10.cnf` | UNSAT | 0.0960 | 0.0960 | 0.0912 | 0.1008 | `[0.1008, 0.0912]` | OK,OK |
| `medium/test_3.cnf` | UNSAT | 0.0940 | 0.0940 | 0.0906 | 0.0974 | `[0.0906, 0.0974]` | OK,OK |
| `special/easy.cnf` | SAT | 0.0895 | 0.0895 | 0.0826 | 0.0964 | `[0.0964, 0.0826]` | OK,OK |
| `large/test_3.cnf` | UNSAT | 0.0770 | 0.0770 | 0.0745 | 0.0794 | `[0.0745, 0.0794]` | OK,OK |

## All Cases

| case | satsolver result | satsolver avg s | satsolver_fast result | satsolver_fast avg s | satsolver_blaze result | satsolver_blaze avg s | satsolver_pysat result | satsolver_pysat avg s | best solver | spread s |
|---|---|---:|---|---:|---|---:|---|---:|---|---:|
| `small/test_1.cnf` | SAT | 0.0252 | SAT | 0.0412 | SAT | 0.0624 | SAT | 0.0521 | `satsolver` | 0.0371 |
| `small/test_2.cnf` | SAT | 0.0245 | SAT | 0.0387 | SAT | 0.0715 | SAT | 0.0556 | `satsolver` | 0.0470 |
| `small/test_3.cnf` | SAT | 0.0295 | SAT | 0.0273 | SAT | 0.0582 | SAT | 0.0497 | `satsolver_fast` | 0.0309 |
| `small/test_4.cnf` | UNSAT | 0.0286 | UNSAT | 0.0266 | UNSAT | 0.0777 | UNSAT | 0.0551 | `satsolver_fast` | 0.0511 |
| `small/test_5.cnf` | SAT | 0.0395 | SAT | 0.0309 | SAT | 0.0734 | SAT | 0.0538 | `satsolver_fast` | 0.0424 |
| `small/test_6.cnf` | SAT | 0.0292 | SAT | 0.0349 | SAT | 0.0655 | SAT | 0.0542 | `satsolver` | 0.0363 |
| `small/test_7.cnf` | SAT | 0.0326 | SAT | 0.0251 | SAT | 0.0628 | SAT | 0.0514 | `satsolver_fast` | 0.0377 |
| `small/test_8.cnf` | UNSAT | 0.0331 | UNSAT | 0.0366 | UNSAT | 0.0705 | UNSAT | 0.0605 | `satsolver` | 0.0374 |
| `small/test_9.cnf` | SAT | 0.0300 | SAT | 0.0302 | SAT | 0.0646 | SAT | 0.0633 | `satsolver` | 0.0346 |
| `small/test_10.cnf` | UNSAT | 0.0339 | UNSAT | 0.0319 | UNSAT | 0.0546 | UNSAT | 0.0599 | `satsolver_fast` | 0.0281 |
| `medium/test_1.cnf` | UNSAT | 0.0401 | UNSAT | 0.0338 | UNSAT | 0.0670 | UNSAT | 0.0680 | `satsolver_fast` | 0.0342 |
| `medium/test_2.cnf` | UNSAT | 0.0373 | UNSAT | 0.0367 | UNSAT | 0.0725 | UNSAT | 0.0545 | `satsolver_fast` | 0.0358 |
| `medium/test_3.cnf` | UNSAT | 0.5006 | UNSAT | 0.4894 | UNSAT | 0.9838 | UNSAT | 0.0940 | `satsolver_pysat` | 0.8898 |
| `medium/test_4.cnf` | UNSAT | 0.8626 | UNSAT | 0.8494 | UNSAT | 2.3128 | UNSAT | 0.1115 | `satsolver_pysat` | 2.2012 |
| `medium/test_5.cnf` | UNSAT | 0.0341 | UNSAT | 0.0294 | UNSAT | 0.0624 | UNSAT | 0.0518 | `satsolver_fast` | 0.0330 |
| `medium/test_6.cnf` | UNSAT | 0.0354 | UNSAT | 0.0279 | UNSAT | 0.0697 | UNSAT | 0.0503 | `satsolver_fast` | 0.0418 |
| `medium/test_7.cnf` | UNSAT | 0.0333 | UNSAT | 0.0330 | UNSAT | 0.0717 | UNSAT | 0.0583 | `satsolver_fast` | 0.0387 |
| `medium/test_8.cnf` | SAT | 0.0295 | SAT | 0.0305 | SAT | 0.0567 | SAT | 0.0632 | `satsolver` | 0.0337 |
| `medium/test_9.cnf` | SAT | 0.0358 | SAT | 0.0307 | SAT | 0.0572 | SAT | 0.0625 | `satsolver_fast` | 0.0318 |
| `medium/test_10.cnf` | UNSAT | 0.0417 | UNSAT | 0.0403 | UNSAT | 0.0679 | UNSAT | 0.0524 | `satsolver_fast` | 0.0276 |
| `large/test_1.cnf` | SAT | 0.0480 | SAT | 0.0466 | SAT | 0.0717 | SAT | 0.0602 | `satsolver_fast` | 0.0250 |
| `large/test_2.cnf` | SAT | 0.0384 | SAT | 0.0294 | SAT | 0.0549 | SAT | 0.0656 | `satsolver_fast` | 0.0362 |
| `large/test_3.cnf` | UNSAT | 0.2854 | UNSAT | 0.2876 | UNSAT | 0.4306 | UNSAT | 0.0770 | `satsolver_pysat` | 0.3536 |
| `large/test_4.cnf` | UNSAT | 0.2262 | UNSAT | 0.2426 | UNSAT | 0.3573 | UNSAT | 0.0638 | `satsolver_pysat` | 0.2935 |
| `large/test_5.cnf` | SAT | 0.0355 | SAT | 0.0432 | SAT | 0.0631 | SAT | 0.0583 | `satsolver` | 0.0276 |
| `large/test_6.cnf` | UNSAT | 3.5244 | UNSAT | 3.5256 | UNSAT | 15.9033 | UNSAT | 0.3841 | `satsolver_pysat` | 15.5192 |
| `large/test_7.cnf` | SAT | 0.0447 | SAT | 0.0472 | SAT | 0.0768 | SAT | 0.0614 | `satsolver` | 0.0321 |
| `large/test_8.cnf` | SAT | 1.7304 | SAT | 1.7927 | SAT | 4.7999 | SAT | 0.3674 | `satsolver_pysat` | 4.4325 |
| `large/test_9.cnf` | SAT | 0.0434 | SAT | 0.0320 | SAT | 0.0707 | SAT | 0.0645 | `satsolver_fast` | 0.0387 |
| `large/test_10.cnf` | UNSAT | 0.8615 | UNSAT | 0.8734 | UNSAT | 2.2164 | UNSAT | 0.0960 | `satsolver_pysat` | 2.1204 |
| `special/dense.cnf` | UNSAT | 0.1335 | UNSAT | 0.1307 | UNSAT | 0.1806 | UNSAT | 0.0692 | `satsolver_pysat` | 0.1113 |
| `special/easy.cnf` | SAT | 0.0297 | SAT | 0.0414 | SAT | 0.0662 | SAT | 0.0895 | `satsolver` | 0.0599 |
| `special/hard.cnf` | UNSAT | 2.6295 | UNSAT | 2.6193 | UNSAT | 11.0030 | UNSAT | 0.2908 | `satsolver_pysat` | 10.7122 |
| `special/pigeonhole.cnf` | UNSAT | 0.0322 | UNSAT | 0.0290 | UNSAT | 0.0547 | UNSAT | 2.8382 | `satsolver_fast` | 2.8092 |
| `special/tseitin.cnf` | UNSAT | 0.0316 | UNSAT | 0.0274 | UNSAT | 0.0625 | UNSAT | 0.8694 | `satsolver_fast` | 0.8421 |
