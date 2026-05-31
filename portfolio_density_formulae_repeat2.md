# PORTFOLIO_MAX_DENSITY formulae repeat2 comparison

Generated: 2026-05-31T17:54:30
Dataset: `formulae`
Repeats per case: `2`
Per-run timeout: `60s`
Densities tested: `4.2, 4.3, 4.35, 4.4`
Solver variants were created in temporary directories; the working `satsolver_core.py` was not edited by this benchmark.
Validation: `tools/checker.py`.

## Summary

- Cases tested per density: `35`
- Best avg-total density: `4.3`
- Benchmark wall time: `116.3016s`

| density | valid | timeouts | SAT | UNSAT | avg-total s | median-total s | delta vs 4.3 s | best-case count |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 4.2 | 35/35 | 0 | 16 | 19 | 12.4283 | 12.4283 | +0.2306 | 9 |
| 4.3 | 35/35 | 0 | 16 | 19 | 12.1977 | 12.1977 | +0.0000 | 17 |
| 4.35 | 35/35 | 0 | 16 | 19 | 12.9862 | 12.9862 | +0.7885 | 6 |
| 4.4 | 35/35 | 0 | 16 | 19 | 12.3008 | 12.3008 | +0.1031 | 13 |

## Most Sensitive Cases

| case | 4.2 avg s | 4.3 avg s | 4.35 avg s | 4.4 avg s | spread s | best density |
|---|---:|---:|---:|---:|---:|---:|
| `medium/test_3.cnf` | 0.5161 | 0.5152 | 0.8319 | 0.5725 | 0.3167 | 4.3 |
| `large/test_6.cnf` | 3.8428 | 3.6514 | 3.8221 | 3.6607 | 0.1914 | 4.3 |
| `medium/test_4.cnf` | 0.9489 | 0.9497 | 1.0913 | 0.9294 | 0.1619 | 4.4 |
| `large/test_8.cnf` | 1.7717 | 1.7327 | 1.8174 | 1.8460 | 0.1133 | 4.3 |
| `special/hard.cnf` | 2.7574 | 2.7510 | 2.7833 | 2.7228 | 0.0605 | 4.4 |
| `large/test_4.cnf` | 0.2808 | 0.2964 | 0.2555 | 0.2589 | 0.0409 | 4.35 |
| `large/test_10.cnf` | 0.9159 | 0.9111 | 0.9457 | 0.9082 | 0.0375 | 4.4 |
| `small/test_5.cnf` | 0.0459 | 0.0249 | 0.0287 | 0.0445 | 0.0210 | 4.3 |
| `large/test_3.cnf` | 0.3088 | 0.2976 | 0.3043 | 0.3154 | 0.0178 | 4.3 |
| `special/dense.cnf` | 0.1315 | 0.1458 | 0.1420 | 0.1284 | 0.0174 | 4.4 |
| `medium/test_10.cnf` | 0.0377 | 0.0333 | 0.0494 | 0.0396 | 0.0161 | 4.3 |
| `large/test_2.cnf` | 0.0378 | 0.0346 | 0.0497 | 0.0362 | 0.0151 | 4.3 |
| `small/test_1.cnf` | 0.0351 | 0.0488 | 0.0393 | 0.0445 | 0.0137 | 4.2 |
| `large/test_5.cnf` | 0.0374 | 0.0411 | 0.0460 | 0.0324 | 0.0136 | 4.4 |
| `special/pigeonhole.cnf` | 0.0409 | 0.0281 | 0.0323 | 0.0284 | 0.0128 | 4.3 |

## Slowest Cases Per Density

### Density 4.2

| case | result | avg s | median s | min s | max s | runs s | status |
|---|---|---:|---:|---:|---:|---|---|
| `large/test_6.cnf` | UNSAT | 3.8428 | 3.8428 | 3.8327 | 3.8528 | `[3.8327, 3.8528]` | OK,OK |
| `special/hard.cnf` | UNSAT | 2.7574 | 2.7574 | 2.7504 | 2.7643 | `[2.7643, 2.7504]` | OK,OK |
| `large/test_8.cnf` | SAT | 1.7717 | 1.7717 | 1.7454 | 1.7979 | `[1.7979, 1.7454]` | OK,OK |
| `medium/test_4.cnf` | UNSAT | 0.9489 | 0.9489 | 0.9071 | 0.9908 | `[0.9908, 0.9071]` | OK,OK |
| `large/test_10.cnf` | UNSAT | 0.9159 | 0.9159 | 0.9127 | 0.9191 | `[0.9127, 0.9191]` | OK,OK |
| `medium/test_3.cnf` | UNSAT | 0.5161 | 0.5161 | 0.5141 | 0.5182 | `[0.5141, 0.5182]` | OK,OK |
| `large/test_3.cnf` | UNSAT | 0.3088 | 0.3088 | 0.2936 | 0.3240 | `[0.2936, 0.3240]` | OK,OK |
| `large/test_4.cnf` | UNSAT | 0.2808 | 0.2808 | 0.2590 | 0.3026 | `[0.3026, 0.2590]` | OK,OK |
| `special/dense.cnf` | UNSAT | 0.1315 | 0.1315 | 0.1308 | 0.1322 | `[0.1322, 0.1308]` | OK,OK |
| `small/test_5.cnf` | SAT | 0.0459 | 0.0459 | 0.0378 | 0.0541 | `[0.0541, 0.0378]` | OK,OK |

### Density 4.3

| case | result | avg s | median s | min s | max s | runs s | status |
|---|---|---:|---:|---:|---:|---|---|
| `large/test_6.cnf` | UNSAT | 3.6514 | 3.6514 | 3.6368 | 3.6659 | `[3.6368, 3.6659]` | OK,OK |
| `special/hard.cnf` | UNSAT | 2.7510 | 2.7510 | 2.6908 | 2.8112 | `[2.6908, 2.8112]` | OK,OK |
| `large/test_8.cnf` | SAT | 1.7327 | 1.7327 | 1.7235 | 1.7419 | `[1.7419, 1.7235]` | OK,OK |
| `medium/test_4.cnf` | UNSAT | 0.9497 | 0.9497 | 0.8889 | 1.0106 | `[0.8889, 1.0106]` | OK,OK |
| `large/test_10.cnf` | UNSAT | 0.9111 | 0.9111 | 0.9027 | 0.9195 | `[0.9027, 0.9195]` | OK,OK |
| `medium/test_3.cnf` | UNSAT | 0.5152 | 0.5152 | 0.5115 | 0.5189 | `[0.5189, 0.5115]` | OK,OK |
| `large/test_3.cnf` | UNSAT | 0.2976 | 0.2976 | 0.2959 | 0.2993 | `[0.2993, 0.2959]` | OK,OK |
| `large/test_4.cnf` | UNSAT | 0.2964 | 0.2964 | 0.2764 | 0.3164 | `[0.2764, 0.3164]` | OK,OK |
| `special/dense.cnf` | UNSAT | 0.1458 | 0.1458 | 0.1456 | 0.1460 | `[0.1456, 0.1460]` | OK,OK |
| `small/test_1.cnf` | SAT | 0.0488 | 0.0488 | 0.0421 | 0.0555 | `[0.0555, 0.0421]` | OK,OK |

### Density 4.35

| case | result | avg s | median s | min s | max s | runs s | status |
|---|---|---:|---:|---:|---:|---|---|
| `large/test_6.cnf` | UNSAT | 3.8221 | 3.8221 | 3.7991 | 3.8452 | `[3.7991, 3.8452]` | OK,OK |
| `special/hard.cnf` | UNSAT | 2.7833 | 2.7833 | 2.7114 | 2.8552 | `[2.7114, 2.8552]` | OK,OK |
| `large/test_8.cnf` | SAT | 1.8174 | 1.8174 | 1.7959 | 1.8389 | `[1.8389, 1.7959]` | OK,OK |
| `medium/test_4.cnf` | UNSAT | 1.0913 | 1.0913 | 0.9957 | 1.1869 | `[1.1869, 0.9957]` | OK,OK |
| `large/test_10.cnf` | UNSAT | 0.9457 | 0.9457 | 0.9259 | 0.9655 | `[0.9259, 0.9655]` | OK,OK |
| `medium/test_3.cnf` | UNSAT | 0.8319 | 0.8319 | 0.6883 | 0.9755 | `[0.6883, 0.9755]` | OK,OK |
| `large/test_3.cnf` | UNSAT | 0.3043 | 0.3043 | 0.2924 | 0.3162 | `[0.3162, 0.2924]` | OK,OK |
| `large/test_4.cnf` | UNSAT | 0.2555 | 0.2555 | 0.2465 | 0.2644 | `[0.2644, 0.2465]` | OK,OK |
| `special/dense.cnf` | UNSAT | 0.1420 | 0.1420 | 0.1409 | 0.1431 | `[0.1409, 0.1431]` | OK,OK |
| `large/test_2.cnf` | SAT | 0.0497 | 0.0497 | 0.0473 | 0.0521 | `[0.0473, 0.0521]` | OK,OK |

### Density 4.4

| case | result | avg s | median s | min s | max s | runs s | status |
|---|---|---:|---:|---:|---:|---|---|
| `large/test_6.cnf` | UNSAT | 3.6607 | 3.6607 | 3.6534 | 3.6680 | `[3.6680, 3.6534]` | OK,OK |
| `special/hard.cnf` | UNSAT | 2.7228 | 2.7228 | 2.6902 | 2.7554 | `[2.6902, 2.7554]` | OK,OK |
| `large/test_8.cnf` | SAT | 1.8460 | 1.8460 | 1.7939 | 1.8980 | `[1.7939, 1.8980]` | OK,OK |
| `medium/test_4.cnf` | UNSAT | 0.9294 | 0.9294 | 0.9249 | 0.9339 | `[0.9249, 0.9339]` | OK,OK |
| `large/test_10.cnf` | UNSAT | 0.9082 | 0.9082 | 0.8874 | 0.9290 | `[0.8874, 0.9290]` | OK,OK |
| `medium/test_3.cnf` | UNSAT | 0.5725 | 0.5725 | 0.5239 | 0.6211 | `[0.5239, 0.6211]` | OK,OK |
| `large/test_3.cnf` | UNSAT | 0.3154 | 0.3154 | 0.3135 | 0.3173 | `[0.3173, 0.3135]` | OK,OK |
| `large/test_4.cnf` | UNSAT | 0.2589 | 0.2589 | 0.2541 | 0.2636 | `[0.2541, 0.2636]` | OK,OK |
| `special/dense.cnf` | UNSAT | 0.1284 | 0.1284 | 0.1225 | 0.1343 | `[0.1343, 0.1225]` | OK,OK |
| `large/test_1.cnf` | SAT | 0.0476 | 0.0476 | 0.0458 | 0.0494 | `[0.0494, 0.0458]` | OK,OK |

## All Cases

| case | 4.2 result | 4.2 avg s | 4.3 result | 4.3 avg s | 4.35 result | 4.35 avg s | 4.4 result | 4.4 avg s | best density | spread s |
|---|---|---:|---|---:|---|---:|---|---:|---:|---:|
| `small/test_1.cnf` | SAT | 0.0351 | SAT | 0.0488 | SAT | 0.0393 | SAT | 0.0445 | 4.2 | 0.0137 |
| `small/test_2.cnf` | SAT | 0.0371 | SAT | 0.0325 | SAT | 0.0393 | SAT | 0.0317 | 4.4 | 0.0076 |
| `small/test_3.cnf` | SAT | 0.0373 | SAT | 0.0410 | SAT | 0.0333 | SAT | 0.0315 | 4.4 | 0.0095 |
| `small/test_4.cnf` | UNSAT | 0.0395 | UNSAT | 0.0388 | UNSAT | 0.0327 | UNSAT | 0.0341 | 4.35 | 0.0067 |
| `small/test_5.cnf` | SAT | 0.0459 | SAT | 0.0249 | SAT | 0.0287 | SAT | 0.0445 | 4.3 | 0.0210 |
| `small/test_6.cnf` | SAT | 0.0349 | SAT | 0.0272 | SAT | 0.0371 | SAT | 0.0280 | 4.3 | 0.0100 |
| `small/test_7.cnf` | SAT | 0.0304 | SAT | 0.0357 | SAT | 0.0317 | SAT | 0.0300 | 4.4 | 0.0057 |
| `small/test_8.cnf` | UNSAT | 0.0314 | UNSAT | 0.0366 | UNSAT | 0.0355 | UNSAT | 0.0404 | 4.2 | 0.0090 |
| `small/test_9.cnf` | SAT | 0.0379 | SAT | 0.0343 | SAT | 0.0295 | SAT | 0.0322 | 4.35 | 0.0084 |
| `small/test_10.cnf` | UNSAT | 0.0309 | UNSAT | 0.0313 | UNSAT | 0.0400 | UNSAT | 0.0340 | 4.2 | 0.0091 |
| `medium/test_1.cnf` | UNSAT | 0.0355 | UNSAT | 0.0477 | UNSAT | 0.0421 | UNSAT | 0.0395 | 4.2 | 0.0122 |
| `medium/test_2.cnf` | UNSAT | 0.0371 | UNSAT | 0.0425 | UNSAT | 0.0359 | UNSAT | 0.0376 | 4.35 | 0.0065 |
| `medium/test_3.cnf` | UNSAT | 0.5161 | UNSAT | 0.5152 | UNSAT | 0.8319 | UNSAT | 0.5725 | 4.3 | 0.3167 |
| `medium/test_4.cnf` | UNSAT | 0.9489 | UNSAT | 0.9497 | UNSAT | 1.0913 | UNSAT | 0.9294 | 4.4 | 0.1619 |
| `medium/test_5.cnf` | UNSAT | 0.0428 | UNSAT | 0.0376 | UNSAT | 0.0425 | UNSAT | 0.0378 | 4.3 | 0.0052 |
| `medium/test_6.cnf` | UNSAT | 0.0399 | UNSAT | 0.0360 | UNSAT | 0.0410 | UNSAT | 0.0421 | 4.3 | 0.0061 |
| `medium/test_7.cnf` | UNSAT | 0.0370 | UNSAT | 0.0299 | UNSAT | 0.0339 | UNSAT | 0.0378 | 4.3 | 0.0079 |
| `medium/test_8.cnf` | SAT | 0.0303 | SAT | 0.0413 | SAT | 0.0386 | SAT | 0.0363 | 4.2 | 0.0111 |
| `medium/test_9.cnf` | SAT | 0.0332 | SAT | 0.0369 | SAT | 0.0321 | SAT | 0.0378 | 4.35 | 0.0056 |
| `medium/test_10.cnf` | UNSAT | 0.0377 | UNSAT | 0.0333 | UNSAT | 0.0494 | UNSAT | 0.0396 | 4.3 | 0.0161 |
| `large/test_1.cnf` | SAT | 0.0396 | SAT | 0.0389 | SAT | 0.0445 | SAT | 0.0476 | 4.3 | 0.0087 |
| `large/test_2.cnf` | SAT | 0.0378 | SAT | 0.0346 | SAT | 0.0497 | SAT | 0.0362 | 4.3 | 0.0151 |
| `large/test_3.cnf` | UNSAT | 0.3088 | UNSAT | 0.2976 | UNSAT | 0.3043 | UNSAT | 0.3154 | 4.3 | 0.0178 |
| `large/test_4.cnf` | UNSAT | 0.2808 | UNSAT | 0.2964 | UNSAT | 0.2555 | UNSAT | 0.2589 | 4.35 | 0.0409 |
| `large/test_5.cnf` | SAT | 0.0374 | SAT | 0.0411 | SAT | 0.0460 | SAT | 0.0324 | 4.4 | 0.0136 |
| `large/test_6.cnf` | UNSAT | 3.8428 | UNSAT | 3.6514 | UNSAT | 3.8221 | UNSAT | 3.6607 | 4.3 | 0.1914 |
| `large/test_7.cnf` | SAT | 0.0385 | SAT | 0.0433 | SAT | 0.0394 | SAT | 0.0374 | 4.4 | 0.0058 |
| `large/test_8.cnf` | SAT | 1.7717 | SAT | 1.7327 | SAT | 1.8174 | SAT | 1.8460 | 4.3 | 0.1133 |
| `large/test_9.cnf` | SAT | 0.0409 | SAT | 0.0421 | SAT | 0.0427 | SAT | 0.0412 | 4.2 | 0.0018 |
| `large/test_10.cnf` | UNSAT | 0.9159 | UNSAT | 0.9111 | UNSAT | 0.9457 | UNSAT | 0.9082 | 4.4 | 0.0375 |
| `special/dense.cnf` | UNSAT | 0.1315 | UNSAT | 0.1458 | UNSAT | 0.1420 | UNSAT | 0.1284 | 4.4 | 0.0174 |
| `special/easy.cnf` | SAT | 0.0320 | SAT | 0.0300 | SAT | 0.0427 | SAT | 0.0346 | 4.3 | 0.0127 |
| `special/hard.cnf` | UNSAT | 2.7574 | UNSAT | 2.7510 | UNSAT | 2.7833 | UNSAT | 2.7228 | 4.4 | 0.0605 |
| `special/pigeonhole.cnf` | UNSAT | 0.0409 | UNSAT | 0.0281 | UNSAT | 0.0323 | UNSAT | 0.0284 | 4.3 | 0.0128 |
| `special/tseitin.cnf` | UNSAT | 0.0336 | UNSAT | 0.0325 | UNSAT | 0.0329 | UNSAT | 0.0413 | 4.3 | 0.0088 |
