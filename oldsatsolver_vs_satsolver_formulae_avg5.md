# oldsatsolver.py vs satsolver.py formulae avg5

Generated: 2026-05-31T15:41:13
Old solver command: `python odlsatsover.py <input.cnf> <output.txt>`
New solver command: `python satsolver.py <input.cnf> <output.txt>`
Dataset: `formulae`
Repeats per solver per case: `5`
Per-run timeout: `60s`

## Summary

- Cases tested: `35`
- Old ok: `35/35`
- New ok: `35/35`
- Timeout cases: `0`
- Old avg-total: `26.1078s`
- New avg-total: `11.4830s`
- Delta new-old: `-14.6248s`
- Improved valid cases: `34`
- Regressed valid cases: `1`
- Tied valid cases: `0`
- Benchmark wall time: `205.0085s`

## Largest Improvements

| case | old avg s | new avg s | delta s | old result | new result |
|---|---:|---:|---:|---|---|
| `large/test_6.cnf` | 11.8052 | 3.4553 | -8.3499 | UNSAT | UNSAT |
| `special/hard.cnf` | 7.9773 | 2.5721 | -5.4052 | UNSAT | UNSAT |
| `large/test_10.cnf` | 1.9222 | 0.9080 | -1.0142 | UNSAT | UNSAT |
| `medium/test_4.cnf` | 1.6987 | 0.8429 | -0.8558 | UNSAT | UNSAT |
| `medium/test_3.cnf` | 0.6606 | 0.4803 | -0.1802 | UNSAT | UNSAT |
| `large/test_4.cnf` | 0.2511 | 0.2320 | -0.0191 | UNSAT | UNSAT |
| `small/test_7.cnf` | 0.0432 | 0.0266 | -0.0166 | SAT | SAT |
| `large/test_2.cnf` | 0.0486 | 0.0341 | -0.0145 | SAT | SAT |
| `special/dense.cnf` | 0.1405 | 0.1274 | -0.0131 | UNSAT | UNSAT |
| `small/test_5.cnf` | 0.0422 | 0.0293 | -0.0129 | SAT | SAT |

## Largest Regressions

| case | old avg s | new avg s | delta s | old result | new result |
|---|---:|---:|---:|---|---|
| `large/test_8.cnf` | 0.2851 | 1.7144 | +1.4294 | SAT | SAT |
| `medium/test_7.cnf` | 0.0374 | 0.0362 | -0.0012 | UNSAT | UNSAT |
| `large/test_5.cnf` | 0.0395 | 0.0356 | -0.0039 | SAT | SAT |
| `small/test_1.cnf` | 0.0354 | 0.0314 | -0.0040 | SAT | SAT |
| `special/tseitin.cnf` | 0.0387 | 0.0345 | -0.0042 | UNSAT | UNSAT |
| `small/test_4.cnf` | 0.0389 | 0.0338 | -0.0052 | UNSAT | UNSAT |
| `medium/test_10.cnf` | 0.0437 | 0.0382 | -0.0055 | UNSAT | UNSAT |
| `small/test_10.cnf` | 0.0364 | 0.0309 | -0.0055 | UNSAT | UNSAT |
| `medium/test_2.cnf` | 0.0444 | 0.0385 | -0.0059 | UNSAT | UNSAT |
| `special/easy.cnf` | 0.0421 | 0.0358 | -0.0063 | SAT | SAT |

## All Cases

| case | old avg s | old median s | old min s | old max s | new avg s | new median s | new min s | new max s | delta s | old status | new status |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---|---|
| `large/test_1.cnf` | 0.0548 | 0.0534 | 0.0493 | 0.0651 | 0.0442 | 0.0426 | 0.0368 | 0.0530 | -0.0106 | SAT | SAT |
| `large/test_10.cnf` | 1.9222 | 1.8815 | 1.7255 | 2.1920 | 0.9080 | 0.9094 | 0.8592 | 0.9661 | -1.0142 | UNSAT | UNSAT |
| `large/test_2.cnf` | 0.0486 | 0.0497 | 0.0424 | 0.0540 | 0.0341 | 0.0326 | 0.0312 | 0.0380 | -0.0145 | SAT | SAT |
| `large/test_3.cnf` | 0.3008 | 0.3012 | 0.2933 | 0.3077 | 0.2880 | 0.2880 | 0.2710 | 0.3094 | -0.0128 | UNSAT | UNSAT |
| `large/test_4.cnf` | 0.2511 | 0.2509 | 0.2349 | 0.2665 | 0.2320 | 0.2253 | 0.2213 | 0.2465 | -0.0191 | UNSAT | UNSAT |
| `large/test_5.cnf` | 0.0395 | 0.0371 | 0.0342 | 0.0497 | 0.0356 | 0.0352 | 0.0282 | 0.0432 | -0.0039 | SAT | SAT |
| `large/test_6.cnf` | 11.8052 | 11.8106 | 11.3424 | 12.4522 | 3.4553 | 3.4534 | 3.3328 | 3.6012 | -8.3499 | UNSAT | UNSAT |
| `large/test_7.cnf` | 0.0433 | 0.0401 | 0.0394 | 0.0532 | 0.0346 | 0.0342 | 0.0326 | 0.0379 | -0.0087 | SAT | SAT |
| `large/test_8.cnf` | 0.2851 | 0.2848 | 0.2766 | 0.2985 | 1.7144 | 1.6877 | 1.5891 | 1.8278 | +1.4294 | SAT | SAT |
| `large/test_9.cnf` | 0.0467 | 0.0467 | 0.0395 | 0.0540 | 0.0379 | 0.0349 | 0.0321 | 0.0451 | -0.0088 | SAT | SAT |
| `medium/test_1.cnf` | 0.0464 | 0.0473 | 0.0368 | 0.0530 | 0.0371 | 0.0398 | 0.0287 | 0.0430 | -0.0093 | UNSAT | UNSAT |
| `medium/test_10.cnf` | 0.0437 | 0.0449 | 0.0358 | 0.0477 | 0.0382 | 0.0408 | 0.0286 | 0.0428 | -0.0055 | UNSAT | UNSAT |
| `medium/test_2.cnf` | 0.0444 | 0.0489 | 0.0355 | 0.0510 | 0.0385 | 0.0396 | 0.0298 | 0.0438 | -0.0059 | UNSAT | UNSAT |
| `medium/test_3.cnf` | 0.6606 | 0.6630 | 0.6461 | 0.6697 | 0.4803 | 0.4814 | 0.4698 | 0.4866 | -0.1802 | UNSAT | UNSAT |
| `medium/test_4.cnf` | 1.6987 | 1.6652 | 1.6461 | 1.7816 | 0.8429 | 0.8456 | 0.8358 | 0.8485 | -0.8558 | UNSAT | UNSAT |
| `medium/test_5.cnf` | 0.0430 | 0.0460 | 0.0352 | 0.0503 | 0.0333 | 0.0310 | 0.0286 | 0.0408 | -0.0097 | UNSAT | UNSAT |
| `medium/test_6.cnf` | 0.0381 | 0.0368 | 0.0327 | 0.0468 | 0.0300 | 0.0288 | 0.0275 | 0.0369 | -0.0080 | UNSAT | UNSAT |
| `medium/test_7.cnf` | 0.0374 | 0.0360 | 0.0342 | 0.0409 | 0.0362 | 0.0384 | 0.0273 | 0.0422 | -0.0012 | UNSAT | UNSAT |
| `medium/test_8.cnf` | 0.0400 | 0.0419 | 0.0326 | 0.0458 | 0.0329 | 0.0355 | 0.0252 | 0.0397 | -0.0071 | SAT | SAT |
| `medium/test_9.cnf` | 0.0418 | 0.0433 | 0.0311 | 0.0485 | 0.0327 | 0.0373 | 0.0243 | 0.0400 | -0.0091 | SAT | SAT |
| `small/test_1.cnf` | 0.0354 | 0.0302 | 0.0290 | 0.0440 | 0.0314 | 0.0347 | 0.0219 | 0.0383 | -0.0040 | SAT | SAT |
| `small/test_10.cnf` | 0.0364 | 0.0340 | 0.0302 | 0.0439 | 0.0309 | 0.0300 | 0.0235 | 0.0384 | -0.0055 | UNSAT | UNSAT |
| `small/test_2.cnf` | 0.0362 | 0.0339 | 0.0298 | 0.0436 | 0.0287 | 0.0256 | 0.0232 | 0.0370 | -0.0075 | SAT | SAT |
| `small/test_3.cnf` | 0.0364 | 0.0387 | 0.0301 | 0.0434 | 0.0294 | 0.0308 | 0.0229 | 0.0367 | -0.0070 | SAT | SAT |
| `small/test_4.cnf` | 0.0389 | 0.0420 | 0.0303 | 0.0475 | 0.0338 | 0.0354 | 0.0235 | 0.0379 | -0.0052 | UNSAT | UNSAT |
| `small/test_5.cnf` | 0.0422 | 0.0454 | 0.0337 | 0.0511 | 0.0293 | 0.0260 | 0.0233 | 0.0367 | -0.0129 | SAT | SAT |
| `small/test_6.cnf` | 0.0402 | 0.0403 | 0.0343 | 0.0463 | 0.0305 | 0.0337 | 0.0231 | 0.0356 | -0.0097 | SAT | SAT |
| `small/test_7.cnf` | 0.0432 | 0.0451 | 0.0316 | 0.0484 | 0.0266 | 0.0246 | 0.0235 | 0.0355 | -0.0166 | SAT | SAT |
| `small/test_8.cnf` | 0.0353 | 0.0303 | 0.0269 | 0.0450 | 0.0277 | 0.0250 | 0.0222 | 0.0372 | -0.0075 | UNSAT | UNSAT |
| `small/test_9.cnf` | 0.0381 | 0.0419 | 0.0300 | 0.0443 | 0.0300 | 0.0341 | 0.0228 | 0.0354 | -0.0081 | SAT | SAT |
| `special/dense.cnf` | 0.1405 | 0.1419 | 0.1323 | 0.1469 | 0.1274 | 0.1311 | 0.1185 | 0.1330 | -0.0131 | UNSAT | UNSAT |
| `special/easy.cnf` | 0.0421 | 0.0462 | 0.0339 | 0.0489 | 0.0358 | 0.0378 | 0.0239 | 0.0420 | -0.0063 | SAT | SAT |
| `special/hard.cnf` | 7.9773 | 7.9441 | 7.9030 | 8.0928 | 2.5721 | 2.5862 | 2.5113 | 2.6295 | -5.4052 | UNSAT | UNSAT |
| `special/pigeonhole.cnf` | 0.0355 | 0.0358 | 0.0309 | 0.0419 | 0.0285 | 0.0235 | 0.0227 | 0.0375 | -0.0069 | UNSAT | UNSAT |
| `special/tseitin.cnf` | 0.0387 | 0.0403 | 0.0302 | 0.0421 | 0.0345 | 0.0343 | 0.0313 | 0.0391 | -0.0042 | UNSAT | UNSAT |
