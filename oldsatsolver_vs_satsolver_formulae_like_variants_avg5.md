# oldsatsolver.py vs satsolver.py formulae_like variants avg5

Generated: 2026-05-31T17:13:39
Datasets: `formulae_like_01`, `formulae_like_02`, `formulae_like_03`
Old solver command: `python odlsatsover.py <input.cnf> <output.txt>`
New solver command: `python satsolver.py <input.cnf> <output.txt>`
Repeats per solver per case: `5`
Per-run timeout: `60s`
Validation: `tools/checker.py` plus manifest expected SAT/UNSAT labels.

## Summary

- Cases tested: `105`
- Old ok: `105/105`
- New ok: `105/105`
- Timeout cases: `0`
- Old avg-total: `13.9262s`
- New avg-total: `11.3928s`
- Delta new-old: `-2.5333s`
- Improved valid cases: `97`
- Regressed valid cases: `6`
- Tied valid cases: `2`
- Benchmark wall time: `186.7057s`

## By Dataset

| dataset | cases | old ok | new ok | old avg-total s | new avg-total s | delta s | improved | regressed | tied |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| `formulae_like_01` | 35 | 35/35 | 35/35 | 5.3987 | 4.5658 | -0.8330 | 34 | 1 | 0 |
| `formulae_like_02` | 35 | 35/35 | 35/35 | 3.5859 | 4.3140 | +0.7281 | 32 | 3 | 0 |
| `formulae_like_03` | 35 | 35/35 | 35/35 | 4.9415 | 2.5131 | -2.4284 | 31 | 2 | 2 |

## By Category

| dataset | category | cases | old avg-total s | new avg-total s | delta s |
|---|---|---:|---:|---:|---:|
| `formulae_like_01` | `small` | 10 | 0.4270 | 0.3323 | -0.0947 |
| `formulae_like_01` | `medium` | 10 | 2.6017 | 2.9682 | +0.3664 |
| `formulae_like_01` | `large` | 10 | 2.0748 | 1.0191 | -1.0556 |
| `formulae_like_01` | `special` | 5 | 0.2953 | 0.2462 | -0.0491 |
| `formulae_like_02` | `small` | 10 | 0.4315 | 0.3427 | -0.0888 |
| `formulae_like_02` | `medium` | 10 | 1.7140 | 1.9901 | +0.2762 |
| `formulae_like_02` | `large` | 10 | 1.1055 | 1.7421 | +0.6366 |
| `formulae_like_02` | `special` | 5 | 0.3350 | 0.2390 | -0.0960 |
| `formulae_like_03` | `small` | 10 | 0.4203 | 0.3264 | -0.0939 |
| `formulae_like_03` | `medium` | 10 | 0.9479 | 1.2005 | +0.2526 |
| `formulae_like_03` | `large` | 10 | 3.2913 | 0.7332 | -2.5581 |
| `formulae_like_03` | `special` | 5 | 0.2820 | 0.2529 | -0.0291 |

## Largest Improvements

| dataset | case | family | expected | old avg s | new avg s | delta s | ratio |
|---|---|---|---|---:|---:|---:|---:|
| `formulae_like_03` | `large/test_1.cnf` | planted_3sat | SAT | 1.6061 | 0.1011 | -1.5051 | 0.063x |
| `formulae_like_03` | `large/test_2.cnf` | planted_3sat | SAT | 1.0807 | 0.1118 | -0.9689 | 0.103x |
| `formulae_like_01` | `large/test_1.cnf` | planted_3sat | SAT | 0.9459 | 0.3332 | -0.6127 | 0.352x |
| `formulae_like_01` | `large/test_2.cnf` | planted_3sat | SAT | 0.5425 | 0.1828 | -0.3597 | 0.337x |
| `formulae_like_02` | `large/test_2.cnf` | planted_3sat | SAT | 0.3465 | 0.1046 | -0.2419 | 0.302x |
| `formulae_like_01` | `medium/test_3.cnf` | planted_3sat | SAT | 0.1708 | 0.0836 | -0.0872 | 0.489x |
| `formulae_like_03` | `medium/test_3.cnf` | planted_3sat | SAT | 0.1526 | 0.0725 | -0.0801 | 0.475x |
| `formulae_like_02` | `special/dense.cnf` | planted_3sat_dense | SAT | 0.1410 | 0.0816 | -0.0594 | 0.579x |
| `formulae_like_03` | `large/test_6.cnf` | planted_3sat | SAT | 0.1123 | 0.0915 | -0.0208 | 0.815x |
| `formulae_like_01` | `small/test_2.cnf` | planted_3sat | SAT | 0.0500 | 0.0295 | -0.0205 | 0.589x |
| `formulae_like_02` | `small/test_3.cnf` | planted_3sat | SAT | 0.0533 | 0.0329 | -0.0204 | 0.617x |
| `formulae_like_02` | `large/test_5.cnf` | planted_3sat | SAT | 0.1067 | 0.0879 | -0.0188 | 0.824x |
| `formulae_like_02` | `medium/test_2.cnf` | planted_3sat | SAT | 0.0633 | 0.0450 | -0.0183 | 0.710x |
| `formulae_like_01` | `medium/test_9.cnf` | xor_parity | UNSAT | 0.0490 | 0.0311 | -0.0179 | 0.634x |
| `formulae_like_01` | `large/test_9.cnf` | xor_parity | UNSAT | 0.0542 | 0.0374 | -0.0168 | 0.690x |

## Largest Regressions

| dataset | case | family | expected | old avg s | new avg s | delta s | ratio |
|---|---|---|---|---:|---:|---:|---:|
| `formulae_like_02` | `large/test_1.cnf` | planted_3sat | SAT | 0.1623 | 1.1190 | +0.9566 | 6.893x |
| `formulae_like_01` | `medium/test_4.cnf` | planted_3sat | SAT | 2.0584 | 2.6025 | +0.5442 | 1.264x |
| `formulae_like_03` | `medium/test_4.cnf` | planted_3sat | SAT | 0.4393 | 0.8104 | +0.3711 | 1.845x |
| `formulae_like_02` | `medium/test_4.cnf` | planted_3sat | SAT | 1.2790 | 1.5884 | +0.3094 | 1.242x |
| `formulae_like_02` | `medium/test_3.cnf` | planted_3sat | SAT | 0.0764 | 0.1231 | +0.0467 | 1.611x |
| `formulae_like_03` | `medium/test_2.cnf` | planted_3sat | SAT | 0.0443 | 0.0499 | +0.0056 | 1.126x |
| `formulae_like_03` | `special/dense.cnf` | planted_3sat_dense | SAT | 0.0900 | 0.0892 | -0.0009 | 0.990x |
| `formulae_like_03` | `medium/test_10.cnf` | graph_coloring | SAT | 0.0449 | 0.0439 | -0.0009 | 0.979x |
| `formulae_like_03` | `small/test_1.cnf` | planted_3sat | SAT | 0.0383 | 0.0369 | -0.0014 | 0.964x |
| `formulae_like_01` | `small/test_1.cnf` | planted_3sat | SAT | 0.0428 | 0.0406 | -0.0021 | 0.950x |
| `formulae_like_01` | `small/test_7.cnf` | graph_coloring | UNSAT | 0.0385 | 0.0361 | -0.0024 | 0.938x |
| `formulae_like_03` | `special/xor.cnf` | xor_parity | UNSAT | 0.0451 | 0.0424 | -0.0027 | 0.941x |
| `formulae_like_02` | `special/easy.cnf` | unit | SAT | 0.0381 | 0.0354 | -0.0028 | 0.927x |
| `formulae_like_03` | `medium/test_9.cnf` | xor_parity | UNSAT | 0.0441 | 0.0412 | -0.0028 | 0.936x |
| `formulae_like_03` | `medium/test_5.cnf` | pigeonhole | UNSAT | 0.0368 | 0.0339 | -0.0030 | 0.919x |

## All Cases

| dataset | case | vars | clauses | family | expected | old avg s | old median s | new avg s | new median s | delta s | ratio | old status | new status |
|---|---|---:|---:|---|---|---:|---:|---:|---:|---:|---:|---|---|
| `formulae_like_01` | `small/test_1.cnf` | 20 | 85 | planted_3sat | SAT | 0.0428 | 0.0426 | 0.0406 | 0.0399 | -0.0021 | 0.950x | SAT | SAT |
| `formulae_like_01` | `small/test_2.cnf` | 30 | 128 | planted_3sat | SAT | 0.0500 | 0.0503 | 0.0295 | 0.0280 | -0.0205 | 0.589x | SAT | SAT |
| `formulae_like_01` | `small/test_3.cnf` | 40 | 170 | planted_3sat | SAT | 0.0440 | 0.0432 | 0.0334 | 0.0329 | -0.0106 | 0.759x | SAT | SAT |
| `formulae_like_01` | `small/test_4.cnf` | 18 | 48 | xor_parity | UNSAT | 0.0449 | 0.0428 | 0.0295 | 0.0300 | -0.0154 | 0.657x | UNSAT | UNSAT |
| `formulae_like_01` | `small/test_5.cnf` | 24 | 96 | xor_parity | SAT | 0.0487 | 0.0484 | 0.0353 | 0.0329 | -0.0134 | 0.725x | SAT | SAT |
| `formulae_like_01` | `small/test_6.cnf` | 20 | 45 | pigeonhole | UNSAT | 0.0408 | 0.0376 | 0.0325 | 0.0286 | -0.0083 | 0.796x | UNSAT | UNSAT |
| `formulae_like_01` | `small/test_7.cnf` | 12 | 34 | graph_coloring | UNSAT | 0.0385 | 0.0350 | 0.0361 | 0.0346 | -0.0024 | 0.938x | UNSAT | UNSAT |
| `formulae_like_01` | `small/test_8.cnf` | 25 | 165 | nqueens | SAT | 0.0337 | 0.0333 | 0.0297 | 0.0314 | -0.0040 | 0.881x | SAT | SAT |
| `formulae_like_01` | `small/test_9.cnf` | 32 | 56 | cardinality | SAT | 0.0397 | 0.0371 | 0.0352 | 0.0316 | -0.0044 | 0.888x | SAT | SAT |
| `formulae_like_01` | `small/test_10.cnf` | 40 | 41 | horn_chain | UNSAT | 0.0439 | 0.0430 | 0.0305 | 0.0281 | -0.0135 | 0.694x | UNSAT | UNSAT |
| `formulae_like_01` | `medium/test_1.cnf` | 60 | 255 | planted_3sat | SAT | 0.0453 | 0.0444 | 0.0303 | 0.0266 | -0.0150 | 0.669x | SAT | SAT |
| `formulae_like_01` | `medium/test_2.cnf` | 100 | 425 | planted_3sat | SAT | 0.0620 | 0.0617 | 0.0553 | 0.0569 | -0.0067 | 0.892x | SAT | SAT |
| `formulae_like_01` | `medium/test_3.cnf` | 160 | 650 | planted_3sat | SAT | 0.1708 | 0.1764 | 0.0836 | 0.0847 | -0.0872 | 0.489x | SAT | SAT |
| `formulae_like_01` | `medium/test_4.cnf` | 200 | 820 | planted_3sat | SAT | 2.0584 | 2.0281 | 2.6025 | 2.6153 | +0.5442 | 1.264x | SAT | SAT |
| `formulae_like_01` | `medium/test_5.cnf` | 72 | 297 | pigeonhole | UNSAT | 0.0417 | 0.0420 | 0.0312 | 0.0299 | -0.0105 | 0.748x | UNSAT | UNSAT |
| `formulae_like_01` | `medium/test_6.cnf` | 90 | 415 | pigeonhole | UNSAT | 0.0409 | 0.0415 | 0.0317 | 0.0291 | -0.0093 | 0.774x | UNSAT | UNSAT |
| `formulae_like_01` | `medium/test_7.cnf` | 56 | 372 | graph_coloring | UNSAT | 0.0430 | 0.0455 | 0.0294 | 0.0268 | -0.0135 | 0.685x | UNSAT | UNSAT |
| `formulae_like_01` | `medium/test_8.cnf` | 96 | 500 | xor_parity | SAT | 0.0448 | 0.0425 | 0.0383 | 0.0320 | -0.0065 | 0.855x | SAT | SAT |
| `formulae_like_01` | `medium/test_9.cnf` | 128 | 660 | xor_parity | UNSAT | 0.0490 | 0.0467 | 0.0311 | 0.0317 | -0.0179 | 0.634x | UNSAT | UNSAT |
| `formulae_like_01` | `medium/test_10.cnf` | 90 | 570 | graph_coloring | SAT | 0.0458 | 0.0458 | 0.0348 | 0.0349 | -0.0110 | 0.759x | SAT | SAT |
| `formulae_like_01` | `large/test_1.cnf` | 220 | 1000 | planted_3sat | SAT | 0.9459 | 0.9523 | 0.3332 | 0.3381 | -0.6127 | 0.352x | SAT | SAT |
| `formulae_like_01` | `large/test_2.cnf` | 260 | 1060 | planted_3sat | SAT | 0.5425 | 0.5363 | 0.1828 | 0.1842 | -0.3597 | 0.337x | SAT | SAT |
| `formulae_like_01` | `large/test_3.cnf` | 300 | 1000 | planted_3sat | SAT | 0.0930 | 0.0965 | 0.0863 | 0.0861 | -0.0067 | 0.927x | SAT | SAT |
| `formulae_like_01` | `large/test_4.cnf` | 360 | 1000 | planted_3sat | SAT | 0.0954 | 0.0945 | 0.0904 | 0.0893 | -0.0050 | 0.947x | SAT | SAT |
| `formulae_like_01` | `large/test_5.cnf` | 420 | 1050 | planted_3sat | SAT | 0.1009 | 0.1040 | 0.0890 | 0.0898 | -0.0119 | 0.882x | SAT | SAT |
| `formulae_like_01` | `large/test_6.cnf` | 480 | 1120 | planted_3sat | SAT | 0.1034 | 0.1012 | 0.0911 | 0.0906 | -0.0123 | 0.881x | SAT | SAT |
| `formulae_like_01` | `large/test_7.cnf` | 210 | 1485 | pigeonhole | UNSAT | 0.0437 | 0.0384 | 0.0325 | 0.0331 | -0.0112 | 0.745x | UNSAT | UNSAT |
| `formulae_like_01` | `large/test_8.cnf` | 240 | 1816 | pigeonhole | UNSAT | 0.0423 | 0.0396 | 0.0339 | 0.0288 | -0.0083 | 0.803x | UNSAT | UNSAT |
| `formulae_like_01` | `large/test_9.cnf` | 240 | 1360 | xor_parity | UNSAT | 0.0542 | 0.0511 | 0.0374 | 0.0347 | -0.0168 | 0.690x | UNSAT | UNSAT |
| `formulae_like_01` | `large/test_10.cnf` | 345 | 1900 | graph_coloring | SAT | 0.0535 | 0.0532 | 0.0426 | 0.0408 | -0.0109 | 0.796x | SAT | SAT |
| `formulae_like_01` | `special/coloring.cnf` | 500 | 1875 | graph_coloring | SAT | 0.0558 | 0.0529 | 0.0429 | 0.0416 | -0.0129 | 0.769x | SAT | SAT |
| `formulae_like_01` | `special/dense.cnf` | 200 | 1300 | planted_3sat_dense | SAT | 0.1038 | 0.1057 | 0.0969 | 0.0947 | -0.0069 | 0.933x | SAT | SAT |
| `formulae_like_01` | `special/easy.cnf` | 100 | 100 | unit | SAT | 0.0413 | 0.0412 | 0.0364 | 0.0368 | -0.0049 | 0.881x | SAT | SAT |
| `formulae_like_01` | `special/hard.cnf` | 90 | 775 | graph_coloring | UNSAT | 0.0403 | 0.0382 | 0.0319 | 0.0304 | -0.0083 | 0.794x | UNSAT | UNSAT |
| `formulae_like_01` | `special/xor.cnf` | 300 | 1680 | xor_parity | UNSAT | 0.0542 | 0.0534 | 0.0381 | 0.0348 | -0.0161 | 0.704x | UNSAT | UNSAT |
| `formulae_like_02` | `small/test_1.cnf` | 20 | 85 | planted_3sat | SAT | 0.0422 | 0.0433 | 0.0322 | 0.0312 | -0.0100 | 0.763x | SAT | SAT |
| `formulae_like_02` | `small/test_2.cnf` | 30 | 128 | planted_3sat | SAT | 0.0439 | 0.0435 | 0.0327 | 0.0333 | -0.0113 | 0.744x | SAT | SAT |
| `formulae_like_02` | `small/test_3.cnf` | 40 | 170 | planted_3sat | SAT | 0.0533 | 0.0537 | 0.0329 | 0.0317 | -0.0204 | 0.617x | SAT | SAT |
| `formulae_like_02` | `small/test_4.cnf` | 18 | 48 | xor_parity | UNSAT | 0.0410 | 0.0423 | 0.0334 | 0.0281 | -0.0076 | 0.814x | UNSAT | UNSAT |
| `formulae_like_02` | `small/test_5.cnf` | 24 | 96 | xor_parity | SAT | 0.0421 | 0.0432 | 0.0336 | 0.0313 | -0.0085 | 0.798x | SAT | SAT |
| `formulae_like_02` | `small/test_6.cnf` | 30 | 81 | pigeonhole | UNSAT | 0.0393 | 0.0360 | 0.0353 | 0.0367 | -0.0040 | 0.898x | UNSAT | UNSAT |
| `formulae_like_02` | `small/test_7.cnf` | 20 | 75 | graph_coloring | UNSAT | 0.0429 | 0.0426 | 0.0359 | 0.0358 | -0.0070 | 0.836x | UNSAT | UNSAT |
| `formulae_like_02` | `small/test_8.cnf` | 25 | 165 | nqueens | SAT | 0.0412 | 0.0392 | 0.0333 | 0.0342 | -0.0079 | 0.809x | SAT | SAT |
| `formulae_like_02` | `small/test_9.cnf` | 45 | 99 | cardinality | SAT | 0.0383 | 0.0389 | 0.0333 | 0.0267 | -0.0050 | 0.869x | SAT | SAT |
| `formulae_like_02` | `small/test_10.cnf` | 44 | 45 | horn_chain | UNSAT | 0.0473 | 0.0481 | 0.0403 | 0.0390 | -0.0070 | 0.852x | UNSAT | UNSAT |
| `formulae_like_02` | `medium/test_1.cnf` | 60 | 255 | planted_3sat | SAT | 0.0408 | 0.0389 | 0.0334 | 0.0312 | -0.0073 | 0.820x | SAT | SAT |
| `formulae_like_02` | `medium/test_2.cnf` | 100 | 425 | planted_3sat | SAT | 0.0633 | 0.0649 | 0.0450 | 0.0420 | -0.0183 | 0.710x | SAT | SAT |
| `formulae_like_02` | `medium/test_3.cnf` | 160 | 682 | planted_3sat | SAT | 0.0764 | 0.0741 | 0.1231 | 0.1257 | +0.0467 | 1.611x | SAT | SAT |
| `formulae_like_02` | `medium/test_4.cnf` | 200 | 850 | planted_3sat | SAT | 1.2790 | 1.2726 | 1.5884 | 1.5874 | +0.3094 | 1.242x | SAT | SAT |
| `formulae_like_02` | `medium/test_5.cnf` | 72 | 297 | pigeonhole | UNSAT | 0.0365 | 0.0369 | 0.0277 | 0.0245 | -0.0087 | 0.760x | UNSAT | UNSAT |
| `formulae_like_02` | `medium/test_6.cnf` | 90 | 415 | pigeonhole | UNSAT | 0.0374 | 0.0370 | 0.0286 | 0.0255 | -0.0089 | 0.763x | UNSAT | UNSAT |
| `formulae_like_02` | `medium/test_7.cnf` | 72 | 549 | graph_coloring | UNSAT | 0.0425 | 0.0449 | 0.0333 | 0.0311 | -0.0092 | 0.784x | UNSAT | UNSAT |
| `formulae_like_02` | `medium/test_8.cnf` | 96 | 500 | xor_parity | SAT | 0.0496 | 0.0521 | 0.0397 | 0.0384 | -0.0099 | 0.800x | SAT | SAT |
| `formulae_like_02` | `medium/test_9.cnf` | 128 | 660 | xor_parity | UNSAT | 0.0399 | 0.0381 | 0.0327 | 0.0308 | -0.0071 | 0.821x | UNSAT | UNSAT |
| `formulae_like_02` | `medium/test_10.cnf` | 102 | 661 | graph_coloring | SAT | 0.0486 | 0.0473 | 0.0383 | 0.0404 | -0.0103 | 0.788x | SAT | SAT |
| `formulae_like_02` | `large/test_1.cnf` | 230 | 1035 | planted_3sat | SAT | 0.1623 | 0.1626 | 1.1190 | 1.0975 | +0.9566 | 6.893x | SAT | SAT |
| `formulae_like_02` | `large/test_2.cnf` | 270 | 1080 | planted_3sat | SAT | 0.3465 | 0.3454 | 0.1046 | 0.1083 | -0.2419 | 0.302x | SAT | SAT |
| `formulae_like_02` | `large/test_3.cnf` | 310 | 1010 | planted_3sat | SAT | 0.1083 | 0.1091 | 0.0940 | 0.0958 | -0.0143 | 0.868x | SAT | SAT |
| `formulae_like_02` | `large/test_4.cnf` | 370 | 1040 | planted_3sat | SAT | 0.0917 | 0.0915 | 0.0871 | 0.0871 | -0.0046 | 0.950x | SAT | SAT |
| `formulae_like_02` | `large/test_5.cnf` | 430 | 1120 | planted_3sat | SAT | 0.1067 | 0.1028 | 0.0879 | 0.0881 | -0.0188 | 0.824x | SAT | SAT |
| `formulae_like_02` | `large/test_6.cnf` | 490 | 1200 | planted_3sat | SAT | 0.1044 | 0.1041 | 0.0912 | 0.0935 | -0.0132 | 0.873x | SAT | SAT |
| `formulae_like_02` | `large/test_7.cnf` | 210 | 1485 | pigeonhole | UNSAT | 0.0431 | 0.0363 | 0.0383 | 0.0427 | -0.0048 | 0.889x | UNSAT | UNSAT |
| `formulae_like_02` | `large/test_8.cnf` | 240 | 1816 | pigeonhole | UNSAT | 0.0448 | 0.0425 | 0.0316 | 0.0297 | -0.0133 | 0.704x | UNSAT | UNSAT |
| `formulae_like_02` | `large/test_9.cnf` | 256 | 1520 | xor_parity | UNSAT | 0.0456 | 0.0428 | 0.0402 | 0.0409 | -0.0054 | 0.882x | UNSAT | UNSAT |
| `formulae_like_02` | `large/test_10.cnf` | 360 | 1950 | graph_coloring | SAT | 0.0520 | 0.0483 | 0.0482 | 0.0482 | -0.0037 | 0.928x | SAT | SAT |
| `formulae_like_02` | `special/coloring.cnf` | 500 | 1935 | graph_coloring | SAT | 0.0643 | 0.0583 | 0.0512 | 0.0506 | -0.0131 | 0.797x | SAT | SAT |
| `formulae_like_02` | `special/dense.cnf` | 200 | 1450 | planted_3sat_dense | SAT | 0.1410 | 0.1448 | 0.0816 | 0.0816 | -0.0594 | 0.579x | SAT | SAT |
| `formulae_like_02` | `special/easy.cnf` | 140 | 140 | unit | SAT | 0.0381 | 0.0384 | 0.0354 | 0.0322 | -0.0028 | 0.927x | SAT | SAT |
| `formulae_like_02` | `special/hard.cnf` | 110 | 1056 | graph_coloring | UNSAT | 0.0388 | 0.0386 | 0.0295 | 0.0285 | -0.0093 | 0.761x | UNSAT | UNSAT |
| `formulae_like_02` | `special/xor.cnf` | 320 | 1800 | xor_parity | UNSAT | 0.0528 | 0.0563 | 0.0413 | 0.0411 | -0.0115 | 0.783x | UNSAT | UNSAT |
| `formulae_like_03` | `small/test_1.cnf` | 20 | 85 | planted_3sat | SAT | 0.0383 | 0.0348 | 0.0369 | 0.0412 | -0.0014 | 0.964x | SAT | SAT |
| `formulae_like_03` | `small/test_2.cnf` | 30 | 128 | planted_3sat | SAT | 0.0421 | 0.0414 | 0.0338 | 0.0353 | -0.0084 | 0.801x | SAT | SAT |
| `formulae_like_03` | `small/test_3.cnf` | 40 | 170 | planted_3sat | SAT | 0.0430 | 0.0404 | 0.0394 | 0.0397 | -0.0035 | 0.918x | SAT | SAT |
| `formulae_like_03` | `small/test_4.cnf` | 18 | 48 | xor_parity | UNSAT | 0.0466 | 0.0465 | 0.0305 | 0.0312 | -0.0162 | 0.653x | UNSAT | UNSAT |
| `formulae_like_03` | `small/test_5.cnf` | 24 | 96 | xor_parity | SAT | 0.0447 | 0.0468 | 0.0305 | 0.0282 | -0.0142 | 0.682x | SAT | SAT |
| `formulae_like_03` | `small/test_6.cnf` | 20 | 45 | pigeonhole | UNSAT | 0.0398 | 0.0388 | 0.0331 | 0.0354 | -0.0067 | 0.832x | UNSAT | UNSAT |
| `formulae_like_03` | `small/test_7.cnf` | 12 | 34 | graph_coloring | UNSAT | 0.0460 | 0.0463 | 0.0308 | 0.0280 | -0.0151 | 0.671x | UNSAT | UNSAT |
| `formulae_like_03` | `small/test_8.cnf` | 25 | 165 | nqueens | SAT | 0.0385 | 0.0380 | 0.0283 | 0.0266 | -0.0102 | 0.734x | SAT | SAT |
| `formulae_like_03` | `small/test_9.cnf` | 40 | 70 | cardinality | SAT | 0.0413 | 0.0435 | 0.0270 | 0.0267 | -0.0143 | 0.653x | SAT | SAT |
| `formulae_like_03` | `small/test_10.cnf` | 48 | 49 | horn_chain | UNSAT | 0.0400 | 0.0378 | 0.0362 | 0.0344 | -0.0038 | 0.905x | UNSAT | UNSAT |
| `formulae_like_03` | `medium/test_1.cnf` | 60 | 255 | planted_3sat | SAT | 0.0457 | 0.0437 | 0.0363 | 0.0330 | -0.0094 | 0.794x | SAT | SAT |
| `formulae_like_03` | `medium/test_2.cnf` | 100 | 425 | planted_3sat | SAT | 0.0443 | 0.0406 | 0.0499 | 0.0485 | +0.0056 | 1.126x | SAT | SAT |
| `formulae_like_03` | `medium/test_3.cnf` | 160 | 710 | planted_3sat | SAT | 0.1526 | 0.1461 | 0.0725 | 0.0706 | -0.0801 | 0.475x | SAT | SAT |
| `formulae_like_03` | `medium/test_4.cnf` | 200 | 880 | planted_3sat | SAT | 0.4393 | 0.4396 | 0.8104 | 0.8152 | +0.3711 | 1.845x | SAT | SAT |
| `formulae_like_03` | `medium/test_5.cnf` | 72 | 297 | pigeonhole | UNSAT | 0.0368 | 0.0354 | 0.0339 | 0.0320 | -0.0030 | 0.919x | UNSAT | UNSAT |
| `formulae_like_03` | `medium/test_6.cnf` | 90 | 415 | pigeonhole | UNSAT | 0.0449 | 0.0458 | 0.0353 | 0.0363 | -0.0096 | 0.787x | UNSAT | UNSAT |
| `formulae_like_03` | `medium/test_7.cnf` | 90 | 775 | graph_coloring | UNSAT | 0.0449 | 0.0487 | 0.0373 | 0.0385 | -0.0076 | 0.831x | UNSAT | UNSAT |
| `formulae_like_03` | `medium/test_8.cnf` | 96 | 500 | xor_parity | SAT | 0.0505 | 0.0525 | 0.0398 | 0.0357 | -0.0107 | 0.788x | SAT | SAT |
| `formulae_like_03` | `medium/test_9.cnf` | 128 | 660 | xor_parity | UNSAT | 0.0441 | 0.0432 | 0.0412 | 0.0404 | -0.0028 | 0.936x | UNSAT | UNSAT |
| `formulae_like_03` | `medium/test_10.cnf` | 114 | 752 | graph_coloring | SAT | 0.0449 | 0.0407 | 0.0439 | 0.0412 | -0.0009 | 0.979x | SAT | SAT |
| `formulae_like_03` | `large/test_1.cnf` | 240 | 1050 | planted_3sat | SAT | 1.6061 | 1.5914 | 0.1011 | 0.0971 | -1.5051 | 0.063x | SAT | SAT |
| `formulae_like_03` | `large/test_2.cnf` | 280 | 1120 | planted_3sat | SAT | 1.0807 | 1.0820 | 0.1118 | 0.1107 | -0.9689 | 0.103x | SAT | SAT |
| `formulae_like_03` | `large/test_3.cnf` | 320 | 1020 | planted_3sat | SAT | 0.0935 | 0.0943 | 0.0901 | 0.0904 | -0.0035 | 0.963x | SAT | SAT |
| `formulae_like_03` | `large/test_4.cnf` | 380 | 1060 | planted_3sat | SAT | 0.1059 | 0.1069 | 0.0916 | 0.0857 | -0.0143 | 0.865x | SAT | SAT |
| `formulae_like_03` | `large/test_5.cnf` | 440 | 1150 | planted_3sat | SAT | 0.1072 | 0.1062 | 0.0907 | 0.0876 | -0.0165 | 0.846x | SAT | SAT |
| `formulae_like_03` | `large/test_6.cnf` | 500 | 1250 | planted_3sat | SAT | 0.1123 | 0.1129 | 0.0915 | 0.0927 | -0.0208 | 0.815x | SAT | SAT |
| `formulae_like_03` | `large/test_7.cnf` | 210 | 1485 | pigeonhole | UNSAT | 0.0475 | 0.0481 | 0.0389 | 0.0401 | -0.0086 | 0.820x | UNSAT | UNSAT |
| `formulae_like_03` | `large/test_8.cnf` | 240 | 1816 | pigeonhole | UNSAT | 0.0439 | 0.0380 | 0.0348 | 0.0308 | -0.0091 | 0.792x | UNSAT | UNSAT |
| `formulae_like_03` | `large/test_9.cnf` | 280 | 1720 | xor_parity | UNSAT | 0.0421 | 0.0421 | 0.0386 | 0.0413 | -0.0034 | 0.919x | UNSAT | UNSAT |
| `formulae_like_03` | `large/test_10.cnf` | 375 | 2000 | graph_coloring | SAT | 0.0520 | 0.0520 | 0.0442 | 0.0433 | -0.0078 | 0.849x | SAT | SAT |
| `formulae_like_03` | `special/coloring.cnf` | 500 | 1995 | graph_coloring | SAT | 0.0622 | 0.0662 | 0.0502 | 0.0554 | -0.0120 | 0.807x | SAT | SAT |
| `formulae_like_03` | `special/dense.cnf` | 200 | 1600 | planted_3sat_dense | SAT | 0.0900 | 0.0876 | 0.0892 | 0.0874 | -0.0009 | 0.990x | SAT | SAT |
| `formulae_like_03` | `special/easy.cnf` | 180 | 180 | unit | SAT | 0.0454 | 0.0479 | 0.0354 | 0.0350 | -0.0100 | 0.780x | SAT | SAT |
| `formulae_like_03` | `special/hard.cnf` | 132 | 1398 | graph_coloring | UNSAT | 0.0393 | 0.0382 | 0.0357 | 0.0368 | -0.0036 | 0.908x | UNSAT | UNSAT |
| `formulae_like_03` | `special/xor.cnf` | 340 | 1920 | xor_parity | UNSAT | 0.0451 | 0.0410 | 0.0424 | 0.0461 | -0.0027 | 0.941x | UNSAT | UNSAT |
