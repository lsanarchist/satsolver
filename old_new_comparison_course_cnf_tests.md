# Old vs New SAT Solver Comparison

- Tests: `course_cnf_tests` (`279` CNF files, within 500 variables / 2000 clauses)
- Old solver: `HEAD` snapshot at run start
- New solver: current working tree `satsolver.py` / `satsolver_core.py`
- Timeout per solver per case: `60s`
- Wall clock: `215.4243s`

## Summary

| Metric | Old | New | Delta |
|---|---:|---:|---:|
| Correct / within timeout | 278/279 | 278/279 | +0 |
| Timeouts | 1 | 1 | +0 |
| Total measured time | 105.8651s | 105.4399s | -0.4251s |
| Improved valid cases |  | 139 |  |
| Regressed valid cases |  | 139 |  |

## Biggest Improvements

| Source | Old | New | Delta | Ratio |
|---|---:|---:|---:|---:|
| `large/test_6.cnf` | UNSAT 3.5722s | UNSAT 3.2607s | -0.3115s | 0.913x |
| `cnf_training_complex/complex_cnf_hard/planted3sat_balanced_n400_m1704_seed1.cnf` | SAT 3.4587s | SAT 3.3254s | -0.1333s | 0.961x |
| `special/hard.cnf` | UNSAT 2.6822s | UNSAT 2.5600s | -0.1222s | 0.954x |
| `large/test_10.cnf` | UNSAT 0.8803s | UNSAT 0.8136s | -0.0667s | 0.924x |
| `cnf_training_complex/complex_cnf_hard/ramsey_R3_4_n11_unsat.cnf` | UNSAT 1.1350s | UNSAT 1.0819s | -0.0531s | 0.953x |
| `cnf_training_complex/complex_cnf_moderate/xor_sparse_sat_n128_eq165_w3-4_seed3.cnf` | SAT 0.2720s | SAT 0.2353s | -0.0367s | 0.865x |
| `cnf_training_complex/complex_cnf_moderate/planted3sat_balanced_n200_m852_seed2.cnf` | SAT 0.9242s | SAT 0.8949s | -0.0293s | 0.968x |
| `cnf_training_complex/complex_cnf_hard/planted3sat_balanced_n260_m1108_seed2.cnf` | SAT 1.0582s | SAT 1.0328s | -0.0254s | 0.976x |
| `cnf_training_extra/extra_cnf/graphcolor_k3_planted_v12_e26_001.cnf` | SAT 0.0482s | SAT 0.0234s | -0.0248s | 0.486x |
| `cnf_training_extra/extra_cnf/exact_random3sat_sat_n10_m49_008.cnf` | SAT 0.0480s | SAT 0.0255s | -0.0225s | 0.532x |
| `cnf_training_extra/extra_cnf/graphcolor_k3_planted_v24_e53_004.cnf` | SAT 0.0448s | SAT 0.0251s | -0.0197s | 0.560x |
| `cnf_training_extra/extra_cnf/graphcolor_k3_complete_K6_unsat.cnf` | UNSAT 0.0428s | UNSAT 0.0235s | -0.0193s | 0.549x |
| `cnf_training_complex/complex_cnf_moderate/planted3sat_balanced_n120_m511_seed1.cnf` | SAT 0.0490s | SAT 0.0304s | -0.0185s | 0.622x |
| `cnf_training_extra/extra_cnf/planted3sat_n20_m85_001.cnf` | SAT 0.0404s | SAT 0.0219s | -0.0185s | 0.543x |
| `cnf_training_extra/extra_cnf/planted3sat_n30_m128_006.cnf` | SAT 0.0464s | SAT 0.0280s | -0.0184s | 0.603x |

## Biggest Regressions

| Source | Old | New | Delta | Ratio |
|---|---:|---:|---:|---:|
| `cnf_training_complex/complex_cnf_moderate/ramsey_R3_4_n10_unsat.cnf` | UNSAT 1.0398s | UNSAT 1.1283s | +0.0884s | 1.085x |
| `cnf_training_complex/complex_cnf_hard/planted3sat_balanced_n320_m1363_seed2.cnf` | SAT 0.5394s | SAT 0.6225s | +0.0831s | 1.154x |
| `cnf_training_complex/complex_cnf_moderate/ramsey_R3_4_n9_unsat.cnf` | UNSAT 1.0855s | UNSAT 1.1494s | +0.0639s | 1.059x |
| `cnf_training_complex/complex_cnf_hard/planted3sat_balanced_n260_m1108_seed1.cnf` | SAT 15.0616s | SAT 15.1047s | +0.0431s | 1.003x |
| `cnf_training_complex/complex_cnf_moderate/planted3sat_balanced_n200_m852_seed1.cnf` | SAT 0.4633s | SAT 0.4908s | +0.0275s | 1.059x |
| `satlib_subset/uuf100-010.cnf` | UNSAT 0.0666s | UNSAT 0.0921s | +0.0255s | 1.383x |
| `cnf_training_complex/complex_cnf_moderate/vdw_2color_k3_n9_unsat.cnf` | UNSAT 0.0264s | UNSAT 0.0505s | +0.0241s | 1.913x |
| `cnf_training_complex/complex_cnf_hard/planted3sat_balanced_n320_m1363_seed1.cnf` | SAT 0.7572s | SAT 0.7791s | +0.0220s | 1.029x |
| `cnf_training_extra/extra_cnf/exact_random3sat_unsat_n9_m44_001.cnf` | UNSAT 0.0230s | UNSAT 0.0431s | +0.0200s | 1.869x |
| `cnf_training_extra/extra_cnf/planted3sat_n80_m340_003.cnf` | SAT 0.0253s | SAT 0.0451s | +0.0198s | 1.784x |
| `small/test_2.cnf` | SAT 0.0227s | SAT 0.0418s | +0.0191s | 1.840x |
| `cnf_training_complex/complex_cnf_hard/xor_sparse_unsat_n100_eq135_w3-4_seed4.cnf` | UNSAT 0.0270s | UNSAT 0.0459s | +0.0190s | 1.703x |
| `cnf_training_complex/complex_cnf_moderate/ordering_no_minimum_n8.cnf` | UNSAT 0.0280s | UNSAT 0.0467s | +0.0187s | 1.668x |
| `cnf_training_extra/extra_cnf/planted3sat_n40_m170_002.cnf` | SAT 0.0248s | SAT 0.0431s | +0.0183s | 1.738x |
| `medium/test_4.cnf` | UNSAT 0.8321s | UNSAT 0.8496s | +0.0176s | 1.021x |

## All Cases

| Source | Vars | Clauses | Old Status | Old Time | New Status | New Time | Delta | Ratio | Old Valid | New Valid |
|---|---:|---:|---|---:|---|---:|---:|---:|---|---|
| `cnf_training_complex/complex_cnf_hard/mycielski_iter4_color5_unsat.cnf` | 235 | 1697 | TIMEOUT | 60.0000s | TIMEOUT | 60.0000s | +0.0000s | 1.000x | timeout > 60s | timeout > 60s |
| `cnf_training_complex/complex_cnf_hard/planted3sat_balanced_n260_m1108_seed1.cnf` | 260 | 1108 | SAT | 15.0616s | SAT | 15.1047s | +0.0431s | 1.003x | valid SAT | valid SAT |
| `cnf_training_complex/complex_cnf_hard/planted3sat_balanced_n260_m1108_seed2.cnf` | 260 | 1108 | SAT | 1.0582s | SAT | 1.0328s | -0.0254s | 0.976x | valid SAT | valid SAT |
| `cnf_training_complex/complex_cnf_hard/planted3sat_balanced_n320_m1363_seed1.cnf` | 320 | 1363 | SAT | 0.7572s | SAT | 0.7791s | +0.0220s | 1.029x | valid SAT | valid SAT |
| `cnf_training_complex/complex_cnf_hard/planted3sat_balanced_n320_m1363_seed2.cnf` | 320 | 1363 | SAT | 0.5394s | SAT | 0.6225s | +0.0831s | 1.154x | valid SAT | valid SAT |
| `cnf_training_complex/complex_cnf_hard/planted3sat_balanced_n400_m1704_seed1.cnf` | 400 | 1704 | SAT | 3.4587s | SAT | 3.3254s | -0.1333s | 0.961x | valid SAT | valid SAT |
| `cnf_training_complex/complex_cnf_hard/ramsey_R3_4_n11_unsat.cnf` | 55 | 495 | UNSAT | 1.1350s | UNSAT | 1.0819s | -0.0531s | 0.953x | valid UNSAT (format checked) | valid UNSAT (format checked) |
| `cnf_training_complex/complex_cnf_hard/tseitin_deg3_v100_sat.cnf` | 150 | 400 | SAT | 0.0438s | SAT | 0.0407s | -0.0031s | 0.929x | valid SAT | valid SAT |
| `cnf_training_complex/complex_cnf_hard/tseitin_deg3_v100_unsat.cnf` | 150 | 400 | UNSAT | 0.0292s | UNSAT | 0.0280s | -0.0012s | 0.959x | valid UNSAT (format checked) | valid UNSAT (format checked) |
| `cnf_training_complex/complex_cnf_hard/tseitin_deg3_v120_sat.cnf` | 180 | 480 | SAT | 0.0285s | SAT | 0.0304s | +0.0019s | 1.068x | valid SAT | valid SAT |
| `cnf_training_complex/complex_cnf_hard/tseitin_deg3_v120_unsat.cnf` | 180 | 480 | UNSAT | 0.0280s | UNSAT | 0.0315s | +0.0035s | 1.124x | valid UNSAT (format checked) | valid UNSAT (format checked) |
| `cnf_training_complex/complex_cnf_hard/tseitin_deg3_v160_sat.cnf` | 240 | 640 | SAT | 0.0408s | SAT | 0.0477s | +0.0069s | 1.170x | valid SAT | valid SAT |
| `cnf_training_complex/complex_cnf_hard/tseitin_deg3_v160_unsat.cnf` | 240 | 640 | UNSAT | 0.0329s | UNSAT | 0.0265s | -0.0065s | 0.804x | valid UNSAT (format checked) | valid UNSAT (format checked) |
| `cnf_training_complex/complex_cnf_hard/tseitin_deg4_v64_sat.cnf` | 128 | 512 | SAT | 0.0497s | SAT | 0.0440s | -0.0057s | 0.885x | valid SAT | valid SAT |
| `cnf_training_complex/complex_cnf_hard/tseitin_deg4_v64_unsat.cnf` | 128 | 512 | UNSAT | 0.0316s | UNSAT | 0.0230s | -0.0087s | 0.726x | valid UNSAT (format checked) | valid UNSAT (format checked) |
| `cnf_training_complex/complex_cnf_hard/tseitin_deg4_v96_sat.cnf` | 192 | 768 | SAT | 0.0329s | SAT | 0.0423s | +0.0094s | 1.284x | valid SAT | valid SAT |
| `cnf_training_complex/complex_cnf_hard/tseitin_deg4_v96_unsat.cnf` | 192 | 768 | UNSAT | 0.0436s | UNSAT | 0.0372s | -0.0065s | 0.852x | valid UNSAT (format checked) | valid UNSAT (format checked) |
| `cnf_training_complex/complex_cnf_hard/vdw_2color_k4_n45_unsat.cnf` | 45 | 630 | UNSAT | 0.0465s | UNSAT | 0.0503s | +0.0038s | 1.082x | valid UNSAT (format checked) | valid UNSAT (format checked) |
| `cnf_training_complex/complex_cnf_hard/vdw_2color_k4_n60_unsat.cnf` | 60 | 1140 | UNSAT | 0.0587s | UNSAT | 0.0741s | +0.0154s | 1.262x | valid UNSAT (format checked) | valid UNSAT (format checked) |
| `cnf_training_complex/complex_cnf_hard/xor_sparse_unsat_n100_eq135_w3-4_seed4.cnf` | 100 | 828 | UNSAT | 0.0270s | UNSAT | 0.0459s | +0.0190s | 1.703x | valid UNSAT (format checked) | valid UNSAT (format checked) |
| `cnf_training_complex/complex_cnf_hard/xor_sparse_unsat_n140_eq190_w3-4_seed5.cnf` | 140 | 1104 | UNSAT | 0.0486s | UNSAT | 0.0366s | -0.0120s | 0.752x | valid UNSAT (format checked) | valid UNSAT (format checked) |
| `cnf_training_complex/complex_cnf_hard/xor_sparse_unsat_n180_eq250_w3-4_seed6.cnf` | 180 | 1544 | UNSAT | 0.0317s | UNSAT | 0.0390s | +0.0072s | 1.228x | valid UNSAT (format checked) | valid UNSAT (format checked) |
| `cnf_training_complex/complex_cnf_moderate/mycielski_iter2_color3_unsat.cnf` | 33 | 104 | UNSAT | 0.0313s | UNSAT | 0.0411s | +0.0099s | 1.316x | valid UNSAT (format checked) | valid UNSAT (format checked) |
| `cnf_training_complex/complex_cnf_moderate/mycielski_iter2_color4_sat.cnf` | 44 | 157 | SAT | 0.0346s | SAT | 0.0356s | +0.0009s | 1.027x | valid SAT | valid SAT |
| `cnf_training_complex/complex_cnf_moderate/mycielski_iter3_color4_unsat.cnf` | 92 | 445 | UNSAT | 0.2374s | UNSAT | 0.2439s | +0.0066s | 1.028x | valid UNSAT (format checked) | valid UNSAT (format checked) |
| `cnf_training_complex/complex_cnf_moderate/mycielski_iter3_color5_sat.cnf` | 115 | 608 | SAT | 0.0236s | SAT | 0.0242s | +0.0006s | 1.024x | valid SAT | valid SAT |
| `cnf_training_complex/complex_cnf_moderate/ordering_no_minimum_n10.cnf` | 45 | 730 | UNSAT | 0.0519s | UNSAT | 0.0390s | -0.0129s | 0.751x | valid UNSAT (format checked) | valid UNSAT (format checked) |
| `cnf_training_complex/complex_cnf_moderate/ordering_no_minimum_n12.cnf` | 66 | 1332 | UNSAT | 0.0583s | UNSAT | 0.0691s | +0.0109s | 1.187x | valid UNSAT (format checked) | valid UNSAT (format checked) |
| `cnf_training_complex/complex_cnf_moderate/ordering_no_minimum_n8.cnf` | 28 | 344 | UNSAT | 0.0280s | UNSAT | 0.0467s | +0.0187s | 1.668x | valid UNSAT (format checked) | valid UNSAT (format checked) |
| `cnf_training_complex/complex_cnf_moderate/orthogonal_latin_squares_order3_sat.cnf` | 81 | 1998 | SAT | 0.0337s | SAT | 0.0372s | +0.0035s | 1.105x | valid SAT | valid SAT |
| `cnf_training_complex/complex_cnf_moderate/pigeonhole_php_11_into_10.cnf` | 110 | 1056 | UNSAT | 0.0475s | UNSAT | 0.0307s | -0.0169s | 0.645x | valid UNSAT (format checked) | valid UNSAT (format checked) |
| `cnf_training_complex/complex_cnf_moderate/pigeonhole_php_13_into_12.cnf` | 156 | 1807 | UNSAT | 0.0293s | UNSAT | 0.0286s | -0.0006s | 0.978x | valid UNSAT (format checked) | valid UNSAT (format checked) |
| `cnf_training_complex/complex_cnf_moderate/pigeonhole_php_9_into_8.cnf` | 72 | 549 | UNSAT | 0.0251s | UNSAT | 0.0258s | +0.0007s | 1.028x | valid UNSAT (format checked) | valid UNSAT (format checked) |
| `cnf_training_complex/complex_cnf_moderate/planted3sat_balanced_n120_m511_seed1.cnf` | 120 | 511 | SAT | 0.0490s | SAT | 0.0304s | -0.0185s | 0.622x | valid SAT | valid SAT |
| `cnf_training_complex/complex_cnf_moderate/planted3sat_balanced_n120_m511_seed2.cnf` | 120 | 511 | SAT | 0.0407s | SAT | 0.0470s | +0.0063s | 1.156x | valid SAT | valid SAT |
| `cnf_training_complex/complex_cnf_moderate/planted3sat_balanced_n160_m682_seed1.cnf` | 160 | 682 | SAT | 0.0505s | SAT | 0.0347s | -0.0157s | 0.688x | valid SAT | valid SAT |
| `cnf_training_complex/complex_cnf_moderate/planted3sat_balanced_n160_m682_seed2.cnf` | 160 | 682 | SAT | 0.0376s | SAT | 0.0521s | +0.0145s | 1.387x | valid SAT | valid SAT |
| `cnf_training_complex/complex_cnf_moderate/planted3sat_balanced_n200_m852_seed1.cnf` | 200 | 852 | SAT | 0.4633s | SAT | 0.4908s | +0.0275s | 1.059x | valid SAT | valid SAT |
| `cnf_training_complex/complex_cnf_moderate/planted3sat_balanced_n200_m852_seed2.cnf` | 200 | 852 | SAT | 0.9242s | SAT | 0.8949s | -0.0293s | 0.968x | valid SAT | valid SAT |
| `cnf_training_complex/complex_cnf_moderate/ramsey_R3_3_n6_unsat.cnf` | 15 | 40 | UNSAT | 0.0339s | UNSAT | 0.0270s | -0.0069s | 0.796x | valid UNSAT (brute-force checked) | valid UNSAT (brute-force checked) |
| `cnf_training_complex/complex_cnf_moderate/ramsey_R3_3_n7_unsat.cnf` | 21 | 70 | UNSAT | 0.0246s | UNSAT | 0.0331s | +0.0085s | 1.345x | valid UNSAT (format checked) | valid UNSAT (format checked) |
| `cnf_training_complex/complex_cnf_moderate/ramsey_R3_3_n8_unsat.cnf` | 28 | 112 | UNSAT | 0.0227s | UNSAT | 0.0392s | +0.0166s | 1.732x | valid UNSAT (format checked) | valid UNSAT (format checked) |
| `cnf_training_complex/complex_cnf_moderate/ramsey_R3_4_n10_unsat.cnf` | 45 | 330 | UNSAT | 1.0398s | UNSAT | 1.1283s | +0.0884s | 1.085x | valid UNSAT (format checked) | valid UNSAT (format checked) |
| `cnf_training_complex/complex_cnf_moderate/ramsey_R3_4_n9_unsat.cnf` | 36 | 210 | UNSAT | 1.0855s | UNSAT | 1.1494s | +0.0639s | 1.059x | valid UNSAT (format checked) | valid UNSAT (format checked) |
| `cnf_training_complex/complex_cnf_moderate/tseitin_deg3_v40_sat.cnf` | 60 | 160 | SAT | 0.0363s | SAT | 0.0284s | -0.0079s | 0.783x | valid SAT | valid SAT |
| `cnf_training_complex/complex_cnf_moderate/tseitin_deg3_v40_unsat.cnf` | 60 | 160 | UNSAT | 0.0291s | UNSAT | 0.0215s | -0.0077s | 0.737x | valid UNSAT (format checked) | valid UNSAT (format checked) |
| `cnf_training_complex/complex_cnf_moderate/tseitin_deg3_v60_sat.cnf` | 90 | 240 | SAT | 0.0245s | SAT | 0.0222s | -0.0023s | 0.906x | valid SAT | valid SAT |
| `cnf_training_complex/complex_cnf_moderate/tseitin_deg3_v60_unsat.cnf` | 90 | 240 | UNSAT | 0.0211s | UNSAT | 0.0218s | +0.0007s | 1.032x | valid UNSAT (format checked) | valid UNSAT (format checked) |
| `cnf_training_complex/complex_cnf_moderate/tseitin_deg3_v80_sat.cnf` | 120 | 320 | SAT | 0.0268s | SAT | 0.0433s | +0.0165s | 1.617x | valid SAT | valid SAT |
| `cnf_training_complex/complex_cnf_moderate/tseitin_deg3_v80_unsat.cnf` | 120 | 320 | UNSAT | 0.0271s | UNSAT | 0.0236s | -0.0035s | 0.871x | valid UNSAT (format checked) | valid UNSAT (format checked) |
| `cnf_training_complex/complex_cnf_moderate/vdw_2color_k3_n16_unsat.cnf` | 16 | 112 | UNSAT | 0.0376s | UNSAT | 0.0287s | -0.0089s | 0.764x | valid UNSAT (brute-force checked) | valid UNSAT (brute-force checked) |
| `cnf_training_complex/complex_cnf_moderate/vdw_2color_k3_n9_unsat.cnf` | 9 | 32 | UNSAT | 0.0264s | UNSAT | 0.0505s | +0.0241s | 1.913x | valid UNSAT (brute-force checked) | valid UNSAT (brute-force checked) |
| `cnf_training_complex/complex_cnf_moderate/vdw_2color_k4_n35_unsat.cnf` | 35 | 374 | UNSAT | 0.0465s | UNSAT | 0.0521s | +0.0056s | 1.119x | valid UNSAT (format checked) | valid UNSAT (format checked) |
| `cnf_training_complex/complex_cnf_moderate/xor_sparse_sat_n128_eq165_w3-4_seed3.cnf` | 128 | 1000 | SAT | 0.2720s | SAT | 0.2353s | -0.0367s | 0.865x | valid SAT | valid SAT |
| `cnf_training_complex/complex_cnf_moderate/xor_sparse_sat_n64_eq82_w3_seed1.cnf` | 64 | 328 | SAT | 0.0368s | SAT | 0.0268s | -0.0100s | 0.728x | valid SAT | valid SAT |
| `cnf_training_complex/complex_cnf_moderate/xor_sparse_sat_n96_eq125_w3_seed2.cnf` | 96 | 500 | SAT | 0.0401s | SAT | 0.0410s | +0.0009s | 1.024x | valid SAT | valid SAT |
| `cnf_training_complex/complex_cnf_moderate/xor_sparse_unsat_n48_eq62_w3_seed1.cnf` | 48 | 248 | UNSAT | 0.0279s | UNSAT | 0.0344s | +0.0065s | 1.233x | valid UNSAT (format checked) | valid UNSAT (format checked) |
| `cnf_training_complex/complex_cnf_moderate/xor_sparse_unsat_n64_eq86_w3_seed2.cnf` | 64 | 344 | UNSAT | 0.0227s | UNSAT | 0.0233s | +0.0006s | 1.027x | valid UNSAT (format checked) | valid UNSAT (format checked) |
| `cnf_training_complex/complex_cnf_moderate/xor_sparse_unsat_n80_eq108_w3-4_seed3.cnf` | 80 | 608 | UNSAT | 0.0367s | UNSAT | 0.0365s | -0.0002s | 0.995x | valid UNSAT (format checked) | valid UNSAT (format checked) |
| `cnf_training_complex/complex_cnf_stress/tseitin_deg3_v240_unsat.cnf` | 360 | 960 | UNSAT | 0.0419s | UNSAT | 0.0276s | -0.0144s | 0.658x | valid UNSAT (format checked) | valid UNSAT (format checked) |
| `cnf_training_complex/complex_cnf_stress/tseitin_deg4_v160_unsat.cnf` | 320 | 1280 | UNSAT | 0.0403s | UNSAT | 0.0326s | -0.0077s | 0.809x | valid UNSAT (format checked) | valid UNSAT (format checked) |
| `cnf_training_complex/complex_cnf_stress/xor_sparse_unsat_n240_eq330_w3-4_seed1.cnf` | 240 | 1996 | UNSAT | 0.0415s | UNSAT | 0.0458s | +0.0043s | 1.103x | valid UNSAT (format checked) | valid UNSAT (format checked) |
| `cnf_training_extra/extra_cnf/cardinality_exactly_one_sat_g10_s5_004.cnf` | 50 | 110 | SAT | 0.0363s | SAT | 0.0285s | -0.0079s | 0.784x | valid SAT | valid SAT |
| `cnf_training_extra/extra_cnf/cardinality_exactly_one_sat_g12_s6_005.cnf` | 72 | 192 | SAT | 0.0375s | SAT | 0.0421s | +0.0046s | 1.123x | valid SAT | valid SAT |
| `cnf_training_extra/extra_cnf/cardinality_exactly_one_sat_g16_s4_006.cnf` | 64 | 112 | SAT | 0.0405s | SAT | 0.0250s | -0.0155s | 0.618x | valid SAT | valid SAT |
| `cnf_training_extra/extra_cnf/cardinality_exactly_one_sat_g4_s4_001.cnf` | 16 | 28 | SAT | 0.0245s | SAT | 0.0362s | +0.0117s | 1.477x | valid SAT | valid SAT |
| `cnf_training_extra/extra_cnf/cardinality_exactly_one_sat_g5_s5_002.cnf` | 25 | 55 | SAT | 0.0385s | SAT | 0.0412s | +0.0027s | 1.071x | valid SAT | valid SAT |
| `cnf_training_extra/extra_cnf/cardinality_exactly_one_sat_g8_s4_003.cnf` | 32 | 56 | SAT | 0.0345s | SAT | 0.0315s | -0.0030s | 0.914x | valid SAT | valid SAT |
| `cnf_training_extra/extra_cnf/cardinality_exactly_one_unsat_g10_s6_005.cnf` | 60 | 162 | UNSAT | 0.0341s | UNSAT | 0.0321s | -0.0020s | 0.942x | valid UNSAT (format checked) | valid UNSAT (format checked) |
| `cnf_training_extra/extra_cnf/cardinality_exactly_one_unsat_g12_s4_006.cnf` | 48 | 86 | UNSAT | 0.0239s | UNSAT | 0.0282s | +0.0043s | 1.180x | valid UNSAT (format checked) | valid UNSAT (format checked) |
| `cnf_training_extra/extra_cnf/cardinality_exactly_one_unsat_g3_s4_001.cnf` | 12 | 23 | UNSAT | 0.0460s | UNSAT | 0.0301s | -0.0159s | 0.654x | valid UNSAT (brute-force checked) | valid UNSAT (brute-force checked) |
| `cnf_training_extra/extra_cnf/cardinality_exactly_one_unsat_g4_s5_002.cnf` | 20 | 46 | UNSAT | 0.0325s | UNSAT | 0.0231s | -0.0094s | 0.710x | valid UNSAT (format checked) | valid UNSAT (format checked) |
| `cnf_training_extra/extra_cnf/cardinality_exactly_one_unsat_g6_s4_003.cnf` | 24 | 44 | UNSAT | 0.0230s | UNSAT | 0.0276s | +0.0046s | 1.200x | valid UNSAT (format checked) | valid UNSAT (format checked) |
| `cnf_training_extra/extra_cnf/cardinality_exactly_one_unsat_g8_s5_004.cnf` | 40 | 90 | UNSAT | 0.0241s | UNSAT | 0.0317s | +0.0077s | 1.318x | valid UNSAT (format checked) | valid UNSAT (format checked) |
| `cnf_training_extra/extra_cnf/equivalence_chain_len10_sat.cnf` | 10 | 20 | SAT | 0.0420s | SAT | 0.0279s | -0.0141s | 0.665x | valid SAT | valid SAT |
| `cnf_training_extra/extra_cnf/equivalence_chain_len10_unsat.cnf` | 10 | 20 | UNSAT | 0.0411s | UNSAT | 0.0232s | -0.0179s | 0.565x | valid UNSAT (brute-force checked) | valid UNSAT (brute-force checked) |
| `cnf_training_extra/extra_cnf/equivalence_chain_len120_sat.cnf` | 120 | 240 | SAT | 0.0382s | SAT | 0.0346s | -0.0036s | 0.905x | valid SAT | valid SAT |
| `cnf_training_extra/extra_cnf/equivalence_chain_len120_unsat.cnf` | 120 | 240 | UNSAT | 0.0247s | UNSAT | 0.0304s | +0.0058s | 1.234x | valid UNSAT (format checked) | valid UNSAT (format checked) |
| `cnf_training_extra/extra_cnf/equivalence_chain_len20_sat.cnf` | 20 | 40 | SAT | 0.0365s | SAT | 0.0250s | -0.0115s | 0.685x | valid SAT | valid SAT |
| `cnf_training_extra/extra_cnf/equivalence_chain_len20_unsat.cnf` | 20 | 40 | UNSAT | 0.0347s | UNSAT | 0.0346s | -0.0001s | 0.998x | valid UNSAT (format checked) | valid UNSAT (format checked) |
| `cnf_training_extra/extra_cnf/equivalence_chain_len40_sat.cnf` | 40 | 80 | SAT | 0.0385s | SAT | 0.0355s | -0.0030s | 0.922x | valid SAT | valid SAT |
| `cnf_training_extra/extra_cnf/equivalence_chain_len40_unsat.cnf` | 40 | 80 | UNSAT | 0.0299s | UNSAT | 0.0344s | +0.0045s | 1.151x | valid UNSAT (format checked) | valid UNSAT (format checked) |
| `cnf_training_extra/extra_cnf/equivalence_chain_len80_sat.cnf` | 80 | 160 | SAT | 0.0427s | SAT | 0.0328s | -0.0099s | 0.768x | valid SAT | valid SAT |
| `cnf_training_extra/extra_cnf/equivalence_chain_len80_unsat.cnf` | 80 | 160 | UNSAT | 0.0313s | UNSAT | 0.0264s | -0.0049s | 0.842x | valid UNSAT (format checked) | valid UNSAT (format checked) |
| `cnf_training_extra/extra_cnf/exact_random3sat_sat_n10_m49_008.cnf` | 10 | 49 | SAT | 0.0480s | SAT | 0.0255s | -0.0225s | 0.532x | valid SAT | valid SAT |
| `cnf_training_extra/extra_cnf/exact_random3sat_sat_n11_m40_017.cnf` | 11 | 40 | SAT | 0.0257s | SAT | 0.0371s | +0.0114s | 1.443x | valid SAT | valid SAT |
| `cnf_training_extra/extra_cnf/exact_random3sat_sat_n11_m46_001.cnf` | 11 | 46 | SAT | 0.0286s | SAT | 0.0223s | -0.0063s | 0.781x | valid SAT | valid SAT |
| `cnf_training_extra/extra_cnf/exact_random3sat_sat_n12_m43_012.cnf` | 12 | 43 | SAT | 0.0396s | SAT | 0.0452s | +0.0056s | 1.140x | valid SAT | valid SAT |
| `cnf_training_extra/extra_cnf/exact_random3sat_sat_n12_m47_006.cnf` | 12 | 47 | SAT | 0.0316s | SAT | 0.0394s | +0.0078s | 1.246x | valid SAT | valid SAT |
| `cnf_training_extra/extra_cnf/exact_random3sat_sat_n12_m47_013.cnf` | 12 | 47 | SAT | 0.0300s | SAT | 0.0373s | +0.0073s | 1.242x | valid SAT | valid SAT |
| `cnf_training_extra/extra_cnf/exact_random3sat_sat_n13_m47_011.cnf` | 13 | 47 | SAT | 0.0487s | SAT | 0.0311s | -0.0176s | 0.639x | valid SAT | valid SAT |
| `cnf_training_extra/extra_cnf/exact_random3sat_sat_n13_m64_004.cnf` | 13 | 64 | SAT | 0.0335s | SAT | 0.0391s | +0.0056s | 1.167x | valid SAT | valid SAT |
| `cnf_training_extra/extra_cnf/exact_random3sat_sat_n14_m50_015.cnf` | 14 | 50 | SAT | 0.0335s | SAT | 0.0319s | -0.0017s | 0.950x | valid SAT | valid SAT |
| `cnf_training_extra/extra_cnf/exact_random3sat_sat_n15_m68_014.cnf` | 15 | 68 | SAT | 0.0414s | SAT | 0.0358s | -0.0056s | 0.864x | valid SAT | valid SAT |
| `cnf_training_extra/extra_cnf/exact_random3sat_sat_n16_m62_016.cnf` | 16 | 62 | SAT | 0.0243s | SAT | 0.0372s | +0.0129s | 1.528x | valid SAT | valid SAT |
| `cnf_training_extra/extra_cnf/exact_random3sat_sat_n16_m72_003.cnf` | 16 | 72 | SAT | 0.0463s | SAT | 0.0343s | -0.0119s | 0.742x | valid SAT | valid SAT |
| `cnf_training_extra/extra_cnf/exact_random3sat_sat_n8_m31_007.cnf` | 8 | 31 | SAT | 0.0263s | SAT | 0.0268s | +0.0005s | 1.021x | valid SAT | valid SAT |
| `cnf_training_extra/extra_cnf/exact_random3sat_sat_n8_m31_009.cnf` | 8 | 31 | SAT | 0.0241s | SAT | 0.0259s | +0.0018s | 1.076x | valid SAT | valid SAT |
| `cnf_training_extra/extra_cnf/exact_random3sat_sat_n8_m36_002.cnf` | 8 | 36 | SAT | 0.0258s | SAT | 0.0307s | +0.0049s | 1.189x | valid SAT | valid SAT |
| `cnf_training_extra/extra_cnf/exact_random3sat_sat_n8_m36_005.cnf` | 8 | 36 | SAT | 0.0225s | SAT | 0.0346s | +0.0121s | 1.541x | valid SAT | valid SAT |
| `cnf_training_extra/extra_cnf/exact_random3sat_sat_n9_m32_018.cnf` | 9 | 32 | SAT | 0.0421s | SAT | 0.0237s | -0.0184s | 0.563x | valid SAT | valid SAT |
| `cnf_training_extra/extra_cnf/exact_random3sat_sat_n9_m38_010.cnf` | 9 | 38 | SAT | 0.0240s | SAT | 0.0338s | +0.0098s | 1.408x | valid SAT | valid SAT |
| `cnf_training_extra/extra_cnf/exact_random3sat_unsat_n10_m49_015.cnf` | 10 | 49 | UNSAT | 0.0311s | UNSAT | 0.0284s | -0.0027s | 0.912x | valid UNSAT (brute-force checked) | valid UNSAT (brute-force checked) |
| `cnf_training_extra/extra_cnf/exact_random3sat_unsat_n11_m54_012.cnf` | 11 | 54 | UNSAT | 0.0232s | UNSAT | 0.0250s | +0.0018s | 1.077x | valid UNSAT (brute-force checked) | valid UNSAT (brute-force checked) |
| `cnf_training_extra/extra_cnf/exact_random3sat_unsat_n12_m64_007.cnf` | 12 | 64 | UNSAT | 0.0337s | UNSAT | 0.0383s | +0.0045s | 1.134x | valid UNSAT (brute-force checked) | valid UNSAT (brute-force checked) |
| `cnf_training_extra/extra_cnf/exact_random3sat_unsat_n12_m64_013.cnf` | 12 | 64 | UNSAT | 0.0261s | UNSAT | 0.0235s | -0.0026s | 0.900x | valid UNSAT (brute-force checked) | valid UNSAT (brute-force checked) |
| `cnf_training_extra/extra_cnf/exact_random3sat_unsat_n13_m69_006.cnf` | 13 | 69 | UNSAT | 0.0325s | UNSAT | 0.0337s | +0.0013s | 1.039x | valid UNSAT (brute-force checked) | valid UNSAT (brute-force checked) |
| `cnf_training_extra/extra_cnf/exact_random3sat_unsat_n13_m69_010.cnf` | 13 | 69 | UNSAT | 0.0345s | UNSAT | 0.0324s | -0.0022s | 0.937x | valid UNSAT (brute-force checked) | valid UNSAT (brute-force checked) |
| `cnf_training_extra/extra_cnf/exact_random3sat_unsat_n14_m74_017.cnf` | 14 | 74 | UNSAT | 0.0344s | UNSAT | 0.0218s | -0.0126s | 0.633x | valid UNSAT (brute-force checked) | valid UNSAT (brute-force checked) |
| `cnf_training_extra/extra_cnf/exact_random3sat_unsat_n15_m68_011.cnf` | 15 | 68 | UNSAT | 0.0230s | UNSAT | 0.0335s | +0.0105s | 1.456x | valid UNSAT (brute-force checked) | valid UNSAT (brute-force checked) |
| `cnf_training_extra/extra_cnf/exact_random3sat_unsat_n15_m68_018.cnf` | 15 | 68 | UNSAT | 0.0378s | UNSAT | 0.0331s | -0.0047s | 0.876x | valid UNSAT (brute-force checked) | valid UNSAT (brute-force checked) |
| `cnf_training_extra/extra_cnf/exact_random3sat_unsat_n15_m80_014.cnf` | 15 | 80 | UNSAT | 0.0261s | UNSAT | 0.0332s | +0.0072s | 1.275x | valid UNSAT (brute-force checked) | valid UNSAT (brute-force checked) |
| `cnf_training_extra/extra_cnf/exact_random3sat_unsat_n16_m78_005.cnf` | 16 | 78 | UNSAT | 0.0320s | UNSAT | 0.0493s | +0.0172s | 1.539x | valid UNSAT (brute-force checked) | valid UNSAT (brute-force checked) |
| `cnf_training_extra/extra_cnf/exact_random3sat_unsat_n16_m78_008.cnf` | 16 | 78 | UNSAT | 0.0250s | UNSAT | 0.0316s | +0.0066s | 1.264x | valid UNSAT (brute-force checked) | valid UNSAT (brute-force checked) |
| `cnf_training_extra/extra_cnf/exact_random3sat_unsat_n16_m85_002.cnf` | 16 | 85 | UNSAT | 0.0246s | UNSAT | 0.0388s | +0.0143s | 1.581x | valid UNSAT (brute-force checked) | valid UNSAT (brute-force checked) |
| `cnf_training_extra/extra_cnf/exact_random3sat_unsat_n16_m85_003.cnf` | 16 | 85 | UNSAT | 0.0233s | UNSAT | 0.0318s | +0.0086s | 1.369x | valid UNSAT (brute-force checked) | valid UNSAT (brute-force checked) |
| `cnf_training_extra/extra_cnf/exact_random3sat_unsat_n8_m31_016.cnf` | 8 | 31 | UNSAT | 0.0375s | UNSAT | 0.0324s | -0.0051s | 0.865x | valid UNSAT (brute-force checked) | valid UNSAT (brute-force checked) |
| `cnf_training_extra/extra_cnf/exact_random3sat_unsat_n8_m34_009.cnf` | 8 | 34 | UNSAT | 0.0222s | UNSAT | 0.0330s | +0.0108s | 1.484x | valid UNSAT (brute-force checked) | valid UNSAT (brute-force checked) |
| `cnf_training_extra/extra_cnf/exact_random3sat_unsat_n9_m38_004.cnf` | 9 | 38 | UNSAT | 0.0260s | UNSAT | 0.0333s | +0.0073s | 1.282x | valid UNSAT (brute-force checked) | valid UNSAT (brute-force checked) |
| `cnf_training_extra/extra_cnf/exact_random3sat_unsat_n9_m44_001.cnf` | 9 | 44 | UNSAT | 0.0230s | UNSAT | 0.0431s | +0.0200s | 1.869x | valid UNSAT (brute-force checked) | valid UNSAT (brute-force checked) |
| `cnf_training_extra/extra_cnf/graphcolor_k3_complete_K4_unsat.cnf` | 12 | 34 | UNSAT | 0.0213s | UNSAT | 0.0211s | -0.0001s | 0.994x | valid UNSAT (brute-force checked) | valid UNSAT (brute-force checked) |
| `cnf_training_extra/extra_cnf/graphcolor_k3_complete_K5_unsat.cnf` | 15 | 50 | UNSAT | 0.0214s | UNSAT | 0.0216s | +0.0002s | 1.010x | valid UNSAT (brute-force checked) | valid UNSAT (brute-force checked) |
| `cnf_training_extra/extra_cnf/graphcolor_k3_complete_K6_unsat.cnf` | 18 | 69 | UNSAT | 0.0428s | UNSAT | 0.0235s | -0.0193s | 0.549x | valid UNSAT (format checked) | valid UNSAT (format checked) |
| `cnf_training_extra/extra_cnf/graphcolor_k3_planted_v12_e26_001.cnf` | 36 | 126 | SAT | 0.0482s | SAT | 0.0234s | -0.0248s | 0.486x | valid SAT | valid SAT |
| `cnf_training_extra/extra_cnf/graphcolor_k3_planted_v16_e35_002.cnf` | 48 | 169 | SAT | 0.0405s | SAT | 0.0284s | -0.0121s | 0.701x | valid SAT | valid SAT |
| `cnf_training_extra/extra_cnf/graphcolor_k3_planted_v20_e44_003.cnf` | 60 | 212 | SAT | 0.0242s | SAT | 0.0236s | -0.0006s | 0.975x | valid SAT | valid SAT |
| `cnf_training_extra/extra_cnf/graphcolor_k3_planted_v24_e53_004.cnf` | 72 | 255 | SAT | 0.0448s | SAT | 0.0251s | -0.0197s | 0.560x | valid SAT | valid SAT |
| `cnf_training_extra/extra_cnf/graphcolor_k3_planted_v30_e66_005.cnf` | 90 | 318 | SAT | 0.0328s | SAT | 0.0359s | +0.0031s | 1.094x | valid SAT | valid SAT |
| `cnf_training_extra/extra_cnf/graphcolor_k3_planted_v36_e79_006.cnf` | 108 | 381 | SAT | 0.0253s | SAT | 0.0404s | +0.0151s | 1.596x | valid SAT | valid SAT |
| `cnf_training_extra/extra_cnf/graphcolor_k3_planted_v42_e92_007.cnf` | 126 | 444 | SAT | 0.0268s | SAT | 0.0262s | -0.0005s | 0.980x | valid SAT | valid SAT |
| `cnf_training_extra/extra_cnf/graphcolor_k3_planted_v50_e110_008.cnf` | 150 | 530 | SAT | 0.0247s | SAT | 0.0243s | -0.0003s | 0.987x | valid SAT | valid SAT |
| `cnf_training_extra/extra_cnf/graphcolor_k3_planted_v60_e132_009.cnf` | 180 | 636 | SAT | 0.0365s | SAT | 0.0292s | -0.0073s | 0.800x | valid SAT | valid SAT |
| `cnf_training_extra/extra_cnf/graphcolor_k3_planted_v72_e158_010.cnf` | 216 | 762 | SAT | 0.0367s | SAT | 0.0392s | +0.0025s | 1.067x | valid SAT | valid SAT |
| `cnf_training_extra/extra_cnf/horn_chain_len12_sat.cnf` | 12 | 12 | SAT | 0.0308s | SAT | 0.0447s | +0.0138s | 1.449x | valid SAT | valid SAT |
| `cnf_training_extra/extra_cnf/horn_chain_len12_unsat.cnf` | 12 | 13 | UNSAT | 0.0305s | UNSAT | 0.0362s | +0.0057s | 1.186x | valid UNSAT (brute-force checked) | valid UNSAT (brute-force checked) |
| `cnf_training_extra/extra_cnf/horn_chain_len16_sat.cnf` | 16 | 16 | SAT | 0.0231s | SAT | 0.0226s | -0.0006s | 0.976x | valid SAT | valid SAT |
| `cnf_training_extra/extra_cnf/horn_chain_len16_unsat.cnf` | 16 | 17 | UNSAT | 0.0309s | UNSAT | 0.0350s | +0.0041s | 1.132x | valid UNSAT (brute-force checked) | valid UNSAT (brute-force checked) |
| `cnf_training_extra/extra_cnf/horn_chain_len24_sat.cnf` | 24 | 24 | SAT | 0.0441s | SAT | 0.0377s | -0.0064s | 0.854x | valid SAT | valid SAT |
| `cnf_training_extra/extra_cnf/horn_chain_len24_unsat.cnf` | 24 | 25 | UNSAT | 0.0229s | UNSAT | 0.0306s | +0.0077s | 1.337x | valid UNSAT (format checked) | valid UNSAT (format checked) |
| `cnf_training_extra/extra_cnf/horn_chain_len32_sat.cnf` | 32 | 32 | SAT | 0.0489s | SAT | 0.0321s | -0.0168s | 0.657x | valid SAT | valid SAT |
| `cnf_training_extra/extra_cnf/horn_chain_len32_unsat.cnf` | 32 | 33 | UNSAT | 0.0315s | UNSAT | 0.0244s | -0.0071s | 0.775x | valid UNSAT (format checked) | valid UNSAT (format checked) |
| `cnf_training_extra/extra_cnf/horn_chain_len48_sat.cnf` | 48 | 48 | SAT | 0.0486s | SAT | 0.0471s | -0.0015s | 0.969x | valid SAT | valid SAT |
| `cnf_training_extra/extra_cnf/horn_chain_len48_unsat.cnf` | 48 | 49 | UNSAT | 0.0257s | UNSAT | 0.0231s | -0.0025s | 0.901x | valid UNSAT (format checked) | valid UNSAT (format checked) |
| `cnf_training_extra/extra_cnf/horn_chain_len64_sat.cnf` | 64 | 64 | SAT | 0.0285s | SAT | 0.0395s | +0.0109s | 1.383x | valid SAT | valid SAT |
| `cnf_training_extra/extra_cnf/horn_chain_len64_unsat.cnf` | 64 | 65 | UNSAT | 0.0261s | UNSAT | 0.0236s | -0.0025s | 0.904x | valid UNSAT (format checked) | valid UNSAT (format checked) |
| `cnf_training_extra/extra_cnf/horn_chain_len8_sat.cnf` | 8 | 8 | SAT | 0.0265s | SAT | 0.0221s | -0.0044s | 0.835x | valid SAT | valid SAT |
| `cnf_training_extra/extra_cnf/horn_chain_len8_unsat.cnf` | 8 | 9 | UNSAT | 0.0229s | UNSAT | 0.0227s | -0.0002s | 0.991x | valid UNSAT (brute-force checked) | valid UNSAT (brute-force checked) |
| `cnf_training_extra/extra_cnf/nqueens_2x2_unsat.cnf` | 4 | 8 | UNSAT | 0.0245s | UNSAT | 0.0368s | +0.0123s | 1.500x | valid UNSAT (brute-force checked) | valid UNSAT (brute-force checked) |
| `cnf_training_extra/extra_cnf/nqueens_3x3_unsat.cnf` | 9 | 31 | UNSAT | 0.0361s | UNSAT | 0.0282s | -0.0079s | 0.780x | valid UNSAT (brute-force checked) | valid UNSAT (brute-force checked) |
| `cnf_training_extra/extra_cnf/nqueens_4x4_sat.cnf` | 16 | 80 | SAT | 0.0262s | SAT | 0.0216s | -0.0045s | 0.827x | valid SAT | valid SAT |
| `cnf_training_extra/extra_cnf/nqueens_5x5_sat.cnf` | 25 | 165 | SAT | 0.0315s | SAT | 0.0255s | -0.0060s | 0.810x | valid SAT | valid SAT |
| `cnf_training_extra/extra_cnf/nqueens_6x6_sat.cnf` | 36 | 296 | SAT | 0.0305s | SAT | 0.0220s | -0.0086s | 0.720x | valid SAT | valid SAT |
| `cnf_training_extra/extra_cnf/nqueens_7x7_sat.cnf` | 49 | 483 | SAT | 0.0403s | SAT | 0.0246s | -0.0156s | 0.612x | valid SAT | valid SAT |
| `cnf_training_extra/extra_cnf/nqueens_8x8_sat.cnf` | 64 | 736 | SAT | 0.0309s | SAT | 0.0282s | -0.0027s | 0.911x | valid SAT | valid SAT |
| `cnf_training_extra/extra_cnf/nqueens_9x9_sat.cnf` | 81 | 1065 | SAT | 0.0392s | SAT | 0.0286s | -0.0107s | 0.728x | valid SAT | valid SAT |
| `cnf_training_extra/extra_cnf/pigeonhole_php_10_into_9.cnf` | 90 | 415 | UNSAT | 0.0288s | UNSAT | 0.0264s | -0.0024s | 0.915x | valid UNSAT (format checked) | valid UNSAT (format checked) |
| `cnf_training_extra/extra_cnf/pigeonhole_php_4_into_3.cnf` | 12 | 22 | UNSAT | 0.0264s | UNSAT | 0.0284s | +0.0021s | 1.079x | valid UNSAT (brute-force checked) | valid UNSAT (brute-force checked) |
| `cnf_training_extra/extra_cnf/pigeonhole_php_5_into_4.cnf` | 20 | 45 | UNSAT | 0.0224s | UNSAT | 0.0244s | +0.0019s | 1.087x | valid UNSAT (format checked) | valid UNSAT (format checked) |
| `cnf_training_extra/extra_cnf/pigeonhole_php_6_into_5.cnf` | 30 | 81 | UNSAT | 0.0367s | UNSAT | 0.0305s | -0.0062s | 0.832x | valid UNSAT (format checked) | valid UNSAT (format checked) |
| `cnf_training_extra/extra_cnf/pigeonhole_php_7_into_6.cnf` | 42 | 133 | UNSAT | 0.0218s | UNSAT | 0.0328s | +0.0111s | 1.507x | valid UNSAT (format checked) | valid UNSAT (format checked) |
| `cnf_training_extra/extra_cnf/pigeonhole_php_8_into_7.cnf` | 56 | 204 | UNSAT | 0.0311s | UNSAT | 0.0206s | -0.0105s | 0.663x | valid UNSAT (format checked) | valid UNSAT (format checked) |
| `cnf_training_extra/extra_cnf/pigeonhole_php_9_into_8.cnf` | 72 | 297 | UNSAT | 0.0209s | UNSAT | 0.0220s | +0.0010s | 1.050x | valid UNSAT (format checked) | valid UNSAT (format checked) |
| `cnf_training_extra/extra_cnf/planted3sat_n20_m85_001.cnf` | 20 | 85 | SAT | 0.0404s | SAT | 0.0219s | -0.0185s | 0.543x | valid SAT | valid SAT |
| `cnf_training_extra/extra_cnf/planted3sat_n20_m85_002.cnf` | 20 | 85 | SAT | 0.0353s | SAT | 0.0341s | -0.0012s | 0.965x | valid SAT | valid SAT |
| `cnf_training_extra/extra_cnf/planted3sat_n20_m85_003.cnf` | 20 | 85 | SAT | 0.0304s | SAT | 0.0349s | +0.0045s | 1.149x | valid SAT | valid SAT |
| `cnf_training_extra/extra_cnf/planted3sat_n20_m85_004.cnf` | 20 | 85 | SAT | 0.0226s | SAT | 0.0237s | +0.0012s | 1.052x | valid SAT | valid SAT |
| `cnf_training_extra/extra_cnf/planted3sat_n20_m85_005.cnf` | 20 | 85 | SAT | 0.0267s | SAT | 0.0381s | +0.0114s | 1.424x | valid SAT | valid SAT |
| `cnf_training_extra/extra_cnf/planted3sat_n20_m85_006.cnf` | 20 | 85 | SAT | 0.0337s | SAT | 0.0231s | -0.0106s | 0.685x | valid SAT | valid SAT |
| `cnf_training_extra/extra_cnf/planted3sat_n20_m85_007.cnf` | 20 | 85 | SAT | 0.0444s | SAT | 0.0321s | -0.0123s | 0.723x | valid SAT | valid SAT |
| `cnf_training_extra/extra_cnf/planted3sat_n20_m85_008.cnf` | 20 | 85 | SAT | 0.0235s | SAT | 0.0246s | +0.0011s | 1.047x | valid SAT | valid SAT |
| `cnf_training_extra/extra_cnf/planted3sat_n20_m85_009.cnf` | 20 | 85 | SAT | 0.0264s | SAT | 0.0229s | -0.0035s | 0.866x | valid SAT | valid SAT |
| `cnf_training_extra/extra_cnf/planted3sat_n20_m85_010.cnf` | 20 | 85 | SAT | 0.0327s | SAT | 0.0404s | +0.0077s | 1.235x | valid SAT | valid SAT |
| `cnf_training_extra/extra_cnf/planted3sat_n30_m128_001.cnf` | 30 | 128 | SAT | 0.0259s | SAT | 0.0367s | +0.0108s | 1.417x | valid SAT | valid SAT |
| `cnf_training_extra/extra_cnf/planted3sat_n30_m128_002.cnf` | 30 | 128 | SAT | 0.0255s | SAT | 0.0227s | -0.0027s | 0.893x | valid SAT | valid SAT |
| `cnf_training_extra/extra_cnf/planted3sat_n30_m128_003.cnf` | 30 | 128 | SAT | 0.0276s | SAT | 0.0220s | -0.0056s | 0.797x | valid SAT | valid SAT |
| `cnf_training_extra/extra_cnf/planted3sat_n30_m128_004.cnf` | 30 | 128 | SAT | 0.0229s | SAT | 0.0357s | +0.0128s | 1.560x | valid SAT | valid SAT |
| `cnf_training_extra/extra_cnf/planted3sat_n30_m128_005.cnf` | 30 | 128 | SAT | 0.0315s | SAT | 0.0296s | -0.0019s | 0.941x | valid SAT | valid SAT |
| `cnf_training_extra/extra_cnf/planted3sat_n30_m128_006.cnf` | 30 | 128 | SAT | 0.0464s | SAT | 0.0280s | -0.0184s | 0.603x | valid SAT | valid SAT |
| `cnf_training_extra/extra_cnf/planted3sat_n30_m128_007.cnf` | 30 | 128 | SAT | 0.0304s | SAT | 0.0219s | -0.0085s | 0.719x | valid SAT | valid SAT |
| `cnf_training_extra/extra_cnf/planted3sat_n30_m128_008.cnf` | 30 | 128 | SAT | 0.0361s | SAT | 0.0235s | -0.0127s | 0.649x | valid SAT | valid SAT |
| `cnf_training_extra/extra_cnf/planted3sat_n30_m128_009.cnf` | 30 | 128 | SAT | 0.0257s | SAT | 0.0388s | +0.0131s | 1.509x | valid SAT | valid SAT |
| `cnf_training_extra/extra_cnf/planted3sat_n30_m128_010.cnf` | 30 | 128 | SAT | 0.0222s | SAT | 0.0228s | +0.0006s | 1.025x | valid SAT | valid SAT |
| `cnf_training_extra/extra_cnf/planted3sat_n40_m170_001.cnf` | 40 | 170 | SAT | 0.0250s | SAT | 0.0365s | +0.0116s | 1.463x | valid SAT | valid SAT |
| `cnf_training_extra/extra_cnf/planted3sat_n40_m170_002.cnf` | 40 | 170 | SAT | 0.0248s | SAT | 0.0431s | +0.0183s | 1.738x | valid SAT | valid SAT |
| `cnf_training_extra/extra_cnf/planted3sat_n40_m170_003.cnf` | 40 | 170 | SAT | 0.0247s | SAT | 0.0338s | +0.0091s | 1.367x | valid SAT | valid SAT |
| `cnf_training_extra/extra_cnf/planted3sat_n40_m170_004.cnf` | 40 | 170 | SAT | 0.0264s | SAT | 0.0254s | -0.0009s | 0.964x | valid SAT | valid SAT |
| `cnf_training_extra/extra_cnf/planted3sat_n40_m170_005.cnf` | 40 | 170 | SAT | 0.0246s | SAT | 0.0365s | +0.0120s | 1.487x | valid SAT | valid SAT |
| `cnf_training_extra/extra_cnf/planted3sat_n40_m170_006.cnf` | 40 | 170 | SAT | 0.0339s | SAT | 0.0251s | -0.0088s | 0.741x | valid SAT | valid SAT |
| `cnf_training_extra/extra_cnf/planted3sat_n40_m170_007.cnf` | 40 | 170 | SAT | 0.0247s | SAT | 0.0263s | +0.0015s | 1.063x | valid SAT | valid SAT |
| `cnf_training_extra/extra_cnf/planted3sat_n40_m170_008.cnf` | 40 | 170 | SAT | 0.0256s | SAT | 0.0260s | +0.0004s | 1.014x | valid SAT | valid SAT |
| `cnf_training_extra/extra_cnf/planted3sat_n40_m170_009.cnf` | 40 | 170 | SAT | 0.0239s | SAT | 0.0366s | +0.0127s | 1.531x | valid SAT | valid SAT |
| `cnf_training_extra/extra_cnf/planted3sat_n40_m170_010.cnf` | 40 | 170 | SAT | 0.0216s | SAT | 0.0377s | +0.0161s | 1.745x | valid SAT | valid SAT |
| `cnf_training_extra/extra_cnf/planted3sat_n60_m255_001.cnf` | 60 | 255 | SAT | 0.0308s | SAT | 0.0243s | -0.0065s | 0.789x | valid SAT | valid SAT |
| `cnf_training_extra/extra_cnf/planted3sat_n60_m255_002.cnf` | 60 | 255 | SAT | 0.0252s | SAT | 0.0273s | +0.0020s | 1.081x | valid SAT | valid SAT |
| `cnf_training_extra/extra_cnf/planted3sat_n60_m255_003.cnf` | 60 | 255 | SAT | 0.0253s | SAT | 0.0250s | -0.0003s | 0.988x | valid SAT | valid SAT |
| `cnf_training_extra/extra_cnf/planted3sat_n60_m255_004.cnf` | 60 | 255 | SAT | 0.0361s | SAT | 0.0244s | -0.0117s | 0.677x | valid SAT | valid SAT |
| `cnf_training_extra/extra_cnf/planted3sat_n60_m255_005.cnf` | 60 | 255 | SAT | 0.0395s | SAT | 0.0339s | -0.0056s | 0.858x | valid SAT | valid SAT |
| `cnf_training_extra/extra_cnf/planted3sat_n60_m255_006.cnf` | 60 | 255 | SAT | 0.0261s | SAT | 0.0270s | +0.0009s | 1.036x | valid SAT | valid SAT |
| `cnf_training_extra/extra_cnf/planted3sat_n60_m255_007.cnf` | 60 | 255 | SAT | 0.0350s | SAT | 0.0413s | +0.0064s | 1.182x | valid SAT | valid SAT |
| `cnf_training_extra/extra_cnf/planted3sat_n60_m255_008.cnf` | 60 | 255 | SAT | 0.0390s | SAT | 0.0323s | -0.0066s | 0.830x | valid SAT | valid SAT |
| `cnf_training_extra/extra_cnf/planted3sat_n80_m340_001.cnf` | 80 | 340 | SAT | 0.0425s | SAT | 0.0309s | -0.0116s | 0.728x | valid SAT | valid SAT |
| `cnf_training_extra/extra_cnf/planted3sat_n80_m340_002.cnf` | 80 | 340 | SAT | 0.0403s | SAT | 0.0287s | -0.0117s | 0.710x | valid SAT | valid SAT |
| `cnf_training_extra/extra_cnf/planted3sat_n80_m340_003.cnf` | 80 | 340 | SAT | 0.0253s | SAT | 0.0451s | +0.0198s | 1.784x | valid SAT | valid SAT |
| `cnf_training_extra/extra_cnf/planted3sat_n80_m340_004.cnf` | 80 | 340 | SAT | 0.0265s | SAT | 0.0392s | +0.0127s | 1.478x | valid SAT | valid SAT |
| `cnf_training_extra/extra_cnf/planted3sat_n80_m340_005.cnf` | 80 | 340 | SAT | 0.0286s | SAT | 0.0374s | +0.0088s | 1.307x | valid SAT | valid SAT |
| `cnf_training_extra/extra_cnf/planted3sat_n80_m340_006.cnf` | 80 | 340 | SAT | 0.0268s | SAT | 0.0385s | +0.0117s | 1.435x | valid SAT | valid SAT |
| `cnf_training_extra/extra_cnf/xor_parity_sat_n18_eq18_w3_001.cnf` | 18 | 72 | SAT | 0.0416s | SAT | 0.0356s | -0.0061s | 0.854x | valid SAT | valid SAT |
| `cnf_training_extra/extra_cnf/xor_parity_sat_n24_eq24_w3_002.cnf` | 24 | 96 | SAT | 0.0231s | SAT | 0.0395s | +0.0164s | 1.711x | valid SAT | valid SAT |
| `cnf_training_extra/extra_cnf/xor_parity_sat_n30_eq30_w3_003.cnf` | 30 | 120 | SAT | 0.0271s | SAT | 0.0275s | +0.0004s | 1.013x | valid SAT | valid SAT |
| `cnf_training_extra/extra_cnf/xor_parity_sat_n32_eq20_w4_007.cnf` | 32 | 160 | SAT | 0.0360s | SAT | 0.0243s | -0.0117s | 0.674x | valid SAT | valid SAT |
| `cnf_training_extra/extra_cnf/xor_parity_sat_n40_eq35_w3_004.cnf` | 40 | 140 | SAT | 0.0340s | SAT | 0.0403s | +0.0063s | 1.185x | valid SAT | valid SAT |
| `cnf_training_extra/extra_cnf/xor_parity_sat_n48_eq28_w4_008.cnf` | 48 | 224 | SAT | 0.0352s | SAT | 0.0351s | -0.0001s | 0.998x | valid SAT | valid SAT |
| `cnf_training_extra/extra_cnf/xor_parity_sat_n60_eq45_w3_005.cnf` | 60 | 180 | SAT | 0.0284s | SAT | 0.0224s | -0.0060s | 0.789x | valid SAT | valid SAT |
| `cnf_training_extra/extra_cnf/xor_parity_sat_n80_eq55_w3_006.cnf` | 80 | 220 | SAT | 0.0291s | SAT | 0.0266s | -0.0025s | 0.916x | valid SAT | valid SAT |
| `cnf_training_extra/extra_cnf/xor_parity_unsat_n18_eq12_w3_001.cnf` | 18 | 48 | UNSAT | 0.0390s | UNSAT | 0.0244s | -0.0146s | 0.627x | valid UNSAT (format checked) | valid UNSAT (format checked) |
| `cnf_training_extra/extra_cnf/xor_parity_unsat_n24_eq16_w3_002.cnf` | 24 | 64 | UNSAT | 0.0237s | UNSAT | 0.0325s | +0.0088s | 1.371x | valid UNSAT (format checked) | valid UNSAT (format checked) |
| `cnf_training_extra/extra_cnf/xor_parity_unsat_n30_eq20_w3_003.cnf` | 30 | 80 | UNSAT | 0.0351s | UNSAT | 0.0311s | -0.0040s | 0.885x | valid UNSAT (format checked) | valid UNSAT (format checked) |
| `cnf_training_extra/extra_cnf/xor_parity_unsat_n32_eq18_w4_006.cnf` | 32 | 144 | UNSAT | 0.0215s | UNSAT | 0.0264s | +0.0049s | 1.229x | valid UNSAT (format checked) | valid UNSAT (format checked) |
| `cnf_training_extra/extra_cnf/xor_parity_unsat_n40_eq24_w3_004.cnf` | 40 | 96 | UNSAT | 0.0206s | UNSAT | 0.0244s | +0.0038s | 1.185x | valid UNSAT (format checked) | valid UNSAT (format checked) |
| `cnf_training_extra/extra_cnf/xor_parity_unsat_n60_eq32_w3_005.cnf` | 60 | 128 | UNSAT | 0.0235s | UNSAT | 0.0312s | +0.0077s | 1.330x | valid UNSAT (format checked) | valid UNSAT (format checked) |
| `large/test_1.cnf` | 373 | 811 | SAT | 0.0339s | SAT | 0.0432s | +0.0093s | 1.275x | valid SAT | valid SAT |
| `large/test_10.cnf` | 229 | 1280 | UNSAT | 0.8803s | UNSAT | 0.8136s | -0.0667s | 0.924x | valid UNSAT (format checked) | valid UNSAT (format checked) |
| `large/test_2.cnf` | 319 | 573 | SAT | 0.0392s | SAT | 0.0405s | +0.0014s | 1.035x | valid SAT | valid SAT |
| `large/test_3.cnf` | 227 | 1460 | UNSAT | 0.2624s | UNSAT | 0.2740s | +0.0116s | 1.044x | valid UNSAT (format checked) | valid UNSAT (format checked) |
| `large/test_4.cnf` | 219 | 1363 | UNSAT | 0.2504s | UNSAT | 0.2367s | -0.0137s | 0.945x | valid UNSAT (format checked) | valid UNSAT (format checked) |
| `large/test_5.cnf` | 244 | 772 | SAT | 0.0481s | SAT | 0.0303s | -0.0178s | 0.630x | valid SAT | valid SAT |
| `large/test_6.cnf` | 271 | 1393 | UNSAT | 3.5722s | UNSAT | 3.2607s | -0.3115s | 0.913x | valid UNSAT (format checked) | valid UNSAT (format checked) |
| `large/test_7.cnf` | 389 | 863 | SAT | 0.0433s | SAT | 0.0455s | +0.0022s | 1.051x | valid SAT | valid SAT |
| `large/test_8.cnf` | 298 | 1210 | SAT | 1.7199s | SAT | 1.7111s | -0.0088s | 0.995x | valid SAT | valid SAT |
| `large/test_9.cnf` | 365 | 969 | SAT | 0.0416s | SAT | 0.0424s | +0.0008s | 1.019x | valid SAT | valid SAT |
| `medium/test_1.cnf` | 63 | 835 | UNSAT | 0.0570s | UNSAT | 0.0405s | -0.0164s | 0.711x | valid UNSAT (format checked) | valid UNSAT (format checked) |
| `medium/test_10.cnf` | 68 | 822 | UNSAT | 0.0330s | UNSAT | 0.0419s | +0.0089s | 1.270x | valid UNSAT (format checked) | valid UNSAT (format checked) |
| `medium/test_2.cnf` | 69 | 352 | UNSAT | 0.0274s | UNSAT | 0.0386s | +0.0112s | 1.410x | valid UNSAT (format checked) | valid UNSAT (format checked) |
| `medium/test_3.cnf` | 172 | 774 | UNSAT | 0.4795s | UNSAT | 0.4861s | +0.0067s | 1.014x | valid UNSAT (format checked) | valid UNSAT (format checked) |
| `medium/test_4.cnf` | 191 | 886 | UNSAT | 0.8321s | UNSAT | 0.8496s | +0.0176s | 1.021x | valid UNSAT (format checked) | valid UNSAT (format checked) |
| `medium/test_5.cnf` | 55 | 713 | UNSAT | 0.0411s | UNSAT | 0.0255s | -0.0155s | 0.621x | valid UNSAT (format checked) | valid UNSAT (format checked) |
| `medium/test_6.cnf` | 61 | 512 | UNSAT | 0.0356s | UNSAT | 0.0293s | -0.0063s | 0.823x | valid UNSAT (format checked) | valid UNSAT (format checked) |
| `medium/test_7.cnf` | 75 | 562 | UNSAT | 0.0329s | UNSAT | 0.0305s | -0.0024s | 0.927x | valid UNSAT (format checked) | valid UNSAT (format checked) |
| `medium/test_8.cnf` | 130 | 333 | SAT | 0.0296s | SAT | 0.0266s | -0.0030s | 0.898x | valid SAT | valid SAT |
| `medium/test_9.cnf` | 138 | 379 | SAT | 0.0382s | SAT | 0.0336s | -0.0046s | 0.880x | valid SAT | valid SAT |
| `satlib_more/aim-100-1_6-no-1.cnf` | 100 | 160 | UNSAT | 0.0288s | UNSAT | 0.0241s | -0.0047s | 0.838x | valid UNSAT (format checked) | valid UNSAT (format checked) |
| `satlib_more/aim-100-1_6-no-2.cnf` | 100 | 160 | UNSAT | 0.0279s | UNSAT | 0.0252s | -0.0027s | 0.905x | valid UNSAT (format checked) | valid UNSAT (format checked) |
| `satlib_more/aim-100-1_6-yes1-1.cnf` | 100 | 160 | SAT | 0.0318s | SAT | 0.0288s | -0.0030s | 0.906x | valid SAT | valid SAT |
| `satlib_more/aim-100-1_6-yes1-2.cnf` | 100 | 160 | SAT | 0.0292s | SAT | 0.0416s | +0.0124s | 1.425x | valid SAT | valid SAT |
| `satlib_more/flat75-1.cnf` | 225 | 840 | SAT | 0.0277s | SAT | 0.0268s | -0.0008s | 0.970x | valid SAT | valid SAT |
| `satlib_more/flat75-10.cnf` | 225 | 840 | SAT | 0.0450s | SAT | 0.0316s | -0.0134s | 0.702x | valid SAT | valid SAT |
| `satlib_more/jnh1.cnf` | 100 | 850 | SAT | 0.0447s | SAT | 0.0485s | +0.0038s | 1.086x | valid SAT | valid SAT |
| `satlib_more/jnh10.cnf` | 100 | 850 | UNSAT | 0.0444s | UNSAT | 0.0371s | -0.0073s | 0.836x | valid UNSAT (format checked) | valid UNSAT (format checked) |
| `satlib_more/uf125-01.cnf` | 125 | 538 | SAT | 0.0411s | SAT | 0.0332s | -0.0079s | 0.808x | valid SAT | valid SAT |
| `satlib_more/uf125-010.cnf` | 125 | 538 | SAT | 0.0920s | SAT | 0.0973s | +0.0053s | 1.058x | valid SAT | valid SAT |
| `satlib_more/uf150-01.cnf` | 150 | 645 | SAT | 0.0692s | SAT | 0.0525s | -0.0167s | 0.759x | valid SAT | valid SAT |
| `satlib_more/uuf125-01.cnf` | 125 | 538 | UNSAT | 0.1180s | UNSAT | 0.1037s | -0.0143s | 0.879x | valid UNSAT (format checked) | valid UNSAT (format checked) |
| `satlib_more/uuf125-010.cnf` | 125 | 538 | UNSAT | 0.1462s | UNSAT | 0.1463s | +0.0002s | 1.001x | valid UNSAT (format checked) | valid UNSAT (format checked) |
| `satlib_more/uuf150-01.cnf` | 150 | 645 | UNSAT | 0.3324s | UNSAT | 0.3450s | +0.0126s | 1.038x | valid UNSAT (format checked) | valid UNSAT (format checked) |
| `satlib_subset/dubois20.cnf` | 60 | 160 | UNSAT | 0.0381s | UNSAT | 0.0387s | +0.0005s | 1.014x | valid UNSAT (format checked) | valid UNSAT (format checked) |
| `satlib_subset/dubois21.cnf` | 63 | 168 | UNSAT | 0.0397s | UNSAT | 0.0419s | +0.0021s | 1.054x | valid UNSAT (format checked) | valid UNSAT (format checked) |
| `satlib_subset/flat50-1.cnf` | 150 | 545 | SAT | 0.0390s | SAT | 0.0379s | -0.0011s | 0.972x | valid SAT | valid SAT |
| `satlib_subset/flat50-10.cnf` | 150 | 545 | SAT | 0.0336s | SAT | 0.0338s | +0.0003s | 1.008x | valid SAT | valid SAT |
| `satlib_subset/hole10.cnf` | 110 | 561 | UNSAT | 0.0213s | UNSAT | 0.0284s | +0.0071s | 1.335x | valid UNSAT (format checked) | valid UNSAT (format checked) |
| `satlib_subset/hole8.cnf` | 72 | 297 | UNSAT | 0.0286s | UNSAT | 0.0258s | -0.0028s | 0.902x | valid UNSAT (format checked) | valid UNSAT (format checked) |
| `satlib_subset/uf100-01.cnf` | 100 | 430 | SAT | 0.0594s | SAT | 0.0661s | +0.0067s | 1.112x | valid SAT | valid SAT |
| `satlib_subset/uf100-010.cnf` | 100 | 430 | SAT | 0.0380s | SAT | 0.0299s | -0.0081s | 0.787x | valid SAT | valid SAT |
| `satlib_subset/uuf100-01.cnf` | 100 | 430 | UNSAT | 0.0578s | UNSAT | 0.0559s | -0.0019s | 0.967x | valid UNSAT (format checked) | valid UNSAT (format checked) |
| `satlib_subset/uuf100-010.cnf` | 100 | 430 | UNSAT | 0.0666s | UNSAT | 0.0921s | +0.0255s | 1.383x | valid UNSAT (format checked) | valid UNSAT (format checked) |
| `small/test_1.cnf` | 19 | 26 | SAT | 0.0212s | SAT | 0.0209s | -0.0003s | 0.986x | valid SAT | valid SAT |
| `small/test_10.cnf` | 22 | 174 | UNSAT | 0.0391s | UNSAT | 0.0352s | -0.0039s | 0.900x | valid UNSAT (format checked) | valid UNSAT (format checked) |
| `small/test_2.cnf` | 46 | 176 | SAT | 0.0227s | SAT | 0.0418s | +0.0191s | 1.840x | valid SAT | valid SAT |
| `small/test_3.cnf` | 41 | 150 | SAT | 0.0242s | SAT | 0.0371s | +0.0129s | 1.535x | valid SAT | valid SAT |
| `small/test_4.cnf` | 30 | 167 | UNSAT | 0.0347s | UNSAT | 0.0228s | -0.0119s | 0.657x | valid UNSAT (format checked) | valid UNSAT (format checked) |
| `small/test_5.cnf` | 20 | 40 | SAT | 0.0298s | SAT | 0.0220s | -0.0077s | 0.740x | valid SAT | valid SAT |
| `small/test_6.cnf` | 42 | 70 | SAT | 0.0227s | SAT | 0.0388s | +0.0161s | 1.707x | valid SAT | valid SAT |
| `small/test_7.cnf` | 49 | 167 | SAT | 0.0268s | SAT | 0.0295s | +0.0027s | 1.100x | valid SAT | valid SAT |
| `small/test_8.cnf` | 14 | 68 | UNSAT | 0.0251s | UNSAT | 0.0332s | +0.0082s | 1.326x | valid UNSAT (brute-force checked) | valid UNSAT (brute-force checked) |
| `small/test_9.cnf` | 40 | 100 | SAT | 0.0287s | SAT | 0.0415s | +0.0128s | 1.445x | valid SAT | valid SAT |
| `special/dense.cnf` | 200 | 1500 | UNSAT | 0.1292s | UNSAT | 0.1175s | -0.0117s | 0.909x | valid UNSAT (format checked) | valid UNSAT (format checked) |
| `special/easy.cnf` | 200 | 400 | SAT | 0.0282s | SAT | 0.0306s | +0.0024s | 1.085x | valid SAT | valid SAT |
| `special/hard.cnf` | 200 | 850 | UNSAT | 2.6822s | UNSAT | 2.5600s | -0.1222s | 0.954x | valid UNSAT (format checked) | valid UNSAT (format checked) |
| `special/pigeonhole.cnf` | 90 | 415 | UNSAT | 0.0248s | UNSAT | 0.0339s | +0.0091s | 1.367x | valid UNSAT (format checked) | valid UNSAT (format checked) |
| `special/tseitin.cnf` | 40 | 160 | UNSAT | 0.0249s | UNSAT | 0.0394s | +0.0145s | 1.584x | valid UNSAT (format checked) | valid UNSAT (format checked) |
