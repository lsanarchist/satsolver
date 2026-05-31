# oldsatsolver.py vs satsolver.py avg5 comparison

- Test directory: `course_cnf_tests`
- Tests included: `278` CNF files
- Skipped timeout file(s): `cnf_training_complex__complex_cnf_hard__mycielski_iter4_color5_unsat.cnf`
- Old solver label: `oldsatsolver.py` (actual file used: `odlsatsover.py`)
- New solver: `satsolver.py`
- Repeats per solver per case: `5`
- Reported time: arithmetic average of `5` CLI runs
- Timeout per run: `60s`
- Wall clock: `840.6350s`

## Summary

| Metric | oldsatsolver.py | satsolver.py | Delta |
|---|---:|---:|---:|
| Correct all 5 repeats | 277/278 | 278/278 | +1 |
| Timeout cases | 1 | 0 | -1 |
| Sum of avg per-case times | 116.9595s | 47.1389s | -69.8206s |
| Improved valid cases |  | 258 |  |
| Regressed valid cases |  | 19 |  |

## Fixed Cases

| Source | Vars | Clauses | Old avg | New avg |
|---|---:|---:|---:|---:|
| `cnf_training_complex/complex_cnf_hard/planted3sat_balanced_n400_m1704_seed1.cnf` | 400 | 1704 | TIMEOUT 60.0000s | SAT 3.6467s |

## Biggest Avg Improvements

| Source | Old avg | New avg | Delta | Ratio | Old samples | New samples |
|---|---:|---:|---:|---:|---|---|
| `cnf_training_complex/complex_cnf_hard/planted3sat_balanced_n400_m1704_seed1.cnf` | TIMEOUT 60.0000s | SAT 3.6467s | -56.3533s | 0.061x | `[60.0000, 60.0000, 60.0000, 60.0000, 60.0000]` | `[3.5123, 3.4485, 3.6666, 3.8043, 3.8020]` |
| `large/test_6.cnf` | UNSAT 11.8183s | UNSAT 3.4038s | -8.4145s | 0.288x | `[11.3603, 11.8526, 11.9124, 12.0726, 11.8935]` | `[3.4476, 3.2953, 3.4640, 3.4150, 3.3973]` |
| `special/hard.cnf` | UNSAT 7.9452s | UNSAT 2.4969s | -5.4483s | 0.314x | `[8.0149, 7.9758, 7.9099, 7.9270, 7.8984]` | `[2.5804, 2.5372, 2.3730, 2.4828, 2.5113]` |
| `cnf_training_complex/complex_cnf_moderate/ramsey_R3_4_n10_unsat.cnf` | UNSAT 5.0795s | UNSAT 1.1364s | -3.9431s | 0.224x | `[5.0664, 5.0839, 5.0570, 4.9260, 5.2640]` | `[1.1332, 1.2133, 1.0932, 1.0848, 1.1573]` |
| `cnf_training_complex/complex_cnf_moderate/ramsey_R3_4_n9_unsat.cnf` | UNSAT 4.6750s | UNSAT 1.1814s | -3.4936s | 0.253x | `[4.9183, 4.5262, 4.5602, 4.7868, 4.5833]` | `[1.1732, 1.1212, 1.2370, 1.1817, 1.1938]` |
| `cnf_training_complex/complex_cnf_hard/ramsey_R3_4_n11_unsat.cnf` | UNSAT 3.5605s | UNSAT 1.2445s | -2.3160s | 0.350x | `[3.6812, 3.5509, 3.5055, 3.4604, 3.6046]` | `[1.3256, 1.1839, 1.2441, 1.2290, 1.2398]` |
| `cnf_training_complex/complex_cnf_hard/planted3sat_balanced_n320_m1363_seed2.cnf` | SAT 1.8786s | SAT 0.5711s | -1.3075s | 0.304x | `[1.8632, 1.9184, 1.9195, 1.8666, 1.8252]` | `[0.5540, 0.5916, 0.5799, 0.5865, 0.5434]` |
| `large/test_10.cnf` | UNSAT 1.7902s | UNSAT 0.9275s | -0.8627s | 0.518x | `[1.9453, 1.8450, 1.7024, 1.7622, 1.6961]` | `[0.8987, 0.9398, 0.9238, 0.9576, 0.9178]` |
| `medium/test_4.cnf` | UNSAT 1.6919s | UNSAT 0.8573s | -0.8346s | 0.507x | `[1.6824, 1.6900, 1.6760, 1.7153, 1.6958]` | `[0.8589, 0.8757, 0.8225, 0.8692, 0.8600]` |
| `cnf_training_complex/complex_cnf_moderate/mycielski_iter3_color4_unsat.cnf` | UNSAT 0.6840s | UNSAT 0.2767s | -0.4073s | 0.405x | `[0.6404, 0.6775, 0.6819, 0.6934, 0.7267]` | `[0.2760, 0.2788, 0.2961, 0.2611, 0.2715]` |
| `medium/test_3.cnf` | UNSAT 0.6643s | UNSAT 0.4775s | -0.1868s | 0.719x | `[0.6501, 0.6658, 0.6738, 0.6518, 0.6798]` | `[0.4638, 0.4611, 0.5104, 0.4912, 0.4611]` |
| `cnf_training_complex/complex_cnf_moderate/ordering_no_minimum_n12.cnf` | UNSAT 0.1499s | UNSAT 0.0679s | -0.0820s | 0.453x | `[0.1554, 0.1431, 0.1405, 0.1527, 0.1578]` | `[0.0608, 0.0697, 0.0743, 0.0716, 0.0631]` |
| `satlib_more/uuf150-01.cnf` | UNSAT 0.4236s | UNSAT 0.3441s | -0.0796s | 0.812x | `[0.4302, 0.4128, 0.4305, 0.4059, 0.4389]` | `[0.3354, 0.3218, 0.3307, 0.3503, 0.3822]` |
| `large/test_4.cnf` | UNSAT 0.2751s | UNSAT 0.2487s | -0.0265s | 0.904x | `[0.3005, 0.2625, 0.2733, 0.2853, 0.2541]` | `[0.2473, 0.2446, 0.2682, 0.2521, 0.2311]` |
| `cnf_training_extra/extra_cnf/planted3sat_n80_m340_001.cnf` | SAT 0.0605s | SAT 0.0376s | -0.0229s | 0.621x | `[0.0581, 0.0477, 0.0657, 0.0709, 0.0598]` | `[0.0379, 0.0360, 0.0336, 0.0375, 0.0429]` |
| `cnf_training_extra/extra_cnf/cardinality_exactly_one_unsat_g8_s5_004.cnf` | UNSAT 0.0460s | UNSAT 0.0235s | -0.0225s | 0.511x | `[0.0423, 0.0351, 0.0526, 0.0528, 0.0470]` | `[0.0224, 0.0217, 0.0291, 0.0228, 0.0214]` |
| `cnf_training_extra/extra_cnf/xor_parity_unsat_n30_eq20_w3_003.cnf` | UNSAT 0.0517s | UNSAT 0.0294s | -0.0223s | 0.569x | `[0.0544, 0.0518, 0.0570, 0.0474, 0.0480]` | `[0.0260, 0.0357, 0.0270, 0.0276, 0.0307]` |
| `cnf_training_complex/complex_cnf_hard/tseitin_deg3_v160_sat.cnf` | SAT 0.0660s | SAT 0.0456s | -0.0204s | 0.691x | `[0.0621, 0.0553, 0.0681, 0.0711, 0.0735]` | `[0.0429, 0.0499, 0.0440, 0.0439, 0.0472]` |
| `satlib_more/uuf125-01.cnf` | UNSAT 0.1203s | UNSAT 0.1010s | -0.0193s | 0.839x | `[0.1080, 0.1288, 0.1267, 0.1169, 0.1211]` | `[0.0968, 0.0878, 0.1115, 0.1043, 0.1046]` |
| `satlib_more/uuf125-010.cnf` | UNSAT 0.1636s | UNSAT 0.1446s | -0.0189s | 0.884x | `[0.1641, 0.1537, 0.1780, 0.1643, 0.1578]` | `[0.1571, 0.1314, 0.1459, 0.1482, 0.1405]` |

## Biggest Avg Regressions

| Source | Old avg | New avg | Delta | Ratio | Old samples | New samples |
|---|---:|---:|---:|---:|---|---|
| `cnf_training_complex/complex_cnf_hard/planted3sat_balanced_n260_m1108_seed1.cnf` | SAT 2.1544s | SAT 15.9405s | +13.7860s | 7.399x | `[2.0911, 2.2029, 2.1578, 2.1439, 2.1764]` | `[15.4868, 16.5787, 15.5945, 16.1270, 15.9152]` |
| `large/test_8.cnf` | SAT 0.2833s | SAT 1.6251s | +1.3418s | 5.736x | `[0.2937, 0.2690, 0.2716, 0.2882, 0.2941]` | `[1.6611, 1.6905, 1.5689, 1.6001, 1.6050]` |
| `cnf_training_complex/complex_cnf_moderate/planted3sat_balanced_n200_m852_seed2.cnf` | SAT 0.5125s | SAT 0.9478s | +0.4353s | 1.849x | `[0.5152, 0.4959, 0.5060, 0.4978, 0.5478]` | `[0.9870, 0.9123, 0.9341, 0.9488, 0.9569]` |
| `cnf_training_complex/complex_cnf_hard/planted3sat_balanced_n320_m1363_seed1.cnf` | SAT 0.7114s | SAT 0.8551s | +0.1436s | 1.202x | `[0.7553, 0.6700, 0.7043, 0.7201, 0.7075]` | `[1.0641, 0.7801, 0.7975, 0.8233, 0.8104]` |
| `cnf_training_complex/complex_cnf_moderate/xor_sparse_sat_n128_eq165_w3-4_seed3.cnf` | SAT 0.1098s | SAT 0.2420s | +0.1322s | 2.203x | `[0.1086, 0.1123, 0.1078, 0.1156, 0.1048]` | `[0.2264, 0.2464, 0.2427, 0.2478, 0.2466]` |
| `cnf_training_complex/complex_cnf_hard/planted3sat_balanced_n260_m1108_seed2.cnf` | SAT 1.0129s | SAT 1.0815s | +0.0686s | 1.068x | `[0.9775, 0.9739, 0.9720, 1.0692, 1.0719]` | `[1.0520, 1.0760, 1.0383, 1.0547, 1.1867]` |
| `cnf_training_complex/complex_cnf_moderate/planted3sat_balanced_n200_m852_seed1.cnf` | SAT 0.4125s | SAT 0.4695s | +0.0570s | 1.138x | `[0.4161, 0.4082, 0.4248, 0.4100, 0.4033]` | `[0.4616, 0.4871, 0.4871, 0.4611, 0.4506]` |
| `satlib_more/uf125-010.cnf` | SAT 0.0583s | SAT 0.0809s | +0.0226s | 1.387x | `[0.0560, 0.0460, 0.0642, 0.0470, 0.0784]` | `[0.0928, 0.0779, 0.0777, 0.0783, 0.0780]` |
| `large/test_3.cnf` | UNSAT 0.3068s | UNSAT 0.3274s | +0.0206s | 1.067x | `[0.2843, 0.3147, 0.2968, 0.3032, 0.3349]` | `[0.2962, 0.3301, 0.2862, 0.3606, 0.3638]` |
| `satlib_subset/flat50-10.cnf` | SAT 0.0356s | SAT 0.0410s | +0.0054s | 1.151x | `[0.0391, 0.0307, 0.0351, 0.0392, 0.0341]` | `[0.0414, 0.0410, 0.0467, 0.0397, 0.0362]` |
| `small/test_1.cnf` | SAT 0.0333s | SAT 0.0361s | +0.0028s | 1.084x | `[0.0312, 0.0396, 0.0309, 0.0268, 0.0382]` | `[0.0308, 0.0340, 0.0397, 0.0428, 0.0333]` |
| `cnf_training_extra/extra_cnf/xor_parity_unsat_n40_eq24_w3_004.cnf` | UNSAT 0.0360s | UNSAT 0.0388s | +0.0028s | 1.077x | `[0.0435, 0.0328, 0.0368, 0.0293, 0.0376]` | `[0.0403, 0.0498, 0.0297, 0.0470, 0.0270]` |
| `cnf_training_extra/extra_cnf/xor_parity_sat_n48_eq28_w4_008.cnf` | SAT 0.0389s | SAT 0.0409s | +0.0019s | 1.049x | `[0.0347, 0.0326, 0.0339, 0.0382, 0.0551]` | `[0.0488, 0.0451, 0.0503, 0.0325, 0.0276]` |
| `cnf_training_extra/extra_cnf/xor_parity_sat_n40_eq35_w3_004.cnf` | SAT 0.0342s | SAT 0.0357s | +0.0016s | 1.045x | `[0.0338, 0.0337, 0.0340, 0.0363, 0.0331]` | `[0.0436, 0.0308, 0.0374, 0.0403, 0.0265]` |
| `cnf_training_extra/extra_cnf/graphcolor_k3_complete_K6_unsat.cnf` | UNSAT 0.0314s | UNSAT 0.0329s | +0.0015s | 1.048x | `[0.0318, 0.0299, 0.0308, 0.0325, 0.0319]` | `[0.0349, 0.0337, 0.0381, 0.0242, 0.0335]` |
| `satlib_subset/uuf100-010.cnf` | UNSAT 0.0657s | UNSAT 0.0669s | +0.0012s | 1.019x | `[0.0635, 0.0603, 0.0739, 0.0700, 0.0607]` | `[0.0587, 0.0675, 0.0711, 0.0812, 0.0562]` |
| `cnf_training_extra/extra_cnf/equivalence_chain_len120_sat.cnf` | SAT 0.0367s | SAT 0.0377s | +0.0010s | 1.026x | `[0.0424, 0.0341, 0.0288, 0.0415, 0.0368]` | `[0.0421, 0.0257, 0.0346, 0.0446, 0.0415]` |
| `cnf_training_extra/extra_cnf/equivalence_chain_len120_unsat.cnf` | UNSAT 0.0351s | UNSAT 0.0355s | +0.0004s | 1.011x | `[0.0321, 0.0320, 0.0427, 0.0280, 0.0406]` | `[0.0438, 0.0256, 0.0328, 0.0434, 0.0316]` |
| `satlib_subset/uf100-01.cnf` | SAT 0.0607s | SAT 0.0609s | +0.0002s | 1.003x | `[0.0451, 0.0626, 0.0546, 0.0784, 0.0630]` | `[0.0588, 0.0691, 0.0575, 0.0625, 0.0565]` |
| `cnf_training_extra/extra_cnf/graphcolor_k3_planted_v16_e35_002.cnf` | SAT 0.0353s | SAT 0.0350s | -0.0004s | 0.989x | `[0.0289, 0.0338, 0.0353, 0.0478, 0.0309]` | `[0.0361, 0.0377, 0.0350, 0.0293, 0.0365]` |

## All Cases

| Source | Vars | Clauses | Old Status | Old Avg | New Status | New Avg | Delta | Ratio | Old Samples | New Samples |
|---|---:|---:|---|---:|---|---:|---:|---:|---|---|
| `cnf_training_complex/complex_cnf_hard/planted3sat_balanced_n260_m1108_seed1.cnf` | 260 | 1108 | SAT | 2.1544s | SAT | 15.9405s | +13.7860s | 7.399x | `[2.0911, 2.2029, 2.1578, 2.1439, 2.1764]` | `[15.4868, 16.5787, 15.5945, 16.1270, 15.9152]` |
| `cnf_training_complex/complex_cnf_hard/planted3sat_balanced_n260_m1108_seed2.cnf` | 260 | 1108 | SAT | 1.0129s | SAT | 1.0815s | +0.0686s | 1.068x | `[0.9775, 0.9739, 0.9720, 1.0692, 1.0719]` | `[1.0520, 1.0760, 1.0383, 1.0547, 1.1867]` |
| `cnf_training_complex/complex_cnf_hard/planted3sat_balanced_n320_m1363_seed1.cnf` | 320 | 1363 | SAT | 0.7114s | SAT | 0.8551s | +0.1436s | 1.202x | `[0.7553, 0.6700, 0.7043, 0.7201, 0.7075]` | `[1.0641, 0.7801, 0.7975, 0.8233, 0.8104]` |
| `cnf_training_complex/complex_cnf_hard/planted3sat_balanced_n320_m1363_seed2.cnf` | 320 | 1363 | SAT | 1.8786s | SAT | 0.5711s | -1.3075s | 0.304x | `[1.8632, 1.9184, 1.9195, 1.8666, 1.8252]` | `[0.5540, 0.5916, 0.5799, 0.5865, 0.5434]` |
| `cnf_training_complex/complex_cnf_hard/planted3sat_balanced_n400_m1704_seed1.cnf` | 400 | 1704 | TIMEOUT | 60.0000s | SAT | 3.6467s | -56.3533s | 0.061x | `[60.0000, 60.0000, 60.0000, 60.0000, 60.0000]` | `[3.5123, 3.4485, 3.6666, 3.8043, 3.8020]` |
| `cnf_training_complex/complex_cnf_hard/ramsey_R3_4_n11_unsat.cnf` | 55 | 495 | UNSAT | 3.5605s | UNSAT | 1.2445s | -2.3160s | 0.350x | `[3.6812, 3.5509, 3.5055, 3.4604, 3.6046]` | `[1.3256, 1.1839, 1.2441, 1.2290, 1.2398]` |
| `cnf_training_complex/complex_cnf_hard/tseitin_deg3_v100_sat.cnf` | 150 | 400 | SAT | 0.0440s | SAT | 0.0329s | -0.0111s | 0.748x | `[0.0485, 0.0447, 0.0495, 0.0418, 0.0356]` | `[0.0418, 0.0297, 0.0277, 0.0379, 0.0277]` |
| `cnf_training_complex/complex_cnf_hard/tseitin_deg3_v100_unsat.cnf` | 150 | 400 | UNSAT | 0.0389s | UNSAT | 0.0320s | -0.0069s | 0.824x | `[0.0429, 0.0363, 0.0332, 0.0468, 0.0353]` | `[0.0432, 0.0375, 0.0258, 0.0301, 0.0237]` |
| `cnf_training_complex/complex_cnf_hard/tseitin_deg3_v120_sat.cnf` | 180 | 480 | SAT | 0.0420s | SAT | 0.0414s | -0.0005s | 0.987x | `[0.0362, 0.0495, 0.0366, 0.0409, 0.0468]` | `[0.0462, 0.0406, 0.0406, 0.0362, 0.0436]` |
| `cnf_training_complex/complex_cnf_hard/tseitin_deg3_v120_unsat.cnf` | 180 | 480 | UNSAT | 0.0319s | UNSAT | 0.0301s | -0.0018s | 0.944x | `[0.0324, 0.0325, 0.0319, 0.0301, 0.0325]` | `[0.0358, 0.0247, 0.0273, 0.0364, 0.0263]` |
| `cnf_training_complex/complex_cnf_hard/tseitin_deg3_v160_sat.cnf` | 240 | 640 | SAT | 0.0660s | SAT | 0.0456s | -0.0204s | 0.691x | `[0.0621, 0.0553, 0.0681, 0.0711, 0.0735]` | `[0.0429, 0.0499, 0.0440, 0.0439, 0.0472]` |
| `cnf_training_complex/complex_cnf_hard/tseitin_deg3_v160_unsat.cnf` | 240 | 640 | UNSAT | 0.0392s | UNSAT | 0.0296s | -0.0097s | 0.754x | `[0.0485, 0.0459, 0.0382, 0.0317, 0.0318]` | `[0.0376, 0.0294, 0.0315, 0.0244, 0.0248]` |
| `cnf_training_complex/complex_cnf_hard/tseitin_deg4_v64_sat.cnf` | 128 | 512 | SAT | 0.0531s | SAT | 0.0511s | -0.0020s | 0.962x | `[0.0614, 0.0496, 0.0492, 0.0500, 0.0553]` | `[0.0499, 0.0478, 0.0568, 0.0451, 0.0558]` |
| `cnf_training_complex/complex_cnf_hard/tseitin_deg4_v64_unsat.cnf` | 128 | 512 | UNSAT | 0.0398s | UNSAT | 0.0297s | -0.0101s | 0.747x | `[0.0359, 0.0364, 0.0445, 0.0320, 0.0501]` | `[0.0424, 0.0299, 0.0236, 0.0278, 0.0246]` |
| `cnf_training_complex/complex_cnf_hard/tseitin_deg4_v96_sat.cnf` | 192 | 768 | SAT | 0.0481s | SAT | 0.0387s | -0.0094s | 0.805x | `[0.0421, 0.0413, 0.0458, 0.0398, 0.0712]` | `[0.0385, 0.0471, 0.0321, 0.0417, 0.0341]` |
| `cnf_training_complex/complex_cnf_hard/tseitin_deg4_v96_unsat.cnf` | 192 | 768 | UNSAT | 0.0414s | UNSAT | 0.0289s | -0.0125s | 0.697x | `[0.0389, 0.0484, 0.0457, 0.0377, 0.0364]` | `[0.0300, 0.0268, 0.0289, 0.0268, 0.0318]` |
| `cnf_training_complex/complex_cnf_hard/vdw_2color_k4_n45_unsat.cnf` | 45 | 630 | UNSAT | 0.0607s | UNSAT | 0.0566s | -0.0040s | 0.934x | `[0.0655, 0.0584, 0.0595, 0.0656, 0.0543]` | `[0.0646, 0.0654, 0.0465, 0.0576, 0.0490]` |
| `cnf_training_complex/complex_cnf_hard/vdw_2color_k4_n60_unsat.cnf` | 60 | 1140 | UNSAT | 0.0781s | UNSAT | 0.0628s | -0.0153s | 0.804x | `[0.0786, 0.0810, 0.0840, 0.0739, 0.0731]` | `[0.0589, 0.0582, 0.0575, 0.0671, 0.0723]` |
| `cnf_training_complex/complex_cnf_hard/xor_sparse_unsat_n100_eq135_w3-4_seed4.cnf` | 100 | 828 | UNSAT | 0.0363s | UNSAT | 0.0308s | -0.0054s | 0.850x | `[0.0343, 0.0343, 0.0331, 0.0336, 0.0461]` | `[0.0385, 0.0359, 0.0248, 0.0257, 0.0293]` |
| `cnf_training_complex/complex_cnf_hard/xor_sparse_unsat_n140_eq190_w3-4_seed5.cnf` | 140 | 1104 | UNSAT | 0.0430s | UNSAT | 0.0342s | -0.0088s | 0.796x | `[0.0356, 0.0481, 0.0523, 0.0351, 0.0440]` | `[0.0384, 0.0283, 0.0317, 0.0386, 0.0341]` |
| `cnf_training_complex/complex_cnf_hard/xor_sparse_unsat_n180_eq250_w3-4_seed6.cnf` | 180 | 1544 | UNSAT | 0.0462s | UNSAT | 0.0332s | -0.0130s | 0.719x | `[0.0497, 0.0358, 0.0531, 0.0389, 0.0536]` | `[0.0282, 0.0338, 0.0460, 0.0284, 0.0297]` |
| `cnf_training_complex/complex_cnf_moderate/mycielski_iter2_color3_unsat.cnf` | 33 | 104 | UNSAT | 0.0381s | UNSAT | 0.0264s | -0.0117s | 0.692x | `[0.0365, 0.0329, 0.0410, 0.0480, 0.0321]` | `[0.0242, 0.0257, 0.0254, 0.0324, 0.0242]` |
| `cnf_training_complex/complex_cnf_moderate/mycielski_iter2_color4_sat.cnf` | 44 | 157 | SAT | 0.0401s | SAT | 0.0296s | -0.0105s | 0.738x | `[0.0336, 0.0467, 0.0338, 0.0379, 0.0485]` | `[0.0265, 0.0287, 0.0401, 0.0287, 0.0239]` |
| `cnf_training_complex/complex_cnf_moderate/mycielski_iter3_color4_unsat.cnf` | 92 | 445 | UNSAT | 0.6840s | UNSAT | 0.2767s | -0.4073s | 0.405x | `[0.6404, 0.6775, 0.6819, 0.6934, 0.7267]` | `[0.2760, 0.2788, 0.2961, 0.2611, 0.2715]` |
| `cnf_training_complex/complex_cnf_moderate/mycielski_iter3_color5_sat.cnf` | 115 | 608 | SAT | 0.0398s | SAT | 0.0332s | -0.0067s | 0.833x | `[0.0345, 0.0335, 0.0376, 0.0519, 0.0416]` | `[0.0319, 0.0393, 0.0270, 0.0348, 0.0328]` |
| `cnf_training_complex/complex_cnf_moderate/ordering_no_minimum_n10.cnf` | 45 | 730 | UNSAT | 0.0617s | UNSAT | 0.0467s | -0.0150s | 0.757x | `[0.0533, 0.0617, 0.0623, 0.0703, 0.0606]` | `[0.0461, 0.0385, 0.0568, 0.0511, 0.0407]` |
| `cnf_training_complex/complex_cnf_moderate/ordering_no_minimum_n12.cnf` | 66 | 1332 | UNSAT | 0.1499s | UNSAT | 0.0679s | -0.0820s | 0.453x | `[0.1554, 0.1431, 0.1405, 0.1527, 0.1578]` | `[0.0608, 0.0697, 0.0743, 0.0716, 0.0631]` |
| `cnf_training_complex/complex_cnf_moderate/ordering_no_minimum_n8.cnf` | 28 | 344 | UNSAT | 0.0480s | UNSAT | 0.0355s | -0.0126s | 0.739x | `[0.0416, 0.0421, 0.0460, 0.0496, 0.0607]` | `[0.0337, 0.0313, 0.0325, 0.0450, 0.0349]` |
| `cnf_training_complex/complex_cnf_moderate/orthogonal_latin_squares_order3_sat.cnf` | 81 | 1998 | SAT | 0.0499s | SAT | 0.0435s | -0.0064s | 0.872x | `[0.0462, 0.0483, 0.0558, 0.0455, 0.0536]` | `[0.0508, 0.0348, 0.0458, 0.0447, 0.0414]` |
| `cnf_training_complex/complex_cnf_moderate/pigeonhole_php_11_into_10.cnf` | 110 | 1056 | UNSAT | 0.0379s | UNSAT | 0.0267s | -0.0112s | 0.704x | `[0.0335, 0.0417, 0.0441, 0.0342, 0.0358]` | `[0.0250, 0.0288, 0.0279, 0.0266, 0.0250]` |
| `cnf_training_complex/complex_cnf_moderate/pigeonhole_php_13_into_12.cnf` | 156 | 1807 | UNSAT | 0.0379s | UNSAT | 0.0358s | -0.0021s | 0.945x | `[0.0348, 0.0371, 0.0392, 0.0420, 0.0363]` | `[0.0291, 0.0467, 0.0343, 0.0416, 0.0273]` |
| `cnf_training_complex/complex_cnf_moderate/pigeonhole_php_9_into_8.cnf` | 72 | 549 | UNSAT | 0.0372s | UNSAT | 0.0280s | -0.0092s | 0.753x | `[0.0485, 0.0349, 0.0319, 0.0330, 0.0376]` | `[0.0263, 0.0260, 0.0243, 0.0261, 0.0373]` |
| `cnf_training_complex/complex_cnf_moderate/planted3sat_balanced_n120_m511_seed1.cnf` | 120 | 511 | SAT | 0.0436s | SAT | 0.0342s | -0.0094s | 0.784x | `[0.0425, 0.0386, 0.0373, 0.0493, 0.0502]` | `[0.0308, 0.0304, 0.0317, 0.0379, 0.0399]` |
| `cnf_training_complex/complex_cnf_moderate/planted3sat_balanced_n120_m511_seed2.cnf` | 120 | 511 | SAT | 0.0420s | SAT | 0.0325s | -0.0095s | 0.775x | `[0.0476, 0.0379, 0.0361, 0.0405, 0.0478]` | `[0.0322, 0.0289, 0.0311, 0.0292, 0.0411]` |
| `cnf_training_complex/complex_cnf_moderate/planted3sat_balanced_n160_m682_seed1.cnf` | 160 | 682 | SAT | 0.0527s | SAT | 0.0360s | -0.0167s | 0.684x | `[0.0580, 0.0474, 0.0450, 0.0552, 0.0579]` | `[0.0350, 0.0364, 0.0374, 0.0364, 0.0350]` |
| `cnf_training_complex/complex_cnf_moderate/planted3sat_balanced_n160_m682_seed2.cnf` | 160 | 682 | SAT | 0.0457s | SAT | 0.0426s | -0.0030s | 0.933x | `[0.0499, 0.0473, 0.0439, 0.0432, 0.0442]` | `[0.0538, 0.0412, 0.0435, 0.0376, 0.0371]` |
| `cnf_training_complex/complex_cnf_moderate/planted3sat_balanced_n200_m852_seed1.cnf` | 200 | 852 | SAT | 0.4125s | SAT | 0.4695s | +0.0570s | 1.138x | `[0.4161, 0.4082, 0.4248, 0.4100, 0.4033]` | `[0.4616, 0.4871, 0.4871, 0.4611, 0.4506]` |
| `cnf_training_complex/complex_cnf_moderate/planted3sat_balanced_n200_m852_seed2.cnf` | 200 | 852 | SAT | 0.5125s | SAT | 0.9478s | +0.4353s | 1.849x | `[0.5152, 0.4959, 0.5060, 0.4978, 0.5478]` | `[0.9870, 0.9123, 0.9341, 0.9488, 0.9569]` |
| `cnf_training_complex/complex_cnf_moderate/ramsey_R3_3_n6_unsat.cnf` | 15 | 40 | UNSAT | 0.0401s | UNSAT | 0.0345s | -0.0056s | 0.859x | `[0.0334, 0.0486, 0.0355, 0.0506, 0.0325]` | `[0.0333, 0.0399, 0.0245, 0.0497, 0.0250]` |
| `cnf_training_complex/complex_cnf_moderate/ramsey_R3_3_n7_unsat.cnf` | 21 | 70 | UNSAT | 0.0365s | UNSAT | 0.0289s | -0.0076s | 0.792x | `[0.0416, 0.0308, 0.0353, 0.0382, 0.0363]` | `[0.0279, 0.0354, 0.0287, 0.0269, 0.0255]` |
| `cnf_training_complex/complex_cnf_moderate/ramsey_R3_3_n8_unsat.cnf` | 28 | 112 | UNSAT | 0.0355s | UNSAT | 0.0278s | -0.0077s | 0.783x | `[0.0326, 0.0341, 0.0341, 0.0423, 0.0344]` | `[0.0244, 0.0254, 0.0305, 0.0298, 0.0289]` |
| `cnf_training_complex/complex_cnf_moderate/ramsey_R3_4_n10_unsat.cnf` | 45 | 330 | UNSAT | 5.0795s | UNSAT | 1.1364s | -3.9431s | 0.224x | `[5.0664, 5.0839, 5.0570, 4.9260, 5.2640]` | `[1.1332, 1.2133, 1.0932, 1.0848, 1.1573]` |
| `cnf_training_complex/complex_cnf_moderate/ramsey_R3_4_n9_unsat.cnf` | 36 | 210 | UNSAT | 4.6750s | UNSAT | 1.1814s | -3.4936s | 0.253x | `[4.9183, 4.5262, 4.5602, 4.7868, 4.5833]` | `[1.1732, 1.1212, 1.2370, 1.1817, 1.1938]` |
| `cnf_training_complex/complex_cnf_moderate/tseitin_deg3_v40_sat.cnf` | 60 | 160 | SAT | 0.0427s | SAT | 0.0356s | -0.0071s | 0.835x | `[0.0349, 0.0401, 0.0672, 0.0367, 0.0345]` | `[0.0409, 0.0395, 0.0304, 0.0318, 0.0355]` |
| `cnf_training_complex/complex_cnf_moderate/tseitin_deg3_v40_unsat.cnf` | 60 | 160 | UNSAT | 0.0382s | UNSAT | 0.0268s | -0.0114s | 0.702x | `[0.0422, 0.0427, 0.0310, 0.0327, 0.0422]` | `[0.0234, 0.0312, 0.0255, 0.0260, 0.0277]` |
| `cnf_training_complex/complex_cnf_moderate/tseitin_deg3_v60_sat.cnf` | 90 | 240 | SAT | 0.0442s | SAT | 0.0296s | -0.0146s | 0.670x | `[0.0348, 0.0573, 0.0512, 0.0311, 0.0466]` | `[0.0292, 0.0304, 0.0334, 0.0312, 0.0239]` |
| `cnf_training_complex/complex_cnf_moderate/tseitin_deg3_v60_unsat.cnf` | 90 | 240 | UNSAT | 0.0440s | UNSAT | 0.0350s | -0.0090s | 0.796x | `[0.0498, 0.0519, 0.0439, 0.0351, 0.0394]` | `[0.0322, 0.0290, 0.0368, 0.0361, 0.0411]` |
| `cnf_training_complex/complex_cnf_moderate/tseitin_deg3_v80_sat.cnf` | 120 | 320 | SAT | 0.0468s | SAT | 0.0317s | -0.0152s | 0.676x | `[0.0437, 0.0460, 0.0491, 0.0482, 0.0471]` | `[0.0379, 0.0271, 0.0298, 0.0391, 0.0243]` |
| `cnf_training_complex/complex_cnf_moderate/tseitin_deg3_v80_unsat.cnf` | 120 | 320 | UNSAT | 0.0356s | UNSAT | 0.0342s | -0.0013s | 0.962x | `[0.0351, 0.0300, 0.0352, 0.0331, 0.0443]` | `[0.0225, 0.0479, 0.0368, 0.0396, 0.0244]` |
| `cnf_training_complex/complex_cnf_moderate/vdw_2color_k3_n16_unsat.cnf` | 16 | 112 | UNSAT | 0.0389s | UNSAT | 0.0331s | -0.0058s | 0.850x | `[0.0518, 0.0285, 0.0333, 0.0485, 0.0324]` | `[0.0345, 0.0274, 0.0353, 0.0282, 0.0399]` |
| `cnf_training_complex/complex_cnf_moderate/vdw_2color_k3_n9_unsat.cnf` | 9 | 32 | UNSAT | 0.0346s | UNSAT | 0.0315s | -0.0031s | 0.911x | `[0.0308, 0.0387, 0.0387, 0.0320, 0.0329]` | `[0.0273, 0.0396, 0.0303, 0.0325, 0.0281]` |
| `cnf_training_complex/complex_cnf_moderate/vdw_2color_k4_n35_unsat.cnf` | 35 | 374 | UNSAT | 0.0620s | UNSAT | 0.0481s | -0.0139s | 0.776x | `[0.0674, 0.0597, 0.0657, 0.0651, 0.0518]` | `[0.0506, 0.0464, 0.0476, 0.0487, 0.0473]` |
| `cnf_training_complex/complex_cnf_moderate/xor_sparse_sat_n128_eq165_w3-4_seed3.cnf` | 128 | 1000 | SAT | 0.1098s | SAT | 0.2420s | +0.1322s | 2.203x | `[0.1086, 0.1123, 0.1078, 0.1156, 0.1048]` | `[0.2264, 0.2464, 0.2427, 0.2478, 0.2466]` |
| `cnf_training_complex/complex_cnf_moderate/xor_sparse_sat_n64_eq82_w3_seed1.cnf` | 64 | 328 | SAT | 0.0397s | SAT | 0.0299s | -0.0099s | 0.752x | `[0.0445, 0.0380, 0.0363, 0.0456, 0.0343]` | `[0.0296, 0.0267, 0.0401, 0.0253, 0.0276]` |
| `cnf_training_complex/complex_cnf_moderate/xor_sparse_sat_n96_eq125_w3_seed2.cnf` | 96 | 500 | SAT | 0.0412s | SAT | 0.0308s | -0.0104s | 0.747x | `[0.0388, 0.0421, 0.0365, 0.0393, 0.0493]` | `[0.0311, 0.0317, 0.0290, 0.0308, 0.0314]` |
| `cnf_training_complex/complex_cnf_moderate/xor_sparse_unsat_n48_eq62_w3_seed1.cnf` | 48 | 248 | UNSAT | 0.0421s | UNSAT | 0.0299s | -0.0121s | 0.711x | `[0.0316, 0.0438, 0.0449, 0.0495, 0.0405]` | `[0.0394, 0.0253, 0.0254, 0.0367, 0.0227]` |
| `cnf_training_complex/complex_cnf_moderate/xor_sparse_unsat_n64_eq86_w3_seed2.cnf` | 64 | 344 | UNSAT | 0.0454s | UNSAT | 0.0305s | -0.0149s | 0.673x | `[0.0436, 0.0611, 0.0351, 0.0543, 0.0328]` | `[0.0336, 0.0277, 0.0253, 0.0257, 0.0403]` |
| `cnf_training_complex/complex_cnf_moderate/xor_sparse_unsat_n80_eq108_w3-4_seed3.cnf` | 80 | 608 | UNSAT | 0.0353s | UNSAT | 0.0314s | -0.0039s | 0.890x | `[0.0416, 0.0374, 0.0377, 0.0286, 0.0311]` | `[0.0368, 0.0306, 0.0384, 0.0233, 0.0278]` |
| `cnf_training_complex/complex_cnf_stress/tseitin_deg3_v240_unsat.cnf` | 360 | 960 | UNSAT | 0.0429s | UNSAT | 0.0349s | -0.0080s | 0.814x | `[0.0404, 0.0539, 0.0447, 0.0368, 0.0389]` | `[0.0321, 0.0373, 0.0405, 0.0258, 0.0390]` |
| `cnf_training_complex/complex_cnf_stress/tseitin_deg4_v160_unsat.cnf` | 320 | 1280 | UNSAT | 0.0401s | UNSAT | 0.0318s | -0.0084s | 0.792x | `[0.0372, 0.0358, 0.0361, 0.0356, 0.0559]` | `[0.0286, 0.0270, 0.0324, 0.0393, 0.0315]` |
| `cnf_training_complex/complex_cnf_stress/xor_sparse_unsat_n240_eq330_w3-4_seed1.cnf` | 240 | 1996 | UNSAT | 0.0471s | UNSAT | 0.0382s | -0.0090s | 0.810x | `[0.0483, 0.0550, 0.0403, 0.0497, 0.0424]` | `[0.0398, 0.0317, 0.0401, 0.0328, 0.0465]` |
| `cnf_training_extra/extra_cnf/cardinality_exactly_one_sat_g10_s5_004.cnf` | 50 | 110 | SAT | 0.0356s | SAT | 0.0288s | -0.0068s | 0.809x | `[0.0329, 0.0304, 0.0386, 0.0454, 0.0308]` | `[0.0299, 0.0311, 0.0385, 0.0224, 0.0222]` |
| `cnf_training_extra/extra_cnf/cardinality_exactly_one_sat_g12_s6_005.cnf` | 72 | 192 | SAT | 0.0349s | SAT | 0.0280s | -0.0068s | 0.805x | `[0.0352, 0.0336, 0.0326, 0.0321, 0.0408]` | `[0.0260, 0.0254, 0.0364, 0.0218, 0.0305]` |
| `cnf_training_extra/extra_cnf/cardinality_exactly_one_sat_g16_s4_006.cnf` | 64 | 112 | SAT | 0.0350s | SAT | 0.0335s | -0.0016s | 0.956x | `[0.0323, 0.0320, 0.0337, 0.0455, 0.0317]` | `[0.0240, 0.0307, 0.0401, 0.0374, 0.0351]` |
| `cnf_training_extra/extra_cnf/cardinality_exactly_one_sat_g4_s4_001.cnf` | 16 | 28 | SAT | 0.0348s | SAT | 0.0290s | -0.0058s | 0.833x | `[0.0296, 0.0284, 0.0467, 0.0277, 0.0418]` | `[0.0345, 0.0224, 0.0362, 0.0312, 0.0207]` |
| `cnf_training_extra/extra_cnf/cardinality_exactly_one_sat_g5_s5_002.cnf` | 25 | 55 | SAT | 0.0358s | SAT | 0.0288s | -0.0070s | 0.805x | `[0.0348, 0.0327, 0.0388, 0.0307, 0.0420]` | `[0.0226, 0.0203, 0.0364, 0.0330, 0.0318]` |
| `cnf_training_extra/extra_cnf/cardinality_exactly_one_sat_g8_s4_003.cnf` | 32 | 56 | SAT | 0.0326s | SAT | 0.0296s | -0.0030s | 0.908x | `[0.0403, 0.0306, 0.0348, 0.0279, 0.0295]` | `[0.0362, 0.0325, 0.0219, 0.0341, 0.0234]` |
| `cnf_training_extra/extra_cnf/cardinality_exactly_one_unsat_g10_s6_005.cnf` | 60 | 162 | UNSAT | 0.0307s | UNSAT | 0.0291s | -0.0016s | 0.949x | `[0.0303, 0.0287, 0.0338, 0.0301, 0.0305]` | `[0.0364, 0.0409, 0.0227, 0.0236, 0.0222]` |
| `cnf_training_extra/extra_cnf/cardinality_exactly_one_unsat_g12_s4_006.cnf` | 48 | 86 | UNSAT | 0.0355s | UNSAT | 0.0271s | -0.0084s | 0.762x | `[0.0302, 0.0457, 0.0351, 0.0380, 0.0284]` | `[0.0398, 0.0271, 0.0230, 0.0217, 0.0237]` |
| `cnf_training_extra/extra_cnf/cardinality_exactly_one_unsat_g3_s4_001.cnf` | 12 | 23 | UNSAT | 0.0283s | UNSAT | 0.0208s | -0.0076s | 0.732x | `[0.0283, 0.0288, 0.0270, 0.0285, 0.0291]` | `[0.0212, 0.0205, 0.0204, 0.0204, 0.0212]` |
| `cnf_training_extra/extra_cnf/cardinality_exactly_one_unsat_g4_s5_002.cnf` | 20 | 46 | UNSAT | 0.0376s | UNSAT | 0.0315s | -0.0061s | 0.838x | `[0.0286, 0.0351, 0.0479, 0.0439, 0.0325]` | `[0.0346, 0.0447, 0.0221, 0.0248, 0.0314]` |
| `cnf_training_extra/extra_cnf/cardinality_exactly_one_unsat_g6_s4_003.cnf` | 24 | 44 | UNSAT | 0.0355s | UNSAT | 0.0276s | -0.0079s | 0.777x | `[0.0339, 0.0301, 0.0340, 0.0330, 0.0466]` | `[0.0291, 0.0268, 0.0243, 0.0344, 0.0234]` |
| `cnf_training_extra/extra_cnf/cardinality_exactly_one_unsat_g8_s5_004.cnf` | 40 | 90 | UNSAT | 0.0460s | UNSAT | 0.0235s | -0.0225s | 0.511x | `[0.0423, 0.0351, 0.0526, 0.0528, 0.0470]` | `[0.0224, 0.0217, 0.0291, 0.0228, 0.0214]` |
| `cnf_training_extra/extra_cnf/equivalence_chain_len10_sat.cnf` | 10 | 20 | SAT | 0.0288s | SAT | 0.0273s | -0.0015s | 0.948x | `[0.0269, 0.0279, 0.0286, 0.0319, 0.0284]` | `[0.0383, 0.0242, 0.0249, 0.0259, 0.0229]` |
| `cnf_training_extra/extra_cnf/equivalence_chain_len10_unsat.cnf` | 10 | 20 | UNSAT | 0.0367s | UNSAT | 0.0292s | -0.0075s | 0.795x | `[0.0319, 0.0298, 0.0338, 0.0429, 0.0453]` | `[0.0230, 0.0252, 0.0493, 0.0235, 0.0251]` |
| `cnf_training_extra/extra_cnf/equivalence_chain_len120_sat.cnf` | 120 | 240 | SAT | 0.0367s | SAT | 0.0377s | +0.0010s | 1.026x | `[0.0424, 0.0341, 0.0288, 0.0415, 0.0368]` | `[0.0421, 0.0257, 0.0346, 0.0446, 0.0415]` |
| `cnf_training_extra/extra_cnf/equivalence_chain_len120_unsat.cnf` | 120 | 240 | UNSAT | 0.0351s | UNSAT | 0.0355s | +0.0004s | 1.011x | `[0.0321, 0.0320, 0.0427, 0.0280, 0.0406]` | `[0.0438, 0.0256, 0.0328, 0.0434, 0.0316]` |
| `cnf_training_extra/extra_cnf/equivalence_chain_len20_sat.cnf` | 20 | 40 | SAT | 0.0381s | SAT | 0.0270s | -0.0111s | 0.708x | `[0.0352, 0.0312, 0.0368, 0.0404, 0.0469]` | `[0.0260, 0.0243, 0.0241, 0.0366, 0.0241]` |
| `cnf_training_extra/extra_cnf/equivalence_chain_len20_unsat.cnf` | 20 | 40 | UNSAT | 0.0372s | UNSAT | 0.0293s | -0.0079s | 0.789x | `[0.0350, 0.0312, 0.0431, 0.0434, 0.0333]` | `[0.0248, 0.0356, 0.0349, 0.0238, 0.0276]` |
| `cnf_training_extra/extra_cnf/equivalence_chain_len40_sat.cnf` | 40 | 80 | SAT | 0.0464s | SAT | 0.0375s | -0.0090s | 0.807x | `[0.0529, 0.0375, 0.0523, 0.0485, 0.0410]` | `[0.0289, 0.0529, 0.0308, 0.0441, 0.0306]` |
| `cnf_training_extra/extra_cnf/equivalence_chain_len40_unsat.cnf` | 40 | 80 | UNSAT | 0.0324s | UNSAT | 0.0252s | -0.0072s | 0.778x | `[0.0380, 0.0344, 0.0307, 0.0288, 0.0300]` | `[0.0258, 0.0273, 0.0229, 0.0244, 0.0254]` |
| `cnf_training_extra/extra_cnf/equivalence_chain_len80_sat.cnf` | 80 | 160 | SAT | 0.0407s | SAT | 0.0299s | -0.0108s | 0.735x | `[0.0449, 0.0415, 0.0367, 0.0438, 0.0364]` | `[0.0253, 0.0291, 0.0317, 0.0232, 0.0403]` |
| `cnf_training_extra/extra_cnf/equivalence_chain_len80_unsat.cnf` | 80 | 160 | UNSAT | 0.0397s | UNSAT | 0.0308s | -0.0089s | 0.776x | `[0.0343, 0.0456, 0.0484, 0.0349, 0.0356]` | `[0.0402, 0.0247, 0.0258, 0.0332, 0.0303]` |
| `cnf_training_extra/extra_cnf/exact_random3sat_sat_n10_m49_008.cnf` | 10 | 49 | SAT | 0.0384s | SAT | 0.0243s | -0.0141s | 0.633x | `[0.0520, 0.0326, 0.0307, 0.0412, 0.0357]` | `[0.0252, 0.0244, 0.0237, 0.0225, 0.0259]` |
| `cnf_training_extra/extra_cnf/exact_random3sat_sat_n11_m40_017.cnf` | 11 | 40 | SAT | 0.0391s | SAT | 0.0267s | -0.0123s | 0.684x | `[0.0415, 0.0424, 0.0377, 0.0391, 0.0346]` | `[0.0252, 0.0322, 0.0271, 0.0267, 0.0224]` |
| `cnf_training_extra/extra_cnf/exact_random3sat_sat_n11_m46_001.cnf` | 11 | 46 | SAT | 0.0357s | SAT | 0.0296s | -0.0061s | 0.830x | `[0.0357, 0.0367, 0.0331, 0.0321, 0.0409]` | `[0.0338, 0.0251, 0.0323, 0.0248, 0.0320]` |
| `cnf_training_extra/extra_cnf/exact_random3sat_sat_n12_m43_012.cnf` | 12 | 43 | SAT | 0.0327s | SAT | 0.0270s | -0.0057s | 0.826x | `[0.0343, 0.0392, 0.0298, 0.0295, 0.0306]` | `[0.0240, 0.0320, 0.0228, 0.0218, 0.0344]` |
| `cnf_training_extra/extra_cnf/exact_random3sat_sat_n12_m47_006.cnf` | 12 | 47 | SAT | 0.0378s | SAT | 0.0255s | -0.0122s | 0.676x | `[0.0315, 0.0484, 0.0426, 0.0355, 0.0310]` | `[0.0229, 0.0226, 0.0232, 0.0250, 0.0341]` |
| `cnf_training_extra/extra_cnf/exact_random3sat_sat_n12_m47_013.cnf` | 12 | 47 | SAT | 0.0366s | SAT | 0.0297s | -0.0068s | 0.813x | `[0.0326, 0.0490, 0.0306, 0.0305, 0.0400]` | `[0.0409, 0.0265, 0.0227, 0.0223, 0.0362]` |
| `cnf_training_extra/extra_cnf/exact_random3sat_sat_n13_m47_011.cnf` | 13 | 47 | SAT | 0.0363s | SAT | 0.0326s | -0.0037s | 0.899x | `[0.0446, 0.0298, 0.0347, 0.0318, 0.0408]` | `[0.0240, 0.0353, 0.0388, 0.0398, 0.0254]` |
| `cnf_training_extra/extra_cnf/exact_random3sat_sat_n13_m64_004.cnf` | 13 | 64 | SAT | 0.0364s | SAT | 0.0302s | -0.0062s | 0.830x | `[0.0326, 0.0438, 0.0335, 0.0396, 0.0322]` | `[0.0279, 0.0468, 0.0248, 0.0270, 0.0244]` |
| `cnf_training_extra/extra_cnf/exact_random3sat_sat_n14_m50_015.cnf` | 14 | 50 | SAT | 0.0375s | SAT | 0.0300s | -0.0075s | 0.799x | `[0.0508, 0.0311, 0.0329, 0.0386, 0.0339]` | `[0.0274, 0.0231, 0.0202, 0.0450, 0.0340]` |
| `cnf_training_extra/extra_cnf/exact_random3sat_sat_n15_m68_014.cnf` | 15 | 68 | SAT | 0.0385s | SAT | 0.0256s | -0.0129s | 0.665x | `[0.0419, 0.0530, 0.0298, 0.0351, 0.0327]` | `[0.0367, 0.0217, 0.0235, 0.0225, 0.0235]` |
| `cnf_training_extra/extra_cnf/exact_random3sat_sat_n16_m62_016.cnf` | 16 | 62 | SAT | 0.0367s | SAT | 0.0277s | -0.0090s | 0.754x | `[0.0369, 0.0449, 0.0347, 0.0369, 0.0299]` | `[0.0391, 0.0291, 0.0265, 0.0214, 0.0221]` |
| `cnf_training_extra/extra_cnf/exact_random3sat_sat_n16_m72_003.cnf` | 16 | 72 | SAT | 0.0403s | SAT | 0.0293s | -0.0110s | 0.726x | `[0.0522, 0.0309, 0.0343, 0.0358, 0.0484]` | `[0.0258, 0.0292, 0.0347, 0.0231, 0.0337]` |
| `cnf_training_extra/extra_cnf/exact_random3sat_sat_n8_m31_007.cnf` | 8 | 31 | SAT | 0.0360s | SAT | 0.0344s | -0.0016s | 0.956x | `[0.0292, 0.0401, 0.0291, 0.0526, 0.0288]` | `[0.0215, 0.0414, 0.0392, 0.0268, 0.0430]` |
| `cnf_training_extra/extra_cnf/exact_random3sat_sat_n8_m31_009.cnf` | 8 | 31 | SAT | 0.0320s | SAT | 0.0273s | -0.0047s | 0.853x | `[0.0363, 0.0305, 0.0307, 0.0328, 0.0297]` | `[0.0313, 0.0242, 0.0238, 0.0358, 0.0213]` |
| `cnf_training_extra/extra_cnf/exact_random3sat_sat_n8_m36_002.cnf` | 8 | 36 | SAT | 0.0413s | SAT | 0.0260s | -0.0153s | 0.630x | `[0.0531, 0.0329, 0.0370, 0.0333, 0.0501]` | `[0.0250, 0.0274, 0.0226, 0.0279, 0.0272]` |
| `cnf_training_extra/extra_cnf/exact_random3sat_sat_n8_m36_005.cnf` | 8 | 36 | SAT | 0.0384s | SAT | 0.0259s | -0.0126s | 0.673x | `[0.0409, 0.0489, 0.0298, 0.0307, 0.0418]` | `[0.0241, 0.0222, 0.0241, 0.0323, 0.0267]` |
| `cnf_training_extra/extra_cnf/exact_random3sat_sat_n9_m32_018.cnf` | 9 | 32 | SAT | 0.0398s | SAT | 0.0292s | -0.0106s | 0.735x | `[0.0317, 0.0529, 0.0354, 0.0475, 0.0313]` | `[0.0240, 0.0334, 0.0224, 0.0320, 0.0342]` |
| `cnf_training_extra/extra_cnf/exact_random3sat_sat_n9_m38_010.cnf` | 9 | 38 | SAT | 0.0394s | SAT | 0.0276s | -0.0118s | 0.701x | `[0.0480, 0.0332, 0.0348, 0.0360, 0.0450]` | `[0.0287, 0.0230, 0.0316, 0.0319, 0.0229]` |
| `cnf_training_extra/extra_cnf/exact_random3sat_unsat_n10_m49_015.cnf` | 10 | 49 | UNSAT | 0.0387s | UNSAT | 0.0274s | -0.0113s | 0.708x | `[0.0464, 0.0370, 0.0315, 0.0447, 0.0339]` | `[0.0283, 0.0270, 0.0234, 0.0347, 0.0235]` |
| `cnf_training_extra/extra_cnf/exact_random3sat_unsat_n11_m54_012.cnf` | 11 | 54 | UNSAT | 0.0383s | UNSAT | 0.0254s | -0.0128s | 0.665x | `[0.0402, 0.0270, 0.0411, 0.0470, 0.0359]` | `[0.0348, 0.0223, 0.0227, 0.0269, 0.0204]` |
| `cnf_training_extra/extra_cnf/exact_random3sat_unsat_n12_m64_007.cnf` | 12 | 64 | UNSAT | 0.0372s | UNSAT | 0.0262s | -0.0110s | 0.705x | `[0.0432, 0.0299, 0.0413, 0.0308, 0.0405]` | `[0.0220, 0.0327, 0.0216, 0.0252, 0.0295]` |
| `cnf_training_extra/extra_cnf/exact_random3sat_unsat_n12_m64_013.cnf` | 12 | 64 | UNSAT | 0.0383s | UNSAT | 0.0309s | -0.0074s | 0.808x | `[0.0345, 0.0330, 0.0353, 0.0411, 0.0476]` | `[0.0299, 0.0255, 0.0420, 0.0337, 0.0236]` |
| `cnf_training_extra/extra_cnf/exact_random3sat_unsat_n13_m69_006.cnf` | 13 | 69 | UNSAT | 0.0428s | UNSAT | 0.0321s | -0.0107s | 0.750x | `[0.0305, 0.0432, 0.0472, 0.0504, 0.0428]` | `[0.0348, 0.0287, 0.0424, 0.0217, 0.0330]` |
| `cnf_training_extra/extra_cnf/exact_random3sat_unsat_n13_m69_010.cnf` | 13 | 69 | UNSAT | 0.0331s | UNSAT | 0.0316s | -0.0016s | 0.952x | `[0.0331, 0.0372, 0.0340, 0.0292, 0.0321]` | `[0.0296, 0.0320, 0.0331, 0.0238, 0.0393]` |
| `cnf_training_extra/extra_cnf/exact_random3sat_unsat_n14_m74_017.cnf` | 14 | 74 | UNSAT | 0.0391s | UNSAT | 0.0270s | -0.0121s | 0.690x | `[0.0329, 0.0372, 0.0404, 0.0500, 0.0350]` | `[0.0344, 0.0242, 0.0229, 0.0288, 0.0246]` |
| `cnf_training_extra/extra_cnf/exact_random3sat_unsat_n15_m68_011.cnf` | 15 | 68 | UNSAT | 0.0366s | UNSAT | 0.0325s | -0.0041s | 0.888x | `[0.0439, 0.0422, 0.0339, 0.0316, 0.0314]` | `[0.0280, 0.0242, 0.0352, 0.0391, 0.0359]` |
| `cnf_training_extra/extra_cnf/exact_random3sat_unsat_n15_m68_018.cnf` | 15 | 68 | UNSAT | 0.0430s | UNSAT | 0.0290s | -0.0140s | 0.675x | `[0.0478, 0.0340, 0.0432, 0.0470, 0.0429]` | `[0.0272, 0.0274, 0.0374, 0.0296, 0.0234]` |
| `cnf_training_extra/extra_cnf/exact_random3sat_unsat_n15_m80_014.cnf` | 15 | 80 | UNSAT | 0.0384s | UNSAT | 0.0339s | -0.0045s | 0.882x | `[0.0371, 0.0371, 0.0384, 0.0375, 0.0419]` | `[0.0405, 0.0244, 0.0307, 0.0357, 0.0379]` |
| `cnf_training_extra/extra_cnf/exact_random3sat_unsat_n16_m78_005.cnf` | 16 | 78 | UNSAT | 0.0388s | UNSAT | 0.0287s | -0.0101s | 0.739x | `[0.0361, 0.0394, 0.0349, 0.0448, 0.0390]` | `[0.0238, 0.0290, 0.0265, 0.0339, 0.0304]` |
| `cnf_training_extra/extra_cnf/exact_random3sat_unsat_n16_m78_008.cnf` | 16 | 78 | UNSAT | 0.0372s | UNSAT | 0.0310s | -0.0062s | 0.834x | `[0.0347, 0.0348, 0.0516, 0.0349, 0.0299]` | `[0.0281, 0.0276, 0.0375, 0.0256, 0.0363]` |
| `cnf_training_extra/extra_cnf/exact_random3sat_unsat_n16_m85_002.cnf` | 16 | 85 | UNSAT | 0.0360s | UNSAT | 0.0296s | -0.0064s | 0.822x | `[0.0320, 0.0379, 0.0467, 0.0297, 0.0336]` | `[0.0226, 0.0358, 0.0251, 0.0334, 0.0311]` |
| `cnf_training_extra/extra_cnf/exact_random3sat_unsat_n16_m85_003.cnf` | 16 | 85 | UNSAT | 0.0417s | UNSAT | 0.0321s | -0.0097s | 0.769x | `[0.0435, 0.0490, 0.0336, 0.0442, 0.0384]` | `[0.0377, 0.0239, 0.0350, 0.0394, 0.0243]` |
| `cnf_training_extra/extra_cnf/exact_random3sat_unsat_n8_m31_016.cnf` | 8 | 31 | UNSAT | 0.0397s | UNSAT | 0.0349s | -0.0048s | 0.878x | `[0.0460, 0.0400, 0.0408, 0.0429, 0.0289]` | `[0.0427, 0.0355, 0.0335, 0.0341, 0.0286]` |
| `cnf_training_extra/extra_cnf/exact_random3sat_unsat_n8_m34_009.cnf` | 8 | 34 | UNSAT | 0.0379s | UNSAT | 0.0346s | -0.0033s | 0.914x | `[0.0382, 0.0434, 0.0416, 0.0332, 0.0330]` | `[0.0351, 0.0348, 0.0336, 0.0352, 0.0342]` |
| `cnf_training_extra/extra_cnf/exact_random3sat_unsat_n9_m38_004.cnf` | 9 | 38 | UNSAT | 0.0339s | UNSAT | 0.0292s | -0.0047s | 0.862x | `[0.0389, 0.0356, 0.0299, 0.0295, 0.0358]` | `[0.0383, 0.0255, 0.0252, 0.0235, 0.0337]` |
| `cnf_training_extra/extra_cnf/exact_random3sat_unsat_n9_m44_001.cnf` | 9 | 44 | UNSAT | 0.0323s | UNSAT | 0.0314s | -0.0009s | 0.971x | `[0.0387, 0.0346, 0.0310, 0.0277, 0.0296]` | `[0.0483, 0.0400, 0.0209, 0.0233, 0.0244]` |
| `cnf_training_extra/extra_cnf/graphcolor_k3_complete_K4_unsat.cnf` | 12 | 34 | UNSAT | 0.0370s | UNSAT | 0.0272s | -0.0097s | 0.737x | `[0.0407, 0.0429, 0.0302, 0.0401, 0.0310]` | `[0.0352, 0.0335, 0.0211, 0.0209, 0.0256]` |
| `cnf_training_extra/extra_cnf/graphcolor_k3_complete_K5_unsat.cnf` | 15 | 50 | UNSAT | 0.0340s | UNSAT | 0.0253s | -0.0087s | 0.743x | `[0.0420, 0.0425, 0.0274, 0.0274, 0.0307]` | `[0.0263, 0.0231, 0.0215, 0.0214, 0.0339]` |
| `cnf_training_extra/extra_cnf/graphcolor_k3_complete_K6_unsat.cnf` | 18 | 69 | UNSAT | 0.0314s | UNSAT | 0.0329s | +0.0015s | 1.048x | `[0.0318, 0.0299, 0.0308, 0.0325, 0.0319]` | `[0.0349, 0.0337, 0.0381, 0.0242, 0.0335]` |
| `cnf_training_extra/extra_cnf/graphcolor_k3_planted_v12_e26_001.cnf` | 36 | 126 | SAT | 0.0400s | SAT | 0.0322s | -0.0078s | 0.805x | `[0.0331, 0.0342, 0.0504, 0.0470, 0.0353]` | `[0.0258, 0.0411, 0.0377, 0.0226, 0.0338]` |
| `cnf_training_extra/extra_cnf/graphcolor_k3_planted_v16_e35_002.cnf` | 48 | 169 | SAT | 0.0353s | SAT | 0.0350s | -0.0004s | 0.989x | `[0.0289, 0.0338, 0.0353, 0.0478, 0.0309]` | `[0.0361, 0.0377, 0.0350, 0.0293, 0.0365]` |
| `cnf_training_extra/extra_cnf/graphcolor_k3_planted_v20_e44_003.cnf` | 60 | 212 | SAT | 0.0350s | SAT | 0.0315s | -0.0035s | 0.899x | `[0.0335, 0.0361, 0.0372, 0.0304, 0.0377]` | `[0.0378, 0.0273, 0.0340, 0.0367, 0.0216]` |
| `cnf_training_extra/extra_cnf/graphcolor_k3_planted_v24_e53_004.cnf` | 72 | 255 | SAT | 0.0380s | SAT | 0.0304s | -0.0075s | 0.801x | `[0.0462, 0.0371, 0.0365, 0.0302, 0.0397]` | `[0.0275, 0.0246, 0.0278, 0.0368, 0.0353]` |
| `cnf_training_extra/extra_cnf/graphcolor_k3_planted_v30_e66_005.cnf` | 90 | 318 | SAT | 0.0401s | SAT | 0.0337s | -0.0064s | 0.841x | `[0.0353, 0.0416, 0.0493, 0.0386, 0.0357]` | `[0.0397, 0.0298, 0.0367, 0.0338, 0.0287]` |
| `cnf_training_extra/extra_cnf/graphcolor_k3_planted_v36_e79_006.cnf` | 108 | 381 | SAT | 0.0413s | SAT | 0.0344s | -0.0069s | 0.834x | `[0.0481, 0.0448, 0.0361, 0.0351, 0.0423]` | `[0.0458, 0.0249, 0.0312, 0.0341, 0.0361]` |
| `cnf_training_extra/extra_cnf/graphcolor_k3_planted_v42_e92_007.cnf` | 126 | 444 | SAT | 0.0376s | SAT | 0.0334s | -0.0042s | 0.887x | `[0.0365, 0.0395, 0.0349, 0.0368, 0.0404]` | `[0.0305, 0.0272, 0.0294, 0.0262, 0.0535]` |
| `cnf_training_extra/extra_cnf/graphcolor_k3_planted_v50_e110_008.cnf` | 150 | 530 | SAT | 0.0422s | SAT | 0.0323s | -0.0099s | 0.764x | `[0.0555, 0.0365, 0.0356, 0.0486, 0.0348]` | `[0.0306, 0.0280, 0.0360, 0.0401, 0.0266]` |
| `cnf_training_extra/extra_cnf/graphcolor_k3_planted_v60_e132_009.cnf` | 180 | 636 | SAT | 0.0418s | SAT | 0.0344s | -0.0074s | 0.823x | `[0.0324, 0.0354, 0.0560, 0.0474, 0.0376]` | `[0.0357, 0.0404, 0.0351, 0.0334, 0.0273]` |
| `cnf_training_extra/extra_cnf/graphcolor_k3_planted_v72_e158_010.cnf` | 216 | 762 | SAT | 0.0466s | SAT | 0.0369s | -0.0096s | 0.793x | `[0.0518, 0.0445, 0.0431, 0.0525, 0.0409]` | `[0.0357, 0.0376, 0.0289, 0.0433, 0.0391]` |
| `cnf_training_extra/extra_cnf/horn_chain_len12_sat.cnf` | 12 | 12 | SAT | 0.0326s | SAT | 0.0260s | -0.0066s | 0.796x | `[0.0309, 0.0300, 0.0322, 0.0410, 0.0290]` | `[0.0332, 0.0227, 0.0282, 0.0255, 0.0203]` |
| `cnf_training_extra/extra_cnf/horn_chain_len12_unsat.cnf` | 12 | 13 | UNSAT | 0.0439s | UNSAT | 0.0281s | -0.0157s | 0.641x | `[0.0358, 0.0513, 0.0454, 0.0438, 0.0430]` | `[0.0248, 0.0244, 0.0409, 0.0277, 0.0229]` |
| `cnf_training_extra/extra_cnf/horn_chain_len16_sat.cnf` | 16 | 16 | SAT | 0.0367s | SAT | 0.0334s | -0.0032s | 0.912x | `[0.0316, 0.0354, 0.0387, 0.0406, 0.0370]` | `[0.0256, 0.0431, 0.0302, 0.0391, 0.0292]` |
| `cnf_training_extra/extra_cnf/horn_chain_len16_unsat.cnf` | 16 | 17 | UNSAT | 0.0389s | UNSAT | 0.0285s | -0.0104s | 0.733x | `[0.0422, 0.0407, 0.0429, 0.0313, 0.0372]` | `[0.0289, 0.0322, 0.0239, 0.0250, 0.0324]` |
| `cnf_training_extra/extra_cnf/horn_chain_len24_sat.cnf` | 24 | 24 | SAT | 0.0440s | SAT | 0.0301s | -0.0139s | 0.684x | `[0.0460, 0.0496, 0.0325, 0.0465, 0.0456]` | `[0.0318, 0.0243, 0.0300, 0.0343, 0.0301]` |
| `cnf_training_extra/extra_cnf/horn_chain_len24_unsat.cnf` | 24 | 25 | UNSAT | 0.0411s | UNSAT | 0.0316s | -0.0095s | 0.769x | `[0.0297, 0.0477, 0.0441, 0.0456, 0.0385]` | `[0.0339, 0.0383, 0.0218, 0.0380, 0.0262]` |
| `cnf_training_extra/extra_cnf/horn_chain_len32_sat.cnf` | 32 | 32 | SAT | 0.0404s | SAT | 0.0318s | -0.0086s | 0.787x | `[0.0424, 0.0333, 0.0331, 0.0583, 0.0350]` | `[0.0267, 0.0314, 0.0459, 0.0234, 0.0316]` |
| `cnf_training_extra/extra_cnf/horn_chain_len32_unsat.cnf` | 32 | 33 | UNSAT | 0.0384s | UNSAT | 0.0276s | -0.0107s | 0.721x | `[0.0446, 0.0316, 0.0357, 0.0413, 0.0386]` | `[0.0256, 0.0350, 0.0233, 0.0213, 0.0331]` |
| `cnf_training_extra/extra_cnf/horn_chain_len48_sat.cnf` | 48 | 48 | SAT | 0.0413s | SAT | 0.0298s | -0.0114s | 0.723x | `[0.0447, 0.0415, 0.0378, 0.0304, 0.0518]` | `[0.0280, 0.0261, 0.0370, 0.0225, 0.0356]` |
| `cnf_training_extra/extra_cnf/horn_chain_len48_unsat.cnf` | 48 | 49 | UNSAT | 0.0382s | UNSAT | 0.0357s | -0.0025s | 0.935x | `[0.0357, 0.0391, 0.0348, 0.0468, 0.0344]` | `[0.0324, 0.0328, 0.0355, 0.0423, 0.0355]` |
| `cnf_training_extra/extra_cnf/horn_chain_len64_sat.cnf` | 64 | 64 | SAT | 0.0437s | SAT | 0.0330s | -0.0107s | 0.755x | `[0.0421, 0.0521, 0.0478, 0.0365, 0.0398]` | `[0.0398, 0.0297, 0.0349, 0.0350, 0.0254]` |
| `cnf_training_extra/extra_cnf/horn_chain_len64_unsat.cnf` | 64 | 65 | UNSAT | 0.0406s | UNSAT | 0.0300s | -0.0106s | 0.738x | `[0.0362, 0.0377, 0.0505, 0.0453, 0.0335]` | `[0.0230, 0.0326, 0.0308, 0.0368, 0.0267]` |
| `cnf_training_extra/extra_cnf/horn_chain_len8_sat.cnf` | 8 | 8 | SAT | 0.0423s | SAT | 0.0281s | -0.0143s | 0.663x | `[0.0389, 0.0345, 0.0401, 0.0501, 0.0481]` | `[0.0259, 0.0252, 0.0206, 0.0325, 0.0360]` |
| `cnf_training_extra/extra_cnf/horn_chain_len8_unsat.cnf` | 8 | 9 | UNSAT | 0.0392s | UNSAT | 0.0309s | -0.0083s | 0.789x | `[0.0449, 0.0326, 0.0378, 0.0396, 0.0410]` | `[0.0246, 0.0273, 0.0321, 0.0386, 0.0319]` |
| `cnf_training_extra/extra_cnf/nqueens_2x2_unsat.cnf` | 4 | 8 | UNSAT | 0.0419s | UNSAT | 0.0297s | -0.0123s | 0.707x | `[0.0319, 0.0403, 0.0484, 0.0453, 0.0439]` | `[0.0307, 0.0242, 0.0325, 0.0371, 0.0238]` |
| `cnf_training_extra/extra_cnf/nqueens_3x3_unsat.cnf` | 9 | 31 | UNSAT | 0.0340s | UNSAT | 0.0243s | -0.0097s | 0.714x | `[0.0300, 0.0314, 0.0419, 0.0348, 0.0318]` | `[0.0242, 0.0237, 0.0247, 0.0219, 0.0269]` |
| `cnf_training_extra/extra_cnf/nqueens_4x4_sat.cnf` | 16 | 80 | SAT | 0.0357s | SAT | 0.0349s | -0.0009s | 0.975x | `[0.0345, 0.0304, 0.0463, 0.0399, 0.0275]` | `[0.0398, 0.0353, 0.0253, 0.0363, 0.0375]` |
| `cnf_training_extra/extra_cnf/nqueens_5x5_sat.cnf` | 25 | 165 | SAT | 0.0496s | SAT | 0.0378s | -0.0118s | 0.762x | `[0.0453, 0.0404, 0.0481, 0.0679, 0.0464]` | `[0.0383, 0.0290, 0.0402, 0.0532, 0.0284]` |
| `cnf_training_extra/extra_cnf/nqueens_6x6_sat.cnf` | 36 | 296 | SAT | 0.0402s | SAT | 0.0362s | -0.0040s | 0.900x | `[0.0380, 0.0388, 0.0401, 0.0408, 0.0433]` | `[0.0347, 0.0298, 0.0334, 0.0403, 0.0428]` |
| `cnf_training_extra/extra_cnf/nqueens_7x7_sat.cnf` | 49 | 483 | SAT | 0.0493s | SAT | 0.0354s | -0.0139s | 0.719x | `[0.0477, 0.0525, 0.0600, 0.0430, 0.0434]` | `[0.0313, 0.0379, 0.0320, 0.0448, 0.0313]` |
| `cnf_training_extra/extra_cnf/nqueens_8x8_sat.cnf` | 64 | 736 | SAT | 0.0413s | SAT | 0.0341s | -0.0072s | 0.826x | `[0.0401, 0.0408, 0.0470, 0.0357, 0.0428]` | `[0.0303, 0.0300, 0.0323, 0.0394, 0.0385]` |
| `cnf_training_extra/extra_cnf/nqueens_9x9_sat.cnf` | 81 | 1065 | SAT | 0.0480s | SAT | 0.0418s | -0.0063s | 0.870x | `[0.0507, 0.0453, 0.0486, 0.0480, 0.0475]` | `[0.0327, 0.0487, 0.0460, 0.0428, 0.0386]` |
| `cnf_training_extra/extra_cnf/pigeonhole_php_10_into_9.cnf` | 90 | 415 | UNSAT | 0.0385s | UNSAT | 0.0316s | -0.0069s | 0.822x | `[0.0361, 0.0365, 0.0328, 0.0501, 0.0370]` | `[0.0305, 0.0266, 0.0444, 0.0283, 0.0283]` |
| `cnf_training_extra/extra_cnf/pigeonhole_php_4_into_3.cnf` | 12 | 22 | UNSAT | 0.0432s | UNSAT | 0.0323s | -0.0109s | 0.748x | `[0.0465, 0.0336, 0.0562, 0.0410, 0.0388]` | `[0.0249, 0.0444, 0.0231, 0.0365, 0.0327]` |
| `cnf_training_extra/extra_cnf/pigeonhole_php_5_into_4.cnf` | 20 | 45 | UNSAT | 0.0362s | UNSAT | 0.0324s | -0.0038s | 0.894x | `[0.0390, 0.0344, 0.0435, 0.0335, 0.0308]` | `[0.0287, 0.0404, 0.0273, 0.0361, 0.0295]` |
| `cnf_training_extra/extra_cnf/pigeonhole_php_6_into_5.cnf` | 30 | 81 | UNSAT | 0.0431s | UNSAT | 0.0349s | -0.0081s | 0.811x | `[0.0420, 0.0363, 0.0499, 0.0469, 0.0403]` | `[0.0334, 0.0292, 0.0403, 0.0385, 0.0332]` |
| `cnf_training_extra/extra_cnf/pigeonhole_php_7_into_6.cnf` | 42 | 133 | UNSAT | 0.0404s | UNSAT | 0.0329s | -0.0075s | 0.814x | `[0.0509, 0.0462, 0.0427, 0.0320, 0.0304]` | `[0.0413, 0.0233, 0.0312, 0.0370, 0.0319]` |
| `cnf_training_extra/extra_cnf/pigeonhole_php_8_into_7.cnf` | 56 | 204 | UNSAT | 0.0484s | UNSAT | 0.0331s | -0.0153s | 0.683x | `[0.0523, 0.0477, 0.0420, 0.0449, 0.0552]` | `[0.0267, 0.0435, 0.0267, 0.0402, 0.0284]` |
| `cnf_training_extra/extra_cnf/pigeonhole_php_9_into_8.cnf` | 72 | 297 | UNSAT | 0.0397s | UNSAT | 0.0339s | -0.0058s | 0.854x | `[0.0335, 0.0440, 0.0321, 0.0342, 0.0547]` | `[0.0437, 0.0366, 0.0246, 0.0269, 0.0379]` |
| `cnf_training_extra/extra_cnf/planted3sat_n20_m85_001.cnf` | 20 | 85 | SAT | 0.0372s | SAT | 0.0311s | -0.0060s | 0.838x | `[0.0489, 0.0407, 0.0322, 0.0311, 0.0329]` | `[0.0251, 0.0393, 0.0241, 0.0292, 0.0379]` |
| `cnf_training_extra/extra_cnf/planted3sat_n20_m85_002.cnf` | 20 | 85 | SAT | 0.0369s | SAT | 0.0298s | -0.0072s | 0.806x | `[0.0431, 0.0314, 0.0366, 0.0373, 0.0363]` | `[0.0227, 0.0279, 0.0327, 0.0308, 0.0347]` |
| `cnf_training_extra/extra_cnf/planted3sat_n20_m85_003.cnf` | 20 | 85 | SAT | 0.0416s | SAT | 0.0268s | -0.0148s | 0.644x | `[0.0436, 0.0436, 0.0424, 0.0318, 0.0466]` | `[0.0230, 0.0332, 0.0237, 0.0243, 0.0296]` |
| `cnf_training_extra/extra_cnf/planted3sat_n20_m85_004.cnf` | 20 | 85 | SAT | 0.0377s | SAT | 0.0323s | -0.0055s | 0.855x | `[0.0441, 0.0350, 0.0337, 0.0330, 0.0429]` | `[0.0388, 0.0406, 0.0350, 0.0249, 0.0221]` |
| `cnf_training_extra/extra_cnf/planted3sat_n20_m85_005.cnf` | 20 | 85 | SAT | 0.0411s | SAT | 0.0316s | -0.0096s | 0.767x | `[0.0540, 0.0382, 0.0445, 0.0370, 0.0321]` | `[0.0300, 0.0267, 0.0260, 0.0388, 0.0363]` |
| `cnf_training_extra/extra_cnf/planted3sat_n20_m85_006.cnf` | 20 | 85 | SAT | 0.0366s | SAT | 0.0297s | -0.0068s | 0.813x | `[0.0357, 0.0369, 0.0387, 0.0320, 0.0395]` | `[0.0234, 0.0337, 0.0301, 0.0349, 0.0266]` |
| `cnf_training_extra/extra_cnf/planted3sat_n20_m85_007.cnf` | 20 | 85 | SAT | 0.0444s | SAT | 0.0309s | -0.0136s | 0.694x | `[0.0326, 0.0504, 0.0481, 0.0436, 0.0475]` | `[0.0390, 0.0270, 0.0232, 0.0431, 0.0220]` |
| `cnf_training_extra/extra_cnf/planted3sat_n20_m85_008.cnf` | 20 | 85 | SAT | 0.0458s | SAT | 0.0340s | -0.0118s | 0.742x | `[0.0352, 0.0580, 0.0589, 0.0410, 0.0360]` | `[0.0257, 0.0383, 0.0449, 0.0306, 0.0304]` |
| `cnf_training_extra/extra_cnf/planted3sat_n20_m85_009.cnf` | 20 | 85 | SAT | 0.0421s | SAT | 0.0317s | -0.0104s | 0.753x | `[0.0382, 0.0454, 0.0471, 0.0427, 0.0370]` | `[0.0303, 0.0276, 0.0403, 0.0308, 0.0294]` |
| `cnf_training_extra/extra_cnf/planted3sat_n20_m85_010.cnf` | 20 | 85 | SAT | 0.0416s | SAT | 0.0343s | -0.0074s | 0.823x | `[0.0532, 0.0400, 0.0366, 0.0354, 0.0428]` | `[0.0294, 0.0305, 0.0330, 0.0410, 0.0374]` |
| `cnf_training_extra/extra_cnf/planted3sat_n30_m128_001.cnf` | 30 | 128 | SAT | 0.0408s | SAT | 0.0404s | -0.0004s | 0.989x | `[0.0319, 0.0348, 0.0472, 0.0460, 0.0441]` | `[0.0482, 0.0434, 0.0432, 0.0300, 0.0368]` |
| `cnf_training_extra/extra_cnf/planted3sat_n30_m128_002.cnf` | 30 | 128 | SAT | 0.0425s | SAT | 0.0309s | -0.0115s | 0.728x | `[0.0310, 0.0467, 0.0387, 0.0485, 0.0476]` | `[0.0312, 0.0297, 0.0389, 0.0278, 0.0270]` |
| `cnf_training_extra/extra_cnf/planted3sat_n30_m128_003.cnf` | 30 | 128 | SAT | 0.0439s | SAT | 0.0312s | -0.0127s | 0.711x | `[0.0542, 0.0473, 0.0409, 0.0384, 0.0384]` | `[0.0260, 0.0250, 0.0376, 0.0391, 0.0283]` |
| `cnf_training_extra/extra_cnf/planted3sat_n30_m128_004.cnf` | 30 | 128 | SAT | 0.0394s | SAT | 0.0305s | -0.0089s | 0.773x | `[0.0357, 0.0496, 0.0341, 0.0334, 0.0441]` | `[0.0297, 0.0353, 0.0269, 0.0291, 0.0313]` |
| `cnf_training_extra/extra_cnf/planted3sat_n30_m128_005.cnf` | 30 | 128 | SAT | 0.0430s | SAT | 0.0332s | -0.0098s | 0.773x | `[0.0388, 0.0530, 0.0443, 0.0447, 0.0342]` | `[0.0369, 0.0436, 0.0255, 0.0360, 0.0241]` |
| `cnf_training_extra/extra_cnf/planted3sat_n30_m128_006.cnf` | 30 | 128 | SAT | 0.0421s | SAT | 0.0362s | -0.0059s | 0.860x | `[0.0371, 0.0514, 0.0433, 0.0355, 0.0430]` | `[0.0429, 0.0377, 0.0301, 0.0411, 0.0289]` |
| `cnf_training_extra/extra_cnf/planted3sat_n30_m128_007.cnf` | 30 | 128 | SAT | 0.0381s | SAT | 0.0284s | -0.0097s | 0.746x | `[0.0360, 0.0398, 0.0341, 0.0395, 0.0412]` | `[0.0281, 0.0277, 0.0305, 0.0287, 0.0271]` |
| `cnf_training_extra/extra_cnf/planted3sat_n30_m128_008.cnf` | 30 | 128 | SAT | 0.0402s | SAT | 0.0372s | -0.0029s | 0.927x | `[0.0358, 0.0341, 0.0454, 0.0402, 0.0453]` | `[0.0440, 0.0369, 0.0377, 0.0386, 0.0289]` |
| `cnf_training_extra/extra_cnf/planted3sat_n30_m128_009.cnf` | 30 | 128 | SAT | 0.0409s | SAT | 0.0356s | -0.0053s | 0.870x | `[0.0410, 0.0467, 0.0343, 0.0459, 0.0367]` | `[0.0344, 0.0311, 0.0366, 0.0394, 0.0366]` |
| `cnf_training_extra/extra_cnf/planted3sat_n30_m128_010.cnf` | 30 | 128 | SAT | 0.0404s | SAT | 0.0356s | -0.0047s | 0.883x | `[0.0324, 0.0473, 0.0318, 0.0465, 0.0438]` | `[0.0450, 0.0306, 0.0245, 0.0394, 0.0388]` |
| `cnf_training_extra/extra_cnf/planted3sat_n40_m170_001.cnf` | 40 | 170 | SAT | 0.0385s | SAT | 0.0354s | -0.0030s | 0.922x | `[0.0360, 0.0423, 0.0354, 0.0403, 0.0383]` | `[0.0386, 0.0385, 0.0315, 0.0287, 0.0399]` |
| `cnf_training_extra/extra_cnf/planted3sat_n40_m170_002.cnf` | 40 | 170 | SAT | 0.0422s | SAT | 0.0370s | -0.0052s | 0.877x | `[0.0566, 0.0390, 0.0383, 0.0396, 0.0374]` | `[0.0485, 0.0334, 0.0402, 0.0388, 0.0241]` |
| `cnf_training_extra/extra_cnf/planted3sat_n40_m170_003.cnf` | 40 | 170 | SAT | 0.0419s | SAT | 0.0313s | -0.0107s | 0.746x | `[0.0379, 0.0358, 0.0506, 0.0473, 0.0380]` | `[0.0320, 0.0253, 0.0398, 0.0307, 0.0286]` |
| `cnf_training_extra/extra_cnf/planted3sat_n40_m170_004.cnf` | 40 | 170 | SAT | 0.0441s | SAT | 0.0318s | -0.0123s | 0.722x | `[0.0494, 0.0514, 0.0325, 0.0402, 0.0468]` | `[0.0265, 0.0393, 0.0366, 0.0283, 0.0284]` |
| `cnf_training_extra/extra_cnf/planted3sat_n40_m170_005.cnf` | 40 | 170 | SAT | 0.0442s | SAT | 0.0332s | -0.0109s | 0.752x | `[0.0538, 0.0368, 0.0473, 0.0431, 0.0398]` | `[0.0380, 0.0296, 0.0263, 0.0428, 0.0294]` |
| `cnf_training_extra/extra_cnf/planted3sat_n40_m170_006.cnf` | 40 | 170 | SAT | 0.0408s | SAT | 0.0317s | -0.0091s | 0.777x | `[0.0532, 0.0402, 0.0337, 0.0429, 0.0341]` | `[0.0286, 0.0359, 0.0264, 0.0250, 0.0427]` |
| `cnf_training_extra/extra_cnf/planted3sat_n40_m170_007.cnf` | 40 | 170 | SAT | 0.0389s | SAT | 0.0330s | -0.0059s | 0.849x | `[0.0342, 0.0345, 0.0433, 0.0391, 0.0433]` | `[0.0319, 0.0256, 0.0363, 0.0364, 0.0348]` |
| `cnf_training_extra/extra_cnf/planted3sat_n40_m170_008.cnf` | 40 | 170 | SAT | 0.0404s | SAT | 0.0337s | -0.0068s | 0.833x | `[0.0343, 0.0350, 0.0399, 0.0415, 0.0514]` | `[0.0313, 0.0333, 0.0330, 0.0323, 0.0386]` |
| `cnf_training_extra/extra_cnf/planted3sat_n40_m170_009.cnf` | 40 | 170 | SAT | 0.0401s | SAT | 0.0337s | -0.0064s | 0.839x | `[0.0489, 0.0375, 0.0428, 0.0363, 0.0352]` | `[0.0296, 0.0357, 0.0296, 0.0363, 0.0373]` |
| `cnf_training_extra/extra_cnf/planted3sat_n40_m170_010.cnf` | 40 | 170 | SAT | 0.0360s | SAT | 0.0323s | -0.0037s | 0.896x | `[0.0377, 0.0456, 0.0336, 0.0311, 0.0318]` | `[0.0249, 0.0241, 0.0236, 0.0361, 0.0527]` |
| `cnf_training_extra/extra_cnf/planted3sat_n60_m255_001.cnf` | 60 | 255 | SAT | 0.0459s | SAT | 0.0288s | -0.0171s | 0.627x | `[0.0415, 0.0592, 0.0472, 0.0471, 0.0345]` | `[0.0256, 0.0251, 0.0429, 0.0251, 0.0254]` |
| `cnf_training_extra/extra_cnf/planted3sat_n60_m255_002.cnf` | 60 | 255 | SAT | 0.0398s | SAT | 0.0279s | -0.0119s | 0.702x | `[0.0498, 0.0469, 0.0343, 0.0357, 0.0324]` | `[0.0259, 0.0253, 0.0255, 0.0252, 0.0378]` |
| `cnf_training_extra/extra_cnf/planted3sat_n60_m255_003.cnf` | 60 | 255 | SAT | 0.0422s | SAT | 0.0342s | -0.0080s | 0.810x | `[0.0475, 0.0431, 0.0365, 0.0450, 0.0387]` | `[0.0357, 0.0393, 0.0323, 0.0272, 0.0363]` |
| `cnf_training_extra/extra_cnf/planted3sat_n60_m255_004.cnf` | 60 | 255 | SAT | 0.0438s | SAT | 0.0381s | -0.0058s | 0.868x | `[0.0492, 0.0416, 0.0490, 0.0375, 0.0420]` | `[0.0300, 0.0290, 0.0386, 0.0486, 0.0441]` |
| `cnf_training_extra/extra_cnf/planted3sat_n60_m255_005.cnf` | 60 | 255 | SAT | 0.0430s | SAT | 0.0333s | -0.0097s | 0.775x | `[0.0376, 0.0454, 0.0409, 0.0354, 0.0558]` | `[0.0414, 0.0336, 0.0398, 0.0261, 0.0257]` |
| `cnf_training_extra/extra_cnf/planted3sat_n60_m255_006.cnf` | 60 | 255 | SAT | 0.0402s | SAT | 0.0373s | -0.0029s | 0.927x | `[0.0474, 0.0337, 0.0347, 0.0465, 0.0388]` | `[0.0369, 0.0238, 0.0457, 0.0387, 0.0414]` |
| `cnf_training_extra/extra_cnf/planted3sat_n60_m255_007.cnf` | 60 | 255 | SAT | 0.0431s | SAT | 0.0334s | -0.0097s | 0.774x | `[0.0446, 0.0517, 0.0431, 0.0403, 0.0358]` | `[0.0347, 0.0257, 0.0453, 0.0371, 0.0240]` |
| `cnf_training_extra/extra_cnf/planted3sat_n60_m255_008.cnf` | 60 | 255 | SAT | 0.0413s | SAT | 0.0353s | -0.0061s | 0.853x | `[0.0402, 0.0379, 0.0428, 0.0500, 0.0356]` | `[0.0275, 0.0256, 0.0399, 0.0393, 0.0439]` |
| `cnf_training_extra/extra_cnf/planted3sat_n80_m340_001.cnf` | 80 | 340 | SAT | 0.0605s | SAT | 0.0376s | -0.0229s | 0.621x | `[0.0581, 0.0477, 0.0657, 0.0709, 0.0598]` | `[0.0379, 0.0360, 0.0336, 0.0375, 0.0429]` |
| `cnf_training_extra/extra_cnf/planted3sat_n80_m340_002.cnf` | 80 | 340 | SAT | 0.0421s | SAT | 0.0307s | -0.0114s | 0.729x | `[0.0393, 0.0402, 0.0400, 0.0512, 0.0401]` | `[0.0298, 0.0306, 0.0315, 0.0322, 0.0295]` |
| `cnf_training_extra/extra_cnf/planted3sat_n80_m340_003.cnf` | 80 | 340 | SAT | 0.0454s | SAT | 0.0349s | -0.0105s | 0.769x | `[0.0377, 0.0372, 0.0561, 0.0485, 0.0475]` | `[0.0517, 0.0272, 0.0274, 0.0417, 0.0267]` |
| `cnf_training_extra/extra_cnf/planted3sat_n80_m340_004.cnf` | 80 | 340 | SAT | 0.0426s | SAT | 0.0334s | -0.0092s | 0.784x | `[0.0463, 0.0475, 0.0464, 0.0376, 0.0353]` | `[0.0492, 0.0259, 0.0388, 0.0266, 0.0266]` |
| `cnf_training_extra/extra_cnf/planted3sat_n80_m340_005.cnf` | 80 | 340 | SAT | 0.0365s | SAT | 0.0333s | -0.0032s | 0.913x | `[0.0339, 0.0429, 0.0380, 0.0336, 0.0341]` | `[0.0311, 0.0263, 0.0413, 0.0232, 0.0446]` |
| `cnf_training_extra/extra_cnf/planted3sat_n80_m340_006.cnf` | 80 | 340 | SAT | 0.0395s | SAT | 0.0369s | -0.0025s | 0.935x | `[0.0413, 0.0473, 0.0359, 0.0359, 0.0368]` | `[0.0385, 0.0283, 0.0389, 0.0296, 0.0492]` |
| `cnf_training_extra/extra_cnf/xor_parity_sat_n18_eq18_w3_001.cnf` | 18 | 72 | SAT | 0.0430s | SAT | 0.0372s | -0.0058s | 0.865x | `[0.0483, 0.0401, 0.0450, 0.0440, 0.0377]` | `[0.0344, 0.0392, 0.0443, 0.0379, 0.0301]` |
| `cnf_training_extra/extra_cnf/xor_parity_sat_n24_eq24_w3_002.cnf` | 24 | 96 | SAT | 0.0445s | SAT | 0.0349s | -0.0096s | 0.785x | `[0.0404, 0.0487, 0.0469, 0.0467, 0.0398]` | `[0.0362, 0.0291, 0.0365, 0.0456, 0.0273]` |
| `cnf_training_extra/extra_cnf/xor_parity_sat_n30_eq30_w3_003.cnf` | 30 | 120 | SAT | 0.0375s | SAT | 0.0316s | -0.0059s | 0.843x | `[0.0373, 0.0466, 0.0323, 0.0355, 0.0356]` | `[0.0397, 0.0246, 0.0296, 0.0292, 0.0348]` |
| `cnf_training_extra/extra_cnf/xor_parity_sat_n32_eq20_w4_007.cnf` | 32 | 160 | SAT | 0.0468s | SAT | 0.0365s | -0.0103s | 0.780x | `[0.0525, 0.0364, 0.0469, 0.0474, 0.0507]` | `[0.0458, 0.0367, 0.0438, 0.0296, 0.0264]` |
| `cnf_training_extra/extra_cnf/xor_parity_sat_n40_eq35_w3_004.cnf` | 40 | 140 | SAT | 0.0342s | SAT | 0.0357s | +0.0016s | 1.045x | `[0.0338, 0.0337, 0.0340, 0.0363, 0.0331]` | `[0.0436, 0.0308, 0.0374, 0.0403, 0.0265]` |
| `cnf_training_extra/extra_cnf/xor_parity_sat_n48_eq28_w4_008.cnf` | 48 | 224 | SAT | 0.0389s | SAT | 0.0409s | +0.0019s | 1.049x | `[0.0347, 0.0326, 0.0339, 0.0382, 0.0551]` | `[0.0488, 0.0451, 0.0503, 0.0325, 0.0276]` |
| `cnf_training_extra/extra_cnf/xor_parity_sat_n60_eq45_w3_005.cnf` | 60 | 180 | SAT | 0.0395s | SAT | 0.0322s | -0.0073s | 0.816x | `[0.0388, 0.0413, 0.0367, 0.0364, 0.0443]` | `[0.0274, 0.0301, 0.0320, 0.0293, 0.0424]` |
| `cnf_training_extra/extra_cnf/xor_parity_sat_n80_eq55_w3_006.cnf` | 80 | 220 | SAT | 0.0452s | SAT | 0.0359s | -0.0093s | 0.794x | `[0.0456, 0.0451, 0.0497, 0.0433, 0.0424]` | `[0.0263, 0.0355, 0.0475, 0.0441, 0.0260]` |
| `cnf_training_extra/extra_cnf/xor_parity_unsat_n18_eq12_w3_001.cnf` | 18 | 48 | UNSAT | 0.0409s | UNSAT | 0.0360s | -0.0049s | 0.881x | `[0.0369, 0.0443, 0.0298, 0.0436, 0.0498]` | `[0.0389, 0.0319, 0.0374, 0.0430, 0.0288]` |
| `cnf_training_extra/extra_cnf/xor_parity_unsat_n24_eq16_w3_002.cnf` | 24 | 64 | UNSAT | 0.0409s | UNSAT | 0.0307s | -0.0102s | 0.752x | `[0.0381, 0.0451, 0.0348, 0.0403, 0.0461]` | `[0.0282, 0.0441, 0.0265, 0.0293, 0.0256]` |
| `cnf_training_extra/extra_cnf/xor_parity_unsat_n30_eq20_w3_003.cnf` | 30 | 80 | UNSAT | 0.0517s | UNSAT | 0.0294s | -0.0223s | 0.569x | `[0.0544, 0.0518, 0.0570, 0.0474, 0.0480]` | `[0.0260, 0.0357, 0.0270, 0.0276, 0.0307]` |
| `cnf_training_extra/extra_cnf/xor_parity_unsat_n32_eq18_w4_006.cnf` | 32 | 144 | UNSAT | 0.0484s | UNSAT | 0.0310s | -0.0174s | 0.641x | `[0.0373, 0.0494, 0.0524, 0.0403, 0.0624]` | `[0.0282, 0.0292, 0.0252, 0.0336, 0.0387]` |
| `cnf_training_extra/extra_cnf/xor_parity_unsat_n40_eq24_w3_004.cnf` | 40 | 96 | UNSAT | 0.0360s | UNSAT | 0.0388s | +0.0028s | 1.077x | `[0.0435, 0.0328, 0.0368, 0.0293, 0.0376]` | `[0.0403, 0.0498, 0.0297, 0.0470, 0.0270]` |
| `cnf_training_extra/extra_cnf/xor_parity_unsat_n60_eq32_w3_005.cnf` | 60 | 128 | UNSAT | 0.0443s | UNSAT | 0.0350s | -0.0093s | 0.789x | `[0.0496, 0.0389, 0.0440, 0.0454, 0.0438]` | `[0.0408, 0.0303, 0.0419, 0.0377, 0.0244]` |
| `large/test_1.cnf` | 373 | 811 | SAT | 0.0508s | SAT | 0.0469s | -0.0039s | 0.924x | `[0.0516, 0.0529, 0.0557, 0.0432, 0.0504]` | `[0.0515, 0.0391, 0.0570, 0.0496, 0.0374]` |
| `large/test_10.cnf` | 229 | 1280 | UNSAT | 1.7902s | UNSAT | 0.9275s | -0.8627s | 0.518x | `[1.9453, 1.8450, 1.7024, 1.7622, 1.6961]` | `[0.8987, 0.9398, 0.9238, 0.9576, 0.9178]` |
| `large/test_2.cnf` | 319 | 573 | SAT | 0.0458s | SAT | 0.0410s | -0.0047s | 0.896x | `[0.0467, 0.0448, 0.0549, 0.0425, 0.0401]` | `[0.0503, 0.0312, 0.0366, 0.0380, 0.0490]` |
| `large/test_3.cnf` | 227 | 1460 | UNSAT | 0.3068s | UNSAT | 0.3274s | +0.0206s | 1.067x | `[0.2843, 0.3147, 0.2968, 0.3032, 0.3349]` | `[0.2962, 0.3301, 0.2862, 0.3606, 0.3638]` |
| `large/test_4.cnf` | 219 | 1363 | UNSAT | 0.2751s | UNSAT | 0.2487s | -0.0265s | 0.904x | `[0.3005, 0.2625, 0.2733, 0.2853, 0.2541]` | `[0.2473, 0.2446, 0.2682, 0.2521, 0.2311]` |
| `large/test_5.cnf` | 244 | 772 | SAT | 0.0490s | SAT | 0.0375s | -0.0115s | 0.765x | `[0.0384, 0.0386, 0.0641, 0.0506, 0.0531]` | `[0.0389, 0.0351, 0.0412, 0.0298, 0.0421]` |
| `large/test_6.cnf` | 271 | 1393 | UNSAT | 11.8183s | UNSAT | 3.4038s | -8.4145s | 0.288x | `[11.3603, 11.8526, 11.9124, 12.0726, 11.8935]` | `[3.4476, 3.2953, 3.4640, 3.4150, 3.3973]` |
| `large/test_7.cnf` | 389 | 863 | SAT | 0.0510s | SAT | 0.0407s | -0.0103s | 0.798x | `[0.0514, 0.0541, 0.0391, 0.0573, 0.0533]` | `[0.0660, 0.0393, 0.0309, 0.0325, 0.0349]` |
| `large/test_8.cnf` | 298 | 1210 | SAT | 0.2833s | SAT | 1.6251s | +1.3418s | 5.736x | `[0.2937, 0.2690, 0.2716, 0.2882, 0.2941]` | `[1.6611, 1.6905, 1.5689, 1.6001, 1.6050]` |
| `large/test_9.cnf` | 365 | 969 | SAT | 0.0473s | SAT | 0.0392s | -0.0081s | 0.828x | `[0.0404, 0.0564, 0.0576, 0.0405, 0.0417]` | `[0.0316, 0.0476, 0.0341, 0.0520, 0.0307]` |
| `medium/test_1.cnf` | 63 | 835 | UNSAT | 0.0461s | UNSAT | 0.0333s | -0.0128s | 0.722x | `[0.0455, 0.0352, 0.0365, 0.0536, 0.0597]` | `[0.0298, 0.0354, 0.0406, 0.0280, 0.0325]` |
| `medium/test_10.cnf` | 68 | 822 | UNSAT | 0.0402s | UNSAT | 0.0362s | -0.0040s | 0.901x | `[0.0413, 0.0354, 0.0517, 0.0342, 0.0384]` | `[0.0424, 0.0386, 0.0252, 0.0359, 0.0389]` |
| `medium/test_2.cnf` | 69 | 352 | UNSAT | 0.0419s | UNSAT | 0.0313s | -0.0106s | 0.746x | `[0.0365, 0.0491, 0.0491, 0.0350, 0.0399]` | `[0.0323, 0.0287, 0.0278, 0.0273, 0.0404]` |
| `medium/test_3.cnf` | 172 | 774 | UNSAT | 0.6643s | UNSAT | 0.4775s | -0.1868s | 0.719x | `[0.6501, 0.6658, 0.6738, 0.6518, 0.6798]` | `[0.4638, 0.4611, 0.5104, 0.4912, 0.4611]` |
| `medium/test_4.cnf` | 191 | 886 | UNSAT | 1.6919s | UNSAT | 0.8573s | -0.8346s | 0.507x | `[1.6824, 1.6900, 1.6760, 1.7153, 1.6958]` | `[0.8589, 0.8757, 0.8225, 0.8692, 0.8600]` |
| `medium/test_5.cnf` | 55 | 713 | UNSAT | 0.0419s | UNSAT | 0.0386s | -0.0034s | 0.920x | `[0.0478, 0.0488, 0.0350, 0.0324, 0.0457]` | `[0.0487, 0.0403, 0.0379, 0.0260, 0.0400]` |
| `medium/test_6.cnf` | 61 | 512 | UNSAT | 0.0455s | UNSAT | 0.0338s | -0.0117s | 0.743x | `[0.0358, 0.0511, 0.0511, 0.0348, 0.0549]` | `[0.0422, 0.0355, 0.0322, 0.0268, 0.0323]` |
| `medium/test_7.cnf` | 75 | 562 | UNSAT | 0.0467s | UNSAT | 0.0306s | -0.0161s | 0.656x | `[0.0464, 0.0533, 0.0363, 0.0494, 0.0479]` | `[0.0389, 0.0341, 0.0265, 0.0263, 0.0274]` |
| `medium/test_8.cnf` | 130 | 333 | SAT | 0.0376s | SAT | 0.0277s | -0.0099s | 0.737x | `[0.0436, 0.0467, 0.0320, 0.0329, 0.0329]` | `[0.0383, 0.0248, 0.0253, 0.0251, 0.0251]` |
| `medium/test_9.cnf` | 138 | 379 | SAT | 0.0434s | SAT | 0.0276s | -0.0158s | 0.637x | `[0.0474, 0.0453, 0.0332, 0.0463, 0.0448]` | `[0.0255, 0.0248, 0.0252, 0.0392, 0.0236]` |
| `satlib_more/aim-100-1_6-no-1.cnf` | 100 | 160 | UNSAT | 0.0324s | UNSAT | 0.0287s | -0.0037s | 0.885x | `[0.0304, 0.0302, 0.0304, 0.0392, 0.0318]` | `[0.0232, 0.0356, 0.0237, 0.0378, 0.0232]` |
| `satlib_more/aim-100-1_6-no-2.cnf` | 100 | 160 | UNSAT | 0.0396s | UNSAT | 0.0305s | -0.0091s | 0.771x | `[0.0421, 0.0314, 0.0326, 0.0324, 0.0595]` | `[0.0244, 0.0249, 0.0250, 0.0442, 0.0341]` |
| `satlib_more/aim-100-1_6-yes1-1.cnf` | 100 | 160 | SAT | 0.0385s | SAT | 0.0374s | -0.0011s | 0.971x | `[0.0363, 0.0381, 0.0493, 0.0326, 0.0363]` | `[0.0451, 0.0264, 0.0398, 0.0372, 0.0385]` |
| `satlib_more/aim-100-1_6-yes1-2.cnf` | 100 | 160 | SAT | 0.0419s | SAT | 0.0373s | -0.0046s | 0.890x | `[0.0365, 0.0550, 0.0326, 0.0372, 0.0481]` | `[0.0315, 0.0374, 0.0392, 0.0399, 0.0384]` |
| `satlib_more/flat75-1.cnf` | 225 | 840 | SAT | 0.0423s | SAT | 0.0360s | -0.0063s | 0.850x | `[0.0532, 0.0356, 0.0354, 0.0525, 0.0349]` | `[0.0329, 0.0375, 0.0339, 0.0485, 0.0271]` |
| `satlib_more/flat75-10.cnf` | 225 | 840 | SAT | 0.0451s | SAT | 0.0392s | -0.0060s | 0.868x | `[0.0489, 0.0453, 0.0548, 0.0386, 0.0382]` | `[0.0350, 0.0514, 0.0310, 0.0440, 0.0344]` |
| `satlib_more/jnh1.cnf` | 100 | 850 | SAT | 0.0468s | SAT | 0.0429s | -0.0040s | 0.916x | `[0.0531, 0.0412, 0.0431, 0.0400, 0.0567]` | `[0.0453, 0.0428, 0.0352, 0.0550, 0.0360]` |
| `satlib_more/jnh10.cnf` | 100 | 850 | UNSAT | 0.0488s | UNSAT | 0.0359s | -0.0129s | 0.736x | `[0.0392, 0.0566, 0.0553, 0.0519, 0.0409]` | `[0.0407, 0.0299, 0.0308, 0.0473, 0.0308]` |
| `satlib_more/uf125-01.cnf` | 125 | 538 | SAT | 0.0454s | SAT | 0.0368s | -0.0086s | 0.811x | `[0.0471, 0.0611, 0.0477, 0.0372, 0.0338]` | `[0.0269, 0.0448, 0.0432, 0.0270, 0.0420]` |
| `satlib_more/uf125-010.cnf` | 125 | 538 | SAT | 0.0583s | SAT | 0.0809s | +0.0226s | 1.387x | `[0.0560, 0.0460, 0.0642, 0.0470, 0.0784]` | `[0.0928, 0.0779, 0.0777, 0.0783, 0.0780]` |
| `satlib_more/uf150-01.cnf` | 150 | 645 | SAT | 0.0522s | SAT | 0.0416s | -0.0106s | 0.798x | `[0.0494, 0.0629, 0.0494, 0.0494, 0.0496]` | `[0.0569, 0.0389, 0.0382, 0.0357, 0.0382]` |
| `satlib_more/uuf125-01.cnf` | 125 | 538 | UNSAT | 0.1203s | UNSAT | 0.1010s | -0.0193s | 0.839x | `[0.1080, 0.1288, 0.1267, 0.1169, 0.1211]` | `[0.0968, 0.0878, 0.1115, 0.1043, 0.1046]` |
| `satlib_more/uuf125-010.cnf` | 125 | 538 | UNSAT | 0.1636s | UNSAT | 0.1446s | -0.0189s | 0.884x | `[0.1641, 0.1537, 0.1780, 0.1643, 0.1578]` | `[0.1571, 0.1314, 0.1459, 0.1482, 0.1405]` |
| `satlib_more/uuf150-01.cnf` | 150 | 645 | UNSAT | 0.4236s | UNSAT | 0.3441s | -0.0796s | 0.812x | `[0.4302, 0.4128, 0.4305, 0.4059, 0.4389]` | `[0.3354, 0.3218, 0.3307, 0.3503, 0.3822]` |
| `satlib_subset/dubois20.cnf` | 60 | 160 | UNSAT | 0.0402s | UNSAT | 0.0332s | -0.0070s | 0.825x | `[0.0335, 0.0437, 0.0498, 0.0356, 0.0385]` | `[0.0276, 0.0309, 0.0425, 0.0380, 0.0269]` |
| `satlib_subset/dubois21.cnf` | 63 | 168 | UNSAT | 0.0351s | UNSAT | 0.0283s | -0.0067s | 0.808x | `[0.0308, 0.0433, 0.0293, 0.0397, 0.0323]` | `[0.0399, 0.0235, 0.0324, 0.0211, 0.0248]` |
| `satlib_subset/flat50-1.cnf` | 150 | 545 | SAT | 0.0426s | SAT | 0.0391s | -0.0036s | 0.917x | `[0.0497, 0.0477, 0.0459, 0.0362, 0.0336]` | `[0.0310, 0.0442, 0.0385, 0.0385, 0.0431]` |
| `satlib_subset/flat50-10.cnf` | 150 | 545 | SAT | 0.0356s | SAT | 0.0410s | +0.0054s | 1.151x | `[0.0391, 0.0307, 0.0351, 0.0392, 0.0341]` | `[0.0414, 0.0410, 0.0467, 0.0397, 0.0362]` |
| `satlib_subset/hole10.cnf` | 110 | 561 | UNSAT | 0.0349s | UNSAT | 0.0278s | -0.0071s | 0.795x | `[0.0408, 0.0342, 0.0270, 0.0424, 0.0300]` | `[0.0219, 0.0224, 0.0387, 0.0311, 0.0247]` |
| `satlib_subset/hole8.cnf` | 72 | 297 | UNSAT | 0.0373s | UNSAT | 0.0291s | -0.0082s | 0.781x | `[0.0472, 0.0446, 0.0267, 0.0391, 0.0287]` | `[0.0217, 0.0350, 0.0342, 0.0324, 0.0221]` |
| `satlib_subset/uf100-01.cnf` | 100 | 430 | SAT | 0.0607s | SAT | 0.0609s | +0.0002s | 1.003x | `[0.0451, 0.0626, 0.0546, 0.0784, 0.0630]` | `[0.0588, 0.0691, 0.0575, 0.0625, 0.0565]` |
| `satlib_subset/uf100-010.cnf` | 100 | 430 | SAT | 0.0412s | SAT | 0.0315s | -0.0098s | 0.764x | `[0.0442, 0.0327, 0.0470, 0.0477, 0.0346]` | `[0.0375, 0.0298, 0.0358, 0.0275, 0.0268]` |
| `satlib_subset/uuf100-01.cnf` | 100 | 430 | UNSAT | 0.0605s | UNSAT | 0.0555s | -0.0051s | 0.916x | `[0.0722, 0.0478, 0.0558, 0.0514, 0.0755]` | `[0.0598, 0.0403, 0.0541, 0.0653, 0.0578]` |
| `satlib_subset/uuf100-010.cnf` | 100 | 430 | UNSAT | 0.0657s | UNSAT | 0.0669s | +0.0012s | 1.019x | `[0.0635, 0.0603, 0.0739, 0.0700, 0.0607]` | `[0.0587, 0.0675, 0.0711, 0.0812, 0.0562]` |
| `small/test_1.cnf` | 19 | 26 | SAT | 0.0333s | SAT | 0.0361s | +0.0028s | 1.084x | `[0.0312, 0.0396, 0.0309, 0.0268, 0.0382]` | `[0.0308, 0.0340, 0.0397, 0.0428, 0.0333]` |
| `small/test_10.cnf` | 22 | 174 | UNSAT | 0.0410s | UNSAT | 0.0342s | -0.0068s | 0.834x | `[0.0339, 0.0551, 0.0558, 0.0305, 0.0299]` | `[0.0252, 0.0448, 0.0240, 0.0364, 0.0408]` |
| `small/test_2.cnf` | 46 | 176 | SAT | 0.0382s | SAT | 0.0370s | -0.0012s | 0.969x | `[0.0489, 0.0295, 0.0275, 0.0381, 0.0473]` | `[0.0233, 0.0393, 0.0359, 0.0433, 0.0434]` |
| `small/test_3.cnf` | 41 | 150 | SAT | 0.0400s | SAT | 0.0301s | -0.0099s | 0.753x | `[0.0304, 0.0305, 0.0503, 0.0433, 0.0453]` | `[0.0404, 0.0218, 0.0221, 0.0419, 0.0243]` |
| `small/test_4.cnf` | 30 | 167 | UNSAT | 0.0378s | UNSAT | 0.0288s | -0.0090s | 0.762x | `[0.0439, 0.0474, 0.0301, 0.0360, 0.0314]` | `[0.0374, 0.0339, 0.0224, 0.0257, 0.0245]` |
| `small/test_5.cnf` | 20 | 40 | SAT | 0.0324s | SAT | 0.0239s | -0.0085s | 0.736x | `[0.0419, 0.0362, 0.0275, 0.0281, 0.0284]` | `[0.0239, 0.0250, 0.0212, 0.0217, 0.0275]` |
| `small/test_6.cnf` | 42 | 70 | SAT | 0.0309s | SAT | 0.0217s | -0.0092s | 0.702x | `[0.0288, 0.0404, 0.0281, 0.0285, 0.0286]` | `[0.0234, 0.0213, 0.0214, 0.0215, 0.0208]` |
| `small/test_7.cnf` | 49 | 167 | SAT | 0.0341s | SAT | 0.0257s | -0.0085s | 0.752x | `[0.0342, 0.0454, 0.0297, 0.0295, 0.0319]` | `[0.0263, 0.0328, 0.0223, 0.0229, 0.0241]` |
| `small/test_8.cnf` | 14 | 68 | UNSAT | 0.0398s | UNSAT | 0.0297s | -0.0101s | 0.746x | `[0.0292, 0.0441, 0.0419, 0.0387, 0.0452]` | `[0.0304, 0.0220, 0.0226, 0.0358, 0.0378]` |
| `small/test_9.cnf` | 40 | 100 | SAT | 0.0403s | SAT | 0.0292s | -0.0111s | 0.724x | `[0.0401, 0.0331, 0.0416, 0.0399, 0.0467]` | `[0.0244, 0.0393, 0.0358, 0.0200, 0.0263]` |
| `special/dense.cnf` | 200 | 1500 | UNSAT | 0.1332s | UNSAT | 0.1199s | -0.0134s | 0.900x | `[0.1336, 0.1269, 0.1280, 0.1426, 0.1350]` | `[0.1145, 0.1155, 0.1116, 0.1312, 0.1265]` |
| `special/easy.cnf` | 200 | 400 | SAT | 0.0411s | SAT | 0.0387s | -0.0024s | 0.942x | `[0.0416, 0.0389, 0.0399, 0.0477, 0.0375]` | `[0.0386, 0.0282, 0.0432, 0.0431, 0.0405]` |
| `special/hard.cnf` | 200 | 850 | UNSAT | 7.9452s | UNSAT | 2.4969s | -5.4483s | 0.314x | `[8.0149, 7.9758, 7.9099, 7.9270, 7.8984]` | `[2.5804, 2.5372, 2.3730, 2.4828, 2.5113]` |
| `special/pigeonhole.cnf` | 90 | 415 | UNSAT | 0.0393s | UNSAT | 0.0285s | -0.0108s | 0.726x | `[0.0445, 0.0430, 0.0348, 0.0278, 0.0463]` | `[0.0229, 0.0330, 0.0225, 0.0410, 0.0234]` |
| `special/tseitin.cnf` | 40 | 160 | UNSAT | 0.0438s | UNSAT | 0.0357s | -0.0081s | 0.816x | `[0.0413, 0.0485, 0.0408, 0.0468, 0.0415]` | `[0.0429, 0.0236, 0.0352, 0.0401, 0.0368]` |
