# Universal SAT Solver Benchmark Report

Generated from the benchmark markdown reports currently present in the repository.

## Executive Summary

The current `satsolver.py` is consistently correct on the tested datasets and is much faster than the old solver on the course-shaped workloads.

- Main sample `formulae/`: current solver is valid on `35/35`, with avg-total around `11.5-11.6s`.
- Broad `course_cnf_tests`: current solver is valid on `278/278` when the known hard timeout case is excluded.
- Old vs current on `formulae/`: current solver wins `34/35` cases and loses only `large/test_8.cnf`.
- Old vs current on the broad course set: current solver removes the old timeout and gives a large total-time improvement.
- `PORTFOLIO_MAX_DENSITY`: `4.3` is best on the official-like `formulae/` sample, while `4.4` is best on the broader `278`-case set.

Recommended default from the full evidence: keep `4.3` if optimizing for the visible sample set, but use `4.4` if optimizing for broader hidden-test generalization.

## Source Reports

| Report | Scope | Runs | Key Result |
|---|---|---:|---|
| [oldsatsolver_vs_satsolver_formulae_avg5.md](oldsatsolver_vs_satsolver_formulae_avg5.md) | old vs current on `formulae/` | avg of 5 | current `11.6486s`, old `26.1656s`, delta `-14.5170s` |
| [oldsatsolver_vs_satsolver_formulae_like_avg5.md](oldsatsolver_vs_satsolver_formulae_like_avg5.md) | old vs current on generated `formulae_like/` | avg of 5 | current `3.7612s`, old `4.4891s`, delta `-0.7279s` |
| [oldsatsolver_vs_satsolver_formulae_like_variants_avg5.md](oldsatsolver_vs_satsolver_formulae_like_variants_avg5.md) | old vs current on `formulae_like_01..03` | avg of 5 | current `11.3928s`, old `13.9262s`, delta `-2.5333s` |
| [oldsatsolver_vs_satsolver_avg5_no_timeout.md](oldsatsolver_vs_satsolver_avg5_no_timeout.md) | old vs current on `278` course cases, old timeout retained | avg of 5 | current `47.1389s`, old `116.9595s`, old has `1` timeout |
| [oldsatsolver_vs_satsolver_avg5_no_timeouts.md](oldsatsolver_vs_satsolver_avg5_no_timeouts.md) | old vs current on `277` course cases, both timeout cases removed | avg of 5 | current `42.6502s`, old `55.3984s`, delta `-12.7482s` |
| [old_new_comparison_course_cnf_tests_avg5_no_timeout.md](old_new_comparison_course_cnf_tests_avg5_no_timeout.md) | historical old snapshot vs new on `278` course cases | avg of 5 | current `45.8514s`, old `116.2220s`, delta `-70.3706s` |
| [satsolver_formulae_repeat2.md](satsolver_formulae_repeat2.md) | current solver only on `formulae/` | repeat 2 | `35/35` valid, avg-total `11.5190s` |
| [satsolver_course_cnf_tests_278_repeat2.md](satsolver_course_cnf_tests_278_repeat2.md) | current solver only on `278` course cases | repeat 2 | `278/278` valid, avg-total `29.9666s` |
| [portfolio_density_formulae_repeat2.md](portfolio_density_formulae_repeat2.md) | density sweep on `formulae/` | repeat 2 | best `PORTFOLIO_MAX_DENSITY = 4.3` |
| [portfolio_density_course278_repeat2.md](portfolio_density_course278_repeat2.md) | density sweep on `278` course cases | repeat 2 | best `PORTFOLIO_MAX_DENSITY = 4.4` |

## Correctness

No current-solver correctness failures were observed in the retained benchmark reports.

| Dataset / Report | Current Solver Validity | Timeouts |
|---|---:|---:|
| `formulae/` avg5 old-vs-new | `35/35` | `0` |
| `formulae_like/` avg5 old-vs-new | `35/35` | `0` |
| `formulae_like_01..03` avg5 old-vs-new | `105/105` | `0` |
| `course_cnf_tests` repeat2, known timeout excluded | `278/278` | `0` |
| `course_cnf_tests` avg5, old timeout retained | `278/278` | `0` |
| `course_cnf_tests` avg5, both timeout cases removed | `277/277` | `0` |

Known excluded case:

- `cnf_training_complex__complex_cnf_hard__mycielski_iter4_color5_unsat.cnf`

This case is excluded from the broad `278` reports because it is a known timeout-class stress case.

## Old Vs Current Solver

### Official-Like `formulae/`

| Metric | Old | Current | Delta |
|---|---:|---:|---:|
| Valid cases | `35/35` | `35/35` | `0` |
| Timeout cases | `0` | `0` | `0` |
| Avg-total | `26.1656s` | `11.6486s` | `-14.5170s` |
| Improved valid cases |  | `34` |  |
| Regressed valid cases |  | `1` |  |

Current solver is about `2.25x` faster by avg-total on the visible sample dataset.

Main wins:

- `large/test_6.cnf`: old `11.6915s`, current `3.5879s`, delta `-8.1036s`
- `special/hard.cnf`: old `8.0697s`, current `2.4076s`, delta `-5.6621s`
- `medium/test_4.cnf`: old `1.9367s`, current `1.0251s`, delta `-0.9116s`
- `large/test_10.cnf`: old `1.5996s`, current `0.8751s`, delta `-0.7245s`

Main regression:

- `large/test_8.cnf`: old `0.2936s`, current `1.6834s`, delta `+1.3898s`

### Broad Course Set

With one known timeout case excluded, the current solver is valid on all `278` tested cases. In the avg5 comparison where the old solver still sees its extra timeout case, the current solver also fixes that timeout:

| Metric | Old | Current | Delta |
|---|---:|---:|---:|
| Correct all 5 repeats | `277/278` | `278/278` | `+1` |
| Timeout cases | `1` | `0` | `-1` |
| Avg-total | `116.9595s` | `47.1389s` | `-69.8206s` |

When both timeout-class cases are removed for a fairer `277`-case comparison:

| Metric | Old | Current | Delta |
|---|---:|---:|---:|
| Valid cases | `277/277` | `277/277` | `0` |
| Avg-total | `55.3984s` | `42.6502s` | `-12.7482s` |
| Improved valid cases |  | `242` |  |
| Regressed valid cases |  | `21` |  |

This says the current solver is not only fixing a timeout; it is also broadly faster when timeout cases are removed.

## Current Solver Standalone

| Dataset | Cases | Repeats | Valid | Timeouts | Avg-Total | Slowest Cases |
|---|---:|---:|---:|---:|---:|---|
| `formulae/` | `35` | `2` | `35/35` | `0` | `11.5190s` | `large/test_6`, `special/hard`, `large/test_8` |
| `course_cnf_tests` | `278` | `2` | `278/278` | `0` | `29.9666s` | `large__test_6`, `special__hard`, `large__test_8` |

Recurring slow cases:

- `large/test_6.cnf` / `large__test_6.cnf`
- `special/hard.cnf` / `special__hard.cnf`
- `large/test_8.cnf` / `large__test_8.cnf`
- `large/test_10.cnf` / `large__test_10.cnf`
- Ramsey UNSAT cases in `cnf_training_complex`
- selected planted 3-SAT cases such as `planted3sat_balanced_n260_m1108_seed1`

## Density Sweep

The tested knob was:

```python
PORTFOLIO_MAX_DENSITY
```

### `formulae/`

| Density | Valid | Avg-Total | Delta vs 4.3 | Best-Case Count |
|---:|---:|---:|---:|---:|
| `4.2` | `35/35` | `12.4283s` | `+0.2306s` | `9` |
| `4.3` | `35/35` | `12.1977s` | `0.0000s` | `17` |
| `4.35` | `35/35` | `12.9862s` | `+0.7885s` | `6` |
| `4.4` | `35/35` | `12.3008s` | `+0.1031s` | `13` |

Best on `formulae/`: `4.3`.

### Broad `278` Course Cases

| Density | Valid | Avg-Total | Delta vs 4.3 | Best-Case Count |
|---:|---:|---:|---:|---:|
| `4.2` | `278/278` | `48.3530s` | `+18.6824s` | `87` |
| `4.3` | `278/278` | `29.6705s` | `0.0000s` | `64` |
| `4.35` | `278/278` | `29.8504s` | `+0.1799s` | `83` |
| `4.4` | `278/278` | `29.0439s` | `-0.6266s` | `93` |

Best on the broad set: `4.4`.

Interpretation:

- `4.2` is risky; it causes a large slowdown on some planted SAT cases.
- `4.3` is best for the visible `formulae/` sample and is a conservative default.
- `4.4` is better on the broader `278`-case suite and has the most best-case wins there.
- `4.35` is close to `4.3/4.4`, but does not win either main density report.

## Synthetic Formulae-Like Datasets

The current solver also wins on generated hidden-test-style data overall.

| Dataset Group | Cases | Old Avg-Total | Current Avg-Total | Delta | Improved | Regressed |
|---|---:|---:|---:|---:|---:|---:|
| `formulae_like/` | `35` | `4.4891s` | `3.7612s` | `-0.7279s` | `33` | `1` |
| `formulae_like_01..03` | `105` | `13.9262s` | `11.3928s` | `-2.5333s` | `97` | `6` |

The synthetic variants show a useful warning: current solver is not uniformly faster on every planted 3-SAT distribution. `formulae_like_02` regressed overall:

| Dataset | Old Avg-Total | Current Avg-Total | Delta |
|---|---:|---:|---:|
| `formulae_like_01` | `5.3987s` | `4.5658s` | `-0.8330s` |
| `formulae_like_02` | `3.5859s` | `4.3140s` | `+0.7281s` |
| `formulae_like_03` | `4.9415s` | `2.5131s` | `-2.4284s` |

So the current solver is stronger overall, but some planted SAT profiles remain sensitive.

## Main Risks

1. `large/test_8.cnf` is the most consistent visible regression: current solver is slower than old on this SAT case.
2. Some generated planted 3-SAT cases regress, especially around medium-density hidden-assignment formulas.
3. `PORTFOLIO_MAX_DENSITY` has no single perfect value:
   - `4.3` is best for `formulae/`.
   - `4.4` is best for broad `course_cnf_tests`.
4. The known `mycielski_iter4_color5_unsat` case remains outside the practical benchmark set due to timeout behavior.

## Recommendation

For submission readiness:

- Keep the current solver architecture; it is correct on all retained benchmark reports.
- If the target is the visible `formulae/` sample, keep `PORTFOLIO_MAX_DENSITY = 4.3`.
- If the target is broader hidden tests similar to the generated and collected course sets, consider changing `PORTFOLIO_MAX_DENSITY` to `4.4` and rerunning:
  - `python tools/codex_verify.py`
  - `python benchmark_suite.py satsolver /tmp/bench_cli.txt formulae --repeat 2 --cli-script satsolver.py`
  - the `278`-case course benchmark
- Do not submit `odlsatsover.py`, `satsolver_pysat.py`, or external-comparison tooling.
- Verify packaging expectations before final upload: if the assignment accepts only one file, `satsolver.py` currently depends on `satsolver_core.py` and `satsolver_io.py`.

Current best evidence says the solver is ready from correctness and performance perspectives, with the main open decision being whether to tune `PORTFOLIO_MAX_DENSITY` for sample performance (`4.3`) or broader robustness (`4.4`).
