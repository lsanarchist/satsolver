# SAT Solver Coverage Report

Date: 2026-06-01

Environment:

- Python: `3.13.9`
- OS: `Linux desktoppc 6.12.38+kali-amd64 x86_64`
- Solver entrypoint: `python satsolver.py input.cnf output.txt`

## Scope

This report covers the regression and submission-readiness suite added from
`sat_solver_coverage_agent_instructions.md`. The task was coverage-only:
no solver algorithm, heuristic, detector strictness, or portfolio threshold was
changed.

## Generated Coverage

Generated CNFs live under `tests/generated/` with tab-separated manifests.

| Suite | CNFs | Purpose |
| --- | ---: | --- |
| `tests/generated/mycielski` | 6 | Mycielski UNSAT fast-exit guards plus SAT sufficient-color guards |
| `tests/generated/mutated_mycielski` | 11 | False-positive guards for broken or non-standard Mycielski encodings |
| `tests/generated/graph_coloring` | 8 | General graph-coloring SAT and UNSAT coverage |
| `tests/generated/random_near_limit` | 6 | Near-assignment-limit random, planted, XOR, and pigeonhole stress |
| `tests/generated/portfolio_density` | 90 | Portfolio gate boundary coverage around density thresholds |
| `tests/generated/parser_edge_cases` | 19 | DIMACS parser edge cases, invalid inputs, comments, whitespace, and model validation |
| Total | 140 | Generated regression corpus |

## Smoke Results

| Command | Result |
| --- | --- |
| `python -m py_compile satsolver.py satsolver_core.py satsolver_io.py tests/scripts/generate_regression_cases.py tests/scripts/run_regression_smoke.py tests/scripts/validate_output.py tests/scripts/check_single_file_submission.py tests/scripts/stress_portfolio_cleanup.py tests/test_generated_coverage.py` | passed |
| `python tests/scripts/generate_regression_cases.py` | generated 140 CNFs |
| `python -m pytest tests/test_generated_coverage.py -q` | passed, `4 passed` |
| `python tests/scripts/run_regression_smoke.py --solver ./satsolver.py --suite tests/generated --timeout 60` | passed, `140/140`, max `0.1205s` |
| `python tests/scripts/run_regression_smoke.py --solver ./satsolver.py --suite tests/must_pass --timeout 60` | passed, `17/17`, max `3.6623s` |
| `python tests/scripts/stress_portfolio_cleanup.py --solver ./satsolver.py --repeat 5 --timeout 60` | passed, `15/15`, avg `1.8407s`, max `4.1003s` |
| `python tools/codex_verify.py` | passed, `100` unit tests plus compile, queue, checker, and wrapper smoke checks |

## Full Benchmark Sanity

Fresh exact-CLI scratch benchmarks were run for correctness, not as retained
performance baselines.

| Dataset | Cases | Solved | SAT | UNSAT | Errors | Total | Wall Clock | Max |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| `formulae` | 35 | 35 | 16 | 19 | 0 | `10.5580s` | `10.6678s` | `3.7112s` |
| `course_cnf_tests` | 279 | 279 | 157 | 122 | 0 | `28.5081s` | `30.7521s` | `3.7351s` |

Slowest observed cases:

- `formulae/large/test_6.cnf`: `3.7112s`
- `course_cnf_tests/large__test_6.cnf`: `3.7351s`
- `formulae/special/hard.cnf`: `2.6933s`
- `course_cnf_tests/special__hard.cnf`: `2.8142s`
- `course_cnf_tests/cnf_training_complex__complex_cnf_hard__planted3sat_balanced_n260_m1108_seed1.cnf`: `1.6008s`

## Packaging Check

`tests/scripts/check_single_file_submission.py` reports:

- `single_file_supported=false`
- `multi_file_supported=true`
- `required_files=satsolver.py,satsolver_core.py,satsolver_io.py`

The current submission is intentionally modular. A submission archive should
include all three required Python files unless a separate bundling task creates
a verified single-file solver.

## Must-Pass Suite

`tests/must_pass/` is a compact suite for quick pre-submission checks. It
includes:

- formulae hotspots and structural fast-exit cases
- the hard Mycielski UNSAT case
- a Mycielski sufficient-color SAT guard
- planted SAT and Ramsey UNSAT course cases
- generated near-limit XOR UNSAT coverage

Run it with:

```bash
python tests/scripts/run_regression_smoke.py --solver ./satsolver.py --suite tests/must_pass --timeout 60
```

## Remaining Risks

- The Mycielski detector is intentionally conservative and only accepts exact
  standard graph-coloring encodings. Equivalent encodings with redundant or
  reordered constraints may fall through to normal CDCL search.
- Generated coverage improves guardrails but is not a proof against all final
  hidden tests.
- The solver is not currently single-file compatible. The modular three-file
  submission path is verified.
