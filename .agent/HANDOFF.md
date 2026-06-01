# HANDOFF

## Current State

- The repo still uses the queue-driven autonomous control plane rooted in `AGENT.md` and `.agent/*`, plus the machine-checkable queue validator.
- `cp-001`, `cp-002`, `cp-003`, `sat-001`, `tool-001`, `perf-001` through `perf-064` are complete.
- A user-directed `project_context.md` snapshot now exists to bundle the tracked repo files, their roles, and their verbatim contents for external AI review; the queue itself is unchanged.
- A user-directed phase-diversified portfolio keep is now present in the working tree: portfolio workers use deterministic phase modes ordered `default`, `bias_positive`, `lcg1`, `bias_negative`, capped at three workers.
- A user-directed Mycielski graph-coloring detector keep is now present in the working tree: exact standard graph-coloring encodings for Mycielski towers from `K2` can return UNSAT before CDCL when the chromatic lower bound exceeds the available colors.
- A user-directed coverage-suite keep is now present in the working tree: generated regression CNFs, smoke scripts, packaging checks, portfolio cleanup stress, a compact must-pass suite, and `coverage_report.md`.
- A user-directed CNFgen regression pack is now present in `cnfgen_regression_pack/`: 228 retained CNFs across 30 families, all within `vars <= 500` and `clauses <= 2000`, all known SAT/UNSAT, full smoke passing under the 60s per-case timeout, exact-CLI avg-5 benchmark passing `228/228`, and `CNF_LIST.md` listing every retained CNF.
- There is no active in-progress task; the next deterministic task is `perf-065`.

## What Changed This Run

- Added `cnfgen_regression_pack/generate_cnfgen_pack.py`, a deterministic CNFgen generator with hard guards for `vars <= 500`, `clauses <= 2000`, known final status, and `60s` manifest timeout.
- Generated `228` retained CNFgen cases under `cnfgen_regression_pack/cnfgen_cases/`.
- Added `cnfgen_regression_pack/MANIFEST.tsv`, `manifest.csv`, `README.md`, `SMOKE_REPORT.md`, and `AVG5_BENCHMARK.md`.
- Added `cnfgen_regression_pack/CNF_LIST.md`, a complete table of all `228` retained CNF files with status, family, level, vars, clauses, and timeout.
- Updated `generated_cnf_report.md` with the CNFgen pack summary.
- Left solver algorithms, heuristics, detector strictness, and portfolio thresholds unchanged.

## Current Focus

- Start `perf-065` next: stay measurement-only and split the surviving exact `sub10 step-3` deep-overwrite `index 16+` lane into exact source index `16` versus `index 17+`.

## Recommended Next Tasks

- `perf-065` — profile the exact index-16-plus deep overwrite tail after the perf-064 reject

## Verification From This Run

- `python cnfgen_regression_pack/generate_cnfgen_pack.py --cnfgen /tmp/satsolver-cnfgen-venv/bin/cnfgen` — passed; generated `228` retained CNFgen cases (`152 SAT`, `76 UNSAT`)
- Manifest constraint check — passed: `228` rows, `30` families, `max_vars=500`, `max_clauses=2000`, all statuses `SAT` or `UNSAT`, all timeouts `60`
- `PYTHONUNBUFFERED=1 python tests/scripts/run_regression_smoke.py --solver ./satsolver.py --suite cnfgen_regression_pack --timeout 60` — passed (`228/228`, max `35.4312s`)
- `python ../benchmark_suite.py satsolver /tmp/cnfgen_regression_pack_avg5.txt cnfgen_cases --bruteforce-var-limit 16 --repeat 5 --cli-script ../satsolver.py` from `cnfgen_regression_pack/` — passed (`228/228`, `0` errors, representative total `80.1684s`, measured total `402.7179s`, wall `410.3343s`)
- `python -m py_compile cnfgen_regression_pack/generate_cnfgen_pack.py` — passed
- `python tools/codex_verify.py` — passed (`100` tests plus compile, queue, checker, and wrapper smoke checks)
- `git diff --check` — passed

## Notes For The Next Run

- Start with the read order in `.agent/RUNBOOK.md`.
- Reconcile `STATE.yaml` against the repo tree before selecting a task.
- Keep `PLANS.md` updated for any multi-step or code-bearing task.
- Rebuild the CNFgen pack only with an explicit CNFgen executable; CNFgen remains generation-only and must not become a submission-path dependency.
- Keep `cnfgen_regression_pack/manifest.csv` and `MANIFEST.tsv` aligned by rerunning `python cnfgen_regression_pack/generate_cnfgen_pack.py --cnfgen <path>` after generator changes.
- Refresh `project_context.md` only when the tracked repo snapshot or the guidance another AI needs has changed materially; it intentionally snapshots the pre-self tracked tree and excludes local untracked files.
- Reuse the queue checker when adjusting `.agent/STATE.yaml` or `.agent/TASK_QUEUE.yaml`.
- The default verifier covers `satsolver_fast.py`, but `satsolver_pysat.py` remains outside the default gate because it requires an optional external environment.
- External libraries or solvers may be used as short-lived research references only; do not retain them in the submission path or make them a default verifier dependency.
- The phase-diversified portfolio keep is already recorded in `benchmark_summary.md` and `experiments.jsonl`; future portfolio work should preserve the old `default`/`bias_positive` pair unless same-day broad evidence says otherwise.
- The coverage-suite task is intentionally not recorded in `benchmark_summary.md` or `experiments.jsonl` because it kept no performance change; see `coverage_report.md` for its factual results.
- `perf-048` ruled out the whole exact `index 8+` aggregate, `perf-049` showed that the surviving `index 8+` tail is dominated by exact `index 9+`, `perf-050` showed that even the exact `index 9+` aggregate is still too broad for the retained pop-first rewrite, `perf-051` showed that the remaining exact `index 9+` tail is still dominated by exact `index 10+`, `perf-052` showed that even the exact `index 10+` aggregate is still too broad, `perf-053` showed that the surviving `index 10+` tail is itself dominated by exact `index 11+`, `perf-054` showed that even the exact `index 11+` aggregate is still too broad despite a positive dense-anchor and supplemental signal, `perf-055` showed that the remaining exact `index 11+` tail is itself dominated by exact `index 12+`, `perf-056` showed that even the exact `index 12+` aggregate is still too broad despite a positive supplemental signal, `perf-057` showed that the remaining exact `index 12+` tail is itself dominated by exact `index 13+`, `perf-058` showed that even the exact `index 13+` aggregate is still too broad despite a small positive dense-anchor signal, `perf-059` showed that the surviving exact `index 13+` tail is itself still dominated by exact `index 14+`, `perf-060` showed that even the exact `index 14+` aggregate is still too mixed to keep, `perf-061` showed that the surviving exact `index 14+` tail is itself still dominated by exact `index 15+`, and `perf-062` now shows that even the exact `index 15+` aggregate is still too broad because all three early gates regressed.
- `perf-063` now shows that the surviving exact `index 15+` tail is itself still dominated by exact `index 16+` on the dense anchors, and the only non-zero supplemental target-trio traffic remains `uuf125-010` at `3` exact `index 15` hits versus `10` `index 16+` hits.
- `perf-064` now shows that even the exact `index 16+` aggregate is still too broad: it kept the same dense-anchor search counts and improved the supplemental slice slightly, but it still regressed both the dense anchors and the focused seven-case gate.
- Keep `special/hard.cnf` and `large/test_6.cnf` as the dense exact-step anchor pair, and keep the supplemental `satlib_more` slice (`uuf125-010`, `uf125-01`, `uf125-010`, `jnh10`, `jnh1`) in view because the target trio still shows real deep-overwrite traffic while `jnh10` and `jnh1` remain mostly guardrails.
- `perf-065` should stay measurement-only and split exact `index 16+` into exact `index 16` versus `index 17+` before any broader learnt-large bookkeeping rewrite is retried.

## Immediate Constraints

- Keep the submission path standard-library only.
- Preserve `python satsolver.py input.cnf output.txt`.
- Do not update `benchmark_summary.md` or `experiments.jsonl` unless a performance result is kept.
- External comparison tooling is allowed only for research and must not become a retained submission dependency.

## Repo Truths To Preserve

- `satsolver_core.py` is the shared CDCL implementation.
- `satsolver_io.py` is the shared DIMACS parsing and result-writing helper for thin wrappers.
- `tools/checker.py` is the correctness oracle for solver output format.
- `tools/agent_queue_check.py` is the control-plane consistency oracle.
- `tools/codex_verify.py` is expected to cover both `satsolver.py` and `satsolver_fast.py` smoke paths by default.
- The retained portfolio thresholds still intentionally gate only `large/test_8.cnf` until a same-day broader threshold change wins cleanly.
- Same-day exact-CLI evidence is stronger than stale benchmark history when timing signals are close.
- External solvers or libraries may inform research, but only native-only wins belong in the retained solver path.
- `large/test_8.cnf` remains an important SAT-like guardrail for learnt-database and restart-sensitive changes.
- On the current machine, repeat-aware exact-CLI totals are still noisy enough that case ordering is usually more stable than one raw rerun total.
- The current solver still owns the structural fast-exit families (`special/pigeonhole.cnf`, `special/tseitin.cnf`) even though optional external references are dramatically faster on the dense search-heavy UNSAT hotspot slice.
- Future learnt-large relocation work should use the focused seven-case slice plus the supplemental `satlib_more` slice (`uuf125-010`, `jnh10`, `uf125-01`, `uf125-010`, `jnh1`) before the full repeat-aware exact-CLI keep gate.
