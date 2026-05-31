# HANDOFF

## Current State

- The repo still uses the queue-driven autonomous control plane rooted in `AGENT.md` and `.agent/*`, plus the machine-checkable queue validator.
- `cp-001`, `cp-002`, `cp-003`, `sat-001`, `tool-001`, `perf-001` through `perf-064` are complete.
- A user-directed `project_context.md` snapshot now exists to bundle the tracked repo files, their roles, and their verbatim contents for external AI review; the queue itself is unchanged.
- A user-directed phase-diversified portfolio keep is now present in the working tree: portfolio workers use deterministic phase modes ordered `default`, `bias_positive`, `lcg1`, `bias_negative`, capped at three workers.
- There is no active in-progress task; the next deterministic task is `perf-065`.

## What Changed This Run

- Implemented `phase_portfolio_agent_instructions.md` as a user-directed native-only solver change.
- Added shared phase-mode constants and `Solver.seed_saved_phases_mode()` in `satsolver_core.py`, leaving `seed_saved_phases_from_bias()` as a compatibility wrapper.
- Replaced boolean portfolio worker selection in `satsolver_core.py`, `satsolver.py`, and `satsolver_fast.py` with deterministic phase modes.
- Rejected the first mode order (`default`, `lcg1`, `bias_negative`) during benchmarking because it regressed several planted SAT gate cases; kept the safer order (`default`, `bias_positive`, `lcg1`, `bias_negative`) so the old two-worker pair remains first.
- Added regression coverage for phase-mode seeding and updated `PLANS.md`, `benchmark_summary.md`, and `experiments.jsonl` with the kept result.

## Current Focus

- Start `perf-065` next: stay measurement-only and split the surviving exact `sub10 step-3` deep-overwrite `index 16+` lane into exact source index `16` versus `index 17+`.

## Recommended Next Tasks

- `perf-065` — profile the exact index-16-plus deep overwrite tail after the perf-064 reject

## Verification From This Run

- `python -m py_compile satsolver.py satsolver_core.py satsolver_io.py satsolver_fast.py` — passed
- `python -m pytest tests/test_solver_regressions.py -q` — passed (`20 passed`)
- `python tools/hotspot_compare.py --baseline-cli-script /tmp/phase_portfolio_baseline.yPZFfp/satsolver.py --candidate-cli-script satsolver.py --repeat 2 formulae/large/test_8.cnf` — target improved (`1.7061s -> 0.1257s`)
- `python tools/hotspot_compare.py --baseline-cli-script /tmp/phase_portfolio_baseline.yPZFfp/satsolver.py --candidate-cli-script satsolver.py --repeat 2 <six portfolio-gated course cases>` — final gate-only slice improved (`5.5063s -> 3.9310s`)
- `python ../benchmark_suite.py satsolver /tmp/phase_formulae_candidate_final.txt small medium large special --bruteforce-var-limit 16 --repeat 2 --cli-script ../satsolver.py` from `formulae/` — candidate `35/35`, total `10.0431s`
- `python ../benchmark_suite.py satsolver /tmp/phase_formulae_baseline.txt small medium large special --bruteforce-var-limit 16 --repeat 2 --cli-script /tmp/phase_portfolio_baseline.yPZFfp/satsolver.py` from `formulae/` — baseline `35/35`, total `12.0224s`
- `python benchmark_suite.py satsolver /tmp/phase_course_candidate_final.txt . --bruteforce-var-limit 16 --repeat 2 --cli-script /home/doomguy/Desktop/sat/satsolver/satsolver.py` from a scratch 278-case `course_cnf_tests` directory excluding known `mycielski_iter4_color5_unsat` — candidate `278/278`, total `27.8704s`
- `python benchmark_suite.py satsolver /tmp/phase_course_baseline.txt . --bruteforce-var-limit 16 --repeat 2 --cli-script /tmp/phase_portfolio_baseline.yPZFfp/satsolver.py` from the same scratch directory — baseline `278/278`, total `30.3867s`
- `python tools/agent_queue_check.py` — passed after the final control-plane sync (`current_or_next_task='perf-065'`)
- `git diff --check` — passed after the final control-plane sync
- `python tools/codex_verify.py` — passed after the final control-plane sync (`92` tests plus compile, queue, checker, and wrapper smoke checks)

## Notes For The Next Run

- Start with the read order in `.agent/RUNBOOK.md`.
- Reconcile `STATE.yaml` against the repo tree before selecting a task.
- Keep `PLANS.md` updated for any multi-step or code-bearing task.
- Refresh `project_context.md` only when the tracked repo snapshot or the guidance another AI needs has changed materially; it intentionally snapshots the pre-self tracked tree and excludes local untracked files.
- Reuse the queue checker when adjusting `.agent/STATE.yaml` or `.agent/TASK_QUEUE.yaml`.
- The default verifier covers `satsolver_fast.py`, but `satsolver_pysat.py` remains outside the default gate because it requires an optional external environment.
- External libraries or solvers may be used as short-lived research references only; do not retain them in the submission path or make them a default verifier dependency.
- The phase-diversified portfolio keep is already recorded in `benchmark_summary.md` and `experiments.jsonl`; future portfolio work should preserve the old `default`/`bias_positive` pair unless same-day broad evidence says otherwise.
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
