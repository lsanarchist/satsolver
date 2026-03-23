# HANDOFF

## Current State

- The repo still uses the queue-driven autonomous control plane rooted in `AGENT.md` and `.agent/*`, plus the machine-checkable queue validator.
- `cp-001`, `cp-002`, `cp-003`, `sat-001`, `tool-001`, `perf-001` through `perf-059` are complete.
- There is no active in-progress task; the next deterministic task is `perf-060`.

## What Changed This Run

- Closed `perf-059` as a retained measurement-only run with no solver change.
- Added profiler-only exact `index 13` versus `index 14+` deep-overwrite counters plus regression coverage in `tools/profile_solver.py` and `tests/test_profile_solver.py`.
- The dense anchors split exact `index 13+` deep overwrites `574` at exact index `13` versus `1,692` at `index 14+`.
- The supplemental target trio only showed non-zero exact `index 13+` traffic on `uuf125-010`, which split `4` at exact index `13` versus `13` at `index 14+`; `uf125-01`, `uf125-010`, `jnh10`, and `jnh1` stayed at zero exact `index 13+` hits.

## Current Focus

- Start `perf-060` next: test one bounded solver-core candidate only on the exact `sub10 step-3` deep-overwrite `index 14+` lane, while keeping exact `index 13` and all shallower retained baseline behavior unchanged.

## Recommended Next Tasks

- `perf-060` — test the exact index-14-plus deep overwrite tail after the perf-059 profile

## Verification From This Run

- `python -m unittest discover -s tests -p 'test_profile_solver.py' -q` — passed (`29/29` green, including the new exact `index 13` versus `index 14+` deep-tail split test)
- `python tools/profile_solver.py large/test_6.cnf special/hard.cnf satlib_more/uuf125-010.cnf satlib_more/uf125-01.cnf satlib_more/uf125-010.cnf satlib_more/jnh10.cnf satlib_more/jnh1.cnf` — passed and showed exact `index 14+` dominating exact `index 13` on the dense anchors (`1,692` vs `574`) and on the only non-zero supplemental target-trio case, `uuf125-010` (`13` vs `4`)
- `python tools/agent_queue_check.py` — passed after the final control-plane sync; queue now resolves to `current_or_next_task='perf-060'`
- `python tools/codex_verify.py` — passed after the final control-plane sync (`89/89` tests green plus compile, queue, checker, and wrapper smoke checks)
- `git diff --check` — passed after the final control-plane sync

## Notes For The Next Run

- Start with the read order in `.agent/RUNBOOK.md`.
- Reconcile `STATE.yaml` against the repo tree before selecting a task.
- Keep `PLANS.md` updated for any multi-step or code-bearing task.
- Reuse the queue checker when adjusting `.agent/STATE.yaml` or `.agent/TASK_QUEUE.yaml`.
- The default verifier covers `satsolver_fast.py`, but `satsolver_pysat.py` remains outside the default gate because it requires an optional external environment.
- External libraries or solvers may be used as short-lived research references only; do not retain them in the submission path or make them a default verifier dependency.
- Do not update `benchmark_summary.md` or `experiments.jsonl` for `perf-059`; this run kept no solver change.
- `perf-048` ruled out the whole exact `index 8+` aggregate, `perf-049` showed that the surviving `index 8+` tail is dominated by exact `index 9+`, `perf-050` showed that even the exact `index 9+` aggregate is still too broad for the retained pop-first rewrite, `perf-051` showed that the remaining exact `index 9+` tail is still dominated by exact `index 10+`, `perf-052` showed that even the exact `index 10+` aggregate is still too broad, `perf-053` showed that the surviving `index 10+` tail is itself dominated by exact `index 11+`, `perf-054` showed that even the exact `index 11+` aggregate is still too broad despite a positive dense-anchor and supplemental signal, `perf-055` showed that the remaining exact `index 11+` tail is itself dominated by exact `index 12+`, `perf-056` showed that even the exact `index 12+` aggregate is still too broad despite a positive supplemental signal, `perf-057` showed that the remaining exact `index 12+` tail is itself dominated by exact `index 13+`, `perf-058` showed that even the exact `index 13+` aggregate is still too broad despite a small positive dense-anchor signal, and `perf-059` now shows that the surviving exact `index 13+` tail is itself still dominated by exact `index 14+`.
- Keep `special/hard.cnf` and `large/test_6.cnf` as the dense exact-step anchor pair, and keep the supplemental `satlib_more` slice (`uuf125-010`, `uf125-01`, `uf125-010`, `jnh10`, `jnh1`) in view because the target trio still shows real deep-overwrite traffic while `jnh10` and `jnh1` remain mostly guardrails.
- `perf-060` should test one bounded solver-core candidate only on the exact `sub10 step-3` deep-overwrite `index 14+` lane before any broader learnt-large bookkeeping rewrite is retried.

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
