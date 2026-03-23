# HANDOFF

## Current State

- The repo still uses the queue-driven autonomous control plane rooted in `AGENT.md` and `.agent/*`, plus the machine-checkable queue validator.
- `cp-001`, `cp-002`, `cp-003`, `sat-001`, `tool-001`, `perf-001` through `perf-057` are complete.
- There is no active in-progress task; the next deterministic task is `perf-058`.

## What Changed This Run

- Closed `perf-057` as a measurement-only profiling run with no solver change.
- Added profiler-only exact `index 12` versus `index 13+` counters plus regression coverage inside the exact `sub10 step-3` deep-overwrite `index 12+` lane.
- The dense anchors `large/test_6.cnf` and `special/hard.cnf` combined to `791` exact `index 12` hits versus `2,266` `index 13+` hits.
- The real supplemental target trio `uuf125-010`, `uf125-01`, and `uf125-010` combined to `8` exact `index 12` hits versus `17` `index 13+` hits, while `jnh10` and `jnh1` stayed at zero exact `index 12+` hits.

## Current Focus

- Start `perf-058` next: test one bounded solver-core candidate only on the exact `sub10 step-3` deep-overwrite `index 13+` lane, while keeping exact `index 12` and shallower retained baseline behavior unchanged.

## Recommended Next Tasks

- `perf-058` — test the exact index-13-plus deep overwrite tail after the perf-057 profile

## Verification From This Run

- `python -m unittest discover -s tests -p 'test_profile_solver.py' -q` — passed (`28/28` green, including the new exact `index 12` versus `index 13+` deep-tail split test)
- `python tools/profile_solver.py large/test_6.cnf special/hard.cnf satlib_more/uuf125-010.cnf satlib_more/uf125-01.cnf satlib_more/uf125-010.cnf satlib_more/jnh10.cnf satlib_more/jnh1.cnf` — passed and reported `large/test_6.cnf` exact `index 12+` deep overwrites `305` at exact index `12` versus `836` at `index 13+`
- `python tools/profile_solver.py special/hard.cnf | rg -o "learnt_large_success_sub10_step3_source_pop_overwrite_deep_index(11_plus|11|12_plus|12|13_plus)=[0-9]+"` — passed and reported exact `index 12+` deep overwrites `486` at exact index `12` versus `1,430` at `index 13+`
- `python tools/profile_solver.py satlib_more/uuf125-010.cnf | rg -o "learnt_large_success_sub10_step3_source_pop_overwrite_deep_index(11_plus|11|12_plus|12|13_plus)=[0-9]+"` — passed and reported exact `index 12+` deep overwrites `8` at exact index `12` versus `17` at `index 13+`
- `python tools/profile_solver.py satlib_more/uf125-01.cnf | rg -o "learnt_large_success_sub10_step3_source_pop_overwrite_deep_index(11_plus|11|12_plus|12|13_plus)=[0-9]+"` — passed and reported zero exact `index 12+` deep overwrites
- `python tools/profile_solver.py satlib_more/uf125-010.cnf | rg -o "learnt_large_success_sub10_step3_source_pop_overwrite_deep_index(11_plus|11|12_plus|12|13_plus)=[0-9]+"` — passed and reported zero exact `index 12+` deep overwrites, confirming supplemental target-trio totals `8` versus `17`
- `python tools/profile_solver.py satlib_more/jnh10.cnf | rg -o "learnt_large_success_sub10_step3_source_pop_overwrite_deep_index(11_plus|11|12_plus|12|13_plus)=[0-9]+"` — passed and reported zero exact `index 12+` deep overwrites
- `python tools/profile_solver.py satlib_more/jnh1.cnf | rg -o "learnt_large_success_sub10_step3_source_pop_overwrite_deep_index(11_plus|11|12_plus|12|13_plus)=[0-9]+"` — passed and reported zero exact `index 12+` deep overwrites
- `python tools/agent_queue_check.py` — passed after the final control-plane sync; queue now resolves to `current_or_next_task='perf-058'`
- `python tools/codex_verify.py` — passed after the final control-plane sync (`88/88` tests green plus compile, queue, checker, and wrapper smoke checks)
- `git diff --check` — passed after the final control-plane sync

## Notes For The Next Run

- Start with the read order in `.agent/RUNBOOK.md`.
- Reconcile `STATE.yaml` against the repo tree before selecting a task.
- Keep `PLANS.md` updated for any multi-step or code-bearing task.
- Reuse the queue checker when adjusting `.agent/STATE.yaml` or `.agent/TASK_QUEUE.yaml`.
- The default verifier covers `satsolver_fast.py`, but `satsolver_pysat.py` remains outside the default gate because it requires an optional external environment.
- External libraries or solvers may be used as short-lived research references only; do not retain them in the submission path or make them a default verifier dependency.
- Do not update `benchmark_summary.md` or `experiments.jsonl` for `perf-057`; this run kept no solver change.
- `perf-048` ruled out the whole exact `index 8+` aggregate, `perf-049` showed that the surviving `index 8+` tail is dominated by exact `index 9+`, `perf-050` showed that even the exact `index 9+` aggregate is still too broad for the retained pop-first rewrite, `perf-051` showed that the remaining exact `index 9+` tail is still dominated by exact `index 10+`, `perf-052` showed that even the exact `index 10+` aggregate is still too broad, `perf-053` showed that the surviving `index 10+` tail is itself dominated by exact `index 11+`, `perf-054` showed that even the exact `index 11+` aggregate is still too broad despite a positive dense-anchor and supplemental signal, `perf-055` showed that the remaining exact `index 11+` tail is itself dominated by exact `index 12+`, `perf-056` showed that even the exact `index 12+` aggregate is still too broad despite a positive supplemental signal, and `perf-057` now shows that the remaining exact `index 12+` tail is itself dominated by exact `index 13+`.
- Keep `special/hard.cnf` and `large/test_6.cnf` as the dense exact-step anchor pair, and keep the supplemental `satlib_more` slice (`uuf125-010`, `uf125-01`, `uf125-010`, `jnh10`, `jnh1`) in view because the target trio still shows real deep-overwrite traffic while `jnh10` and `jnh1` remain mostly guardrails.
- `perf-058` should test one bounded solver-core candidate only on the exact `sub10 step-3` deep-overwrite `index 13+` lane before any broader learnt-large relocation rewrite is attempted again.

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
