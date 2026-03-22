# HANDOFF

## Current State

- The repo still uses the queue-driven autonomous control plane rooted in `AGENT.md` and `.agent/*`, plus the machine-checkable queue validator.
- `cp-001`, `cp-002`, `cp-003`, `sat-001`, `tool-001`, `perf-001`, `perf-002`, `perf-003`, `perf-004`, `perf-005`, `perf-006`, `perf-007`, `perf-008`, `perf-009`, `perf-010`, `perf-011`, `perf-012`, `perf-013`, `perf-014`, `perf-015`, `perf-016`, `perf-017`, `perf-018`, `perf-019`, `perf-020`, `perf-021`, `perf-022`, `perf-023`, `perf-024`, `perf-025`, `perf-026`, `perf-027`, `perf-028`, `perf-029`, `perf-030`, `perf-031`, `perf-032`, and `perf-033` are complete.
- There is no active in-progress task; the next deterministic task is `perf-034`.

## What Changed This Run

- Closed `perf-033` as a measurement-only profiling run with no solver change.
- Added profiler-only counters for exact `sub10 step-3` learnt-large source-pop tail position in `tools/profile_solver.py`, plus regression coverage in `tests/test_profile_solver.py`.
- The dense-anchor profile showed that the last-slot self-assignment case is the minority path on both anchors. `large/test_6.cnf` split exact `step-3` hits `17,207` last-slot versus `76,954` overwrite, and `special/hard.cnf` split `20,980` versus `88,953`.
- Combined across the dense anchors, exact `step-3` source-pop traffic is `38,187` last-slot versus `165,907` overwrite, so only about `18.7%` of the lane is the tail case that `perf-032` tried to optimize.
- The queue now advances to `perf-034`, which should target the dominant non-last overwrite path instead of revisiting the tail self-assignment lane as the main experiment.

## Current Focus

- Start `perf-034` next: test one bounded exact `sub10 step-3` dense-anchor bookkeeping candidate that only changes non-last source-pop overwrite cases.

## Recommended Next Tasks

- `perf-034` — target exact step-3 non-last source-pop overwrite bookkeeping on the dense anchors after the tail-position profile

## Verification From This Run

- `python -m unittest discover -s tests -p 'test_profile_solver.py' -q` — passed (`16/16` green, including the new exact step-3 tail-position test)
- `python tools/profile_solver.py large/test_6.cnf special/hard.cnf` — passed and showed that exact dense-anchor `step-3` source-pop traffic is dominated by non-last overwrites, not by last-slot self-assignment
- `python tools/agent_queue_check.py` — passed after the final control-plane sync; queue now resolves to `current_or_next_task='perf-034'`
- `python tools/codex_verify.py` — passed after the final control-plane sync
- `git diff --check` — passed

## Notes For The Next Run

- Start with the read order in `.agent/RUNBOOK.md`.
- Reconcile `STATE.yaml` against the repo tree before selecting a task.
- Keep `PLANS.md` updated for any multi-step or code-bearing task.
- Reuse the queue checker when adjusting `.agent/STATE.yaml` or `.agent/TASK_QUEUE.yaml`.
- The default verifier covers `satsolver_fast.py`, but `satsolver_pysat.py` remains outside the default gate because it requires an optional external environment.
- External libraries or solvers may be used as short-lived research references only; do not retain them in the submission path or make them a default verifier dependency.
- Do not update `benchmark_summary.md` or `experiments.jsonl` for `perf-033`; this run kept no solver change.
- `perf-030` rules out the direct watched-slot rewrite across the whole exact `sub10 step-3` aggregate, and `perf-032` rules out a source-list self-assignment skip as a retained dense-anchor keep even though it stays same-search on those anchors.
- The overlap lane is still ruled out by `perf-024`, the broader short-but-deep aggregate is ruled out by `perf-026`, the exact `step-3/4` aggregate is ruled out for the direct rewrite by `perf-028`, and the exact `step-3` aggregate is ruled out for that same rewrite by `perf-030`.
- Keep `special/hard.cnf` and `large/test_6.cnf` as the dense exact-step anchor pair, and let `perf-034` treat the last-slot tail as a guardrail only: the dominant measured path is still the non-last overwrite lane at about `81%` on both anchors.

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
- Changing the watched-clause family order can materially change the dense UNSAT search path, so future watcher-layout experiments should assume they are heuristic changes, not neutral refactors.
- Even low-yield long learnt-reason removals can be important search signal, so relaxed minimization selectors should be treated as SAT-guardrail-sensitive rather than safe bookkeeping cuts.
- Future learnt-large relocation work should use the focused seven-case slice plus the supplemental `satlib_more` slice (`uuf125-010`, `jnh10`, `uf125-01`, `uf125-010`, `jnh1`) before the full repeat-aware exact-CLI keep gate.
