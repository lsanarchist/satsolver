# HANDOFF

## Current State

- The repo still uses the queue-driven autonomous control plane rooted in `AGENT.md` and `.agent/*`, plus the machine-checkable queue validator.
- `cp-001`, `cp-002`, `cp-003`, `sat-001`, `tool-001`, `perf-001`, `perf-002`, `perf-003`, `perf-004`, `perf-005`, `perf-006`, `perf-007`, `perf-008`, `perf-009`, `perf-010`, `perf-011`, `perf-012`, `perf-013`, `perf-014`, `perf-015`, `perf-016`, `perf-017`, `perf-018`, `perf-019`, `perf-020`, `perf-021`, `perf-022`, `perf-023`, `perf-024`, `perf-025`, `perf-026`, and `perf-027` are complete.
- There is no active in-progress task; the next deterministic task is `perf-028`.

## What Changed This Run

- Closed `perf-027` as a measurement-only profiling run with no solver change.
- Added profiler-only short-deep depth-split counters plus tests so `tools/profile_solver.py` now reports `sub10 step-3/4` and `sub10 step-5+` learnt-large successes separately.
- The surviving short-deep lane is now resolved in favor of `step-3/4` on the real target trio: `uuf125-010` was `2556 vs 573`, `uf125-01` was `21 vs 10`, and `uf125-010` was `225 vs 79` for `step-3/4` versus `step-5+`.
- `jnh10` and `jnh1` stayed low-volume problem-large guardrails and showed no step-5+ learnt-large successes at all, so they do not argue for chasing the deeper tail.
- The queue now advances to `perf-028`, a bounded `sub10 step-3/4` solver-core experiment.

## Current Focus

- Start `perf-028` next: test one bounded solver-core change that only touches `sub10 step-3/4` learnt-large successful relocations.

## Recommended Next Tasks

- `perf-028` — target the sub-10 step-3/4 learnt-large success lane after the depth split

## Verification From This Run

- `python -m unittest discover -s tests -p 'test_profile_solver.py' -q` — passed (`15/15` green, including the new short-deep depth-split coverage)
- `python tools/profile_solver.py satlib_more/uuf125-010.cnf satlib_more/uf125-01.cnf satlib_more/uf125-010.cnf satlib_more/jnh10.cnf satlib_more/jnh1.cnf` — passed and showed the target trio favoring `sub10 step-3/4` over `sub10 step-5+` in every case
- `python tools/codex_verify.py` — passed while `perf-027` was active (`75/75` tests green, compile/checker/wrapper smoke all green)
- `python tools/agent_queue_check.py` — passed after the final control-plane sync; queue now resolves to `current_or_next_task='perf-028'`
- `python tools/codex_verify.py` — passed after the final control-plane sync
- `git diff --check` — passed

## Notes For The Next Run

- Start with the read order in `.agent/RUNBOOK.md`.
- Reconcile `STATE.yaml` against the repo tree before selecting a task.
- Keep `PLANS.md` updated for any multi-step or code-bearing task.
- Reuse the queue checker when adjusting `.agent/STATE.yaml` or `.agent/TASK_QUEUE.yaml`.
- The default verifier covers `satsolver_fast.py`, but `satsolver_pysat.py` remains outside the default gate because it requires an optional external environment.
- External libraries or solvers may be used as short-lived research references only; do not retain them in the submission path or make them a default verifier dependency.
- Do not update `benchmark_summary.md` or `experiments.jsonl` for `perf-027`; this run kept no solver change.
- `perf-027` added two new counters to `tools/profile_solver.py`: `learnt_large_success_sub10_step3_4` and `learnt_large_success_sub10_step5_plus`.
- The overlap lane is still ruled out by `perf-024`, the broader short-but-deep aggregate is ruled out by `perf-026`, and the remaining live direction is now the narrower `sub10 step-3/4` lane rather than the step-5+ tail.
- Keep `jnh10` and `jnh1` in the supplemental slice as problem-large guardrails; do not let `perf-028` drift back into mixed-family, long-clause, or whole-aggregate short-deep rewrites.

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
