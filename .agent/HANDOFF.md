# HANDOFF

## Current State

- The repo still uses the queue-driven autonomous control plane rooted in `AGENT.md` and `.agent/*`, plus the machine-checkable queue validator.
- `cp-001`, `cp-002`, `cp-003`, `sat-001`, `tool-001`, `perf-001`, `perf-002`, `perf-003`, `perf-004`, `perf-005`, `perf-006`, `perf-007`, `perf-008`, `perf-009`, `perf-010`, `perf-011`, `perf-012`, `perf-013`, `perf-014`, `perf-015`, `perf-016`, `perf-017`, `perf-018`, `perf-019`, `perf-020`, `perf-021`, `perf-022`, `perf-023`, `perf-024`, `perf-025`, `perf-026`, `perf-027`, `perf-028`, `perf-029`, `perf-030`, and `perf-031` are complete.
- There is no active in-progress task; the next deterministic task is `perf-032`.

## What Changed This Run

- Closed `perf-031` as a measurement-only profiling run with no solver change.
- The focused seven-case profile showed exact `sub10 step-3` learnt-large traffic across the whole slice, but it is overwhelmingly concentrated in the dense UNSAT anchors: `special/hard.cnf` had `109,933` exact step-3 hits and `large/test_6.cnf` had `94,161`, together about `78.9%` of the total exact step-3 volume in the slice.
- The remaining five cases are much smaller tails by volume, though they still matter as guardrails: `medium/test_4.cnf` and `large/test_10.cnf` were each about `5%` of the total, `large/test_8.cnf` remained the SAT-side guardrail, and `medium/test_3.cnf` plus `satlib_more/uuf150-01.cnf` were small exact-step tails.
- The queue now advances to `perf-032`, a bounded dense-UNSAT solver-core experiment targeted at exact `sub10 step-3` bookkeeping on `special/hard.cnf` and `large/test_6.cnf`, while holding the rest of the focused slice plus the supplemental `satlib_more` cases as guardrails.

## Current Focus

- Start `perf-032` next: test one bounded dense-UNSAT solver-core change aimed at exact `sub10 step-3` learnt-large bookkeeping on `special/hard.cnf` and `large/test_6.cnf`.

## Recommended Next Tasks

- `perf-032` — target dense-UNSAT exact sub-10 step-3 learnt-large bookkeeping after the hotspot refresh

## Verification From This Run

- `python tools/profile_solver.py large/test_6.cnf special/hard.cnf large/test_10.cnf medium/test_4.cnf medium/test_3.cnf satlib_more/uuf150-01.cnf large/test_8.cnf` — passed and showed exact `sub10 step-3` traffic concentrated heavily in `special/hard.cnf` and `large/test_6.cnf`
- `python tools/agent_queue_check.py` — passed after the final control-plane sync; queue now resolves to `current_or_next_task='perf-032'`
- `python tools/codex_verify.py` — passed after the final control-plane sync
- `git diff --check` — passed

## Notes For The Next Run

- Start with the read order in `.agent/RUNBOOK.md`.
- Reconcile `STATE.yaml` against the repo tree before selecting a task.
- Keep `PLANS.md` updated for any multi-step or code-bearing task.
- Reuse the queue checker when adjusting `.agent/STATE.yaml` or `.agent/TASK_QUEUE.yaml`.
- The default verifier covers `satsolver_fast.py`, but `satsolver_pysat.py` remains outside the default gate because it requires an optional external environment.
- External libraries or solvers may be used as short-lived research references only; do not retain them in the submission path or make them a default verifier dependency.
- Do not update `benchmark_summary.md` or `experiments.jsonl` for `perf-031`; this run kept no solver change.
- `perf-030` rules out the direct watched-slot rewrite across the whole exact `sub10 step-3` aggregate, and `perf-031` now shows that the remaining exact step-3 volume is overwhelmingly concentrated in the dense UNSAT anchors rather than spread across the whole focused slice.
- The overlap lane is still ruled out by `perf-024`, the broader short-but-deep aggregate is ruled out by `perf-026`, the exact `step-3/4` aggregate is ruled out for this rewrite by `perf-028`, and the exact `step-3` aggregate is ruled out for the same rewrite by `perf-030`.
- Keep the focused seven-case slice primary, use `special/hard.cnf` plus `large/test_6.cnf` as the dense exact-step anchor pair for `perf-032`, and do not let the next run reopen the whole exact step-3 aggregate without hotspot evidence.

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
