# HANDOFF

## Current State

- The repo still uses the queue-driven autonomous control plane rooted in `AGENT.md` and `.agent/*`, plus the machine-checkable queue validator.
- `cp-001`, `cp-002`, `cp-003`, `sat-001`, `tool-001`, `perf-001`, `perf-002`, `perf-003`, `perf-004`, `perf-005`, `perf-006`, `perf-007`, `perf-008`, `perf-009`, `perf-010`, `perf-011`, `perf-012`, `perf-013`, `perf-014`, `perf-015`, `perf-016`, `perf-017`, `perf-018`, `perf-019`, `perf-020`, and `perf-021` are complete.
- There is no active in-progress task; the next deterministic task is `perf-022`.

## What Changed This Run

- Closed `perf-021` as a retained no-op after testing one bounded learnt-large no-replacement tail reorder and reverting it.
- The candidate preserved the dense hard-case search counters, so it looked like same-search bookkeeping, but it still regressed both early gates: the focused seven-case slice (`27.5844s -> 27.6377s`) and the supplemental `satlib_more` slice (`0.3721s -> 0.3774s`).
- That means future learnt-large work should move away from failure-tail branch-order tweaks and instead profile the supplemental `satlib_more` cases directly before choosing the next candidate.
- The queue now advances to `perf-022`, a measurement-only supplemental-slice profiling run.

## Current Focus

- Start `perf-022` next: profile the supplemental `satlib_more` learnt-large guard slice before another solver-core experiment.

## Recommended Next Tasks

- `perf-022` — profile the supplemental satlib_more learnt-large guard slice before the next candidate

## Verification From This Run

- `python tools/codex_verify.py` — passed on the temporary candidate before the performance gates
- `python tools/hotspot_compare.py --baseline-cli-script /tmp/perf021_largeunit_baseline.fb3ecr/satsolver.py --candidate-cli-script satsolver.py large/test_6.cnf special/hard.cnf large/test_10.cnf medium/test_4.cnf medium/test_3.cnf satlib_more/uuf150-01.cnf large/test_8.cnf` — candidate rejected; focused seven-case gate regressed (`27.5844s -> 27.6377s`)
- `python tools/hotspot_compare.py --baseline-cli-script /tmp/perf021_largeunit_baseline.fb3ecr/satsolver.py --candidate-cli-script satsolver.py satlib_more/uuf125-010.cnf satlib_more/jnh10.cnf satlib_more/uf125-01.cnf satlib_more/uf125-010.cnf satlib_more/jnh1.cnf` — candidate rejected; supplemental `satlib_more` gate regressed (`0.3721s -> 0.3774s`)
- `python tools/profile_solver.py large/test_6.cnf special/hard.cnf` — passed; dense hard-case decisions/conflicts stayed unchanged
- `python tools/agent_queue_check.py` — passed; queue now resolves to `current_or_next_task='perf-022'`
- `python tools/codex_verify.py` — passed after the final control-plane sync
- `git diff --check` — passed

## Notes For The Next Run

- Start with the read order in `.agent/RUNBOOK.md`.
- Reconcile `STATE.yaml` against the repo tree before selecting a task.
- Keep `PLANS.md` updated for any multi-step or code-bearing task.
- Reuse the queue checker when adjusting `.agent/STATE.yaml` or `.agent/TASK_QUEUE.yaml`.
- The default verifier covers `satsolver_fast.py`, but `satsolver_pysat.py` remains outside the default gate because it requires an optional external environment.
- External libraries or solvers may be used as short-lived research references only; do not retain them in the submission path or make them a default verifier dependency.
- Do not update `benchmark_summary.md` or `experiments.jsonl` for `perf-021`; no performance keep survived this run.
- The main new lesson is that a large-clause failure-tail unit-first reorder is not the same kind of winner as the earlier ternary tail keep. Even without search drift, it lost both the dense focused slice and the supplemental `satlib_more` slice.
- `perf-022` should use `tools/profile_solver.py` directly on `satlib_more/uuf125-010.cnf`, `satlib_more/jnh10.cnf`, `satlib_more/uf125-01.cnf`, `satlib_more/uf125-010.cnf`, and `satlib_more/jnh1.cnf` so the next learnt-large candidate is driven by the cases that actually pushed back here.

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
