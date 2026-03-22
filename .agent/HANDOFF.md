# HANDOFF

## Current State

- The repo still uses the queue-driven autonomous control plane rooted in `AGENT.md` and `.agent/*`, plus the machine-checkable queue validator.
- `cp-001`, `cp-002`, `cp-003`, `sat-001`, `tool-001`, `perf-001`, `perf-002`, `perf-003`, `perf-004`, `perf-005`, `perf-006`, `perf-007`, `perf-008`, `perf-009`, `perf-010`, `perf-011`, `perf-012`, `perf-013`, `perf-014`, `perf-015`, `perf-016`, `perf-017`, `perf-018`, `perf-019`, `perf-020`, `perf-021`, and `perf-022` are complete.
- There is no active in-progress task; the next deterministic task is `perf-023`.

## What Changed This Run

- Closed `perf-022` as a measurement-only profiling run with no solver change.
- The supplemental `satlib_more` guard slice split into two distinct families instead of one shared learnt-large lane:
  - `satlib_more/jnh10.cnf` and `satlib_more/jnh1.cnf` are dominated by problem-large relocation (`81.32%` and `87.22%` problem-large relocation pop share) with only tiny learnt-large traffic.
  - `satlib_more/uuf125-010.cnf`, `satlib_more/uf125-01.cnf`, and `satlib_more/uf125-010.cnf` carry the real learnt-large load (`24.11%`, `6.33%`, and `17.49%` learnt-large relocation pop share), and the SAT-side `uf*` cases lean noticeably deeper into `len10+` and step-3+ successful probes than the dense UNSAT anchors.
- That means the next learnt-large experiment should target successful-probe bookkeeping on the `uuf125-010` and `uf*` family while keeping the `jnh*` cases as problem-large guardrails rather than treating all five supplemental cases as one homogeneous lane.
- The queue now advances to `perf-023`, a bounded successful-probe bookkeeping experiment informed by that split.

## Current Focus

- Start `perf-023` next: test one bounded SAT-heavy learnt-large successful-probe bookkeeping candidate using the supplemental slice split from `perf-022`.

## Recommended Next Tasks

- `perf-023` — probe SAT-heavy learnt-large successful-probe bookkeeping after the supplemental slice split

## Verification From This Run

- `python tools/profile_solver.py satlib_more/uuf125-010.cnf satlib_more/jnh10.cnf satlib_more/uf125-01.cnf satlib_more/uf125-010.cnf satlib_more/jnh1.cnf` — passed; the slice split cleanly into `jnh*` problem-large cases and `uuf125-010` plus `uf*` learnt-large cases
- `python tools/codex_verify.py` — passed while `perf-022` was active; the repo compiled, the queue check passed, all 73 tests passed, and both default wrapper smoke paths remained green
- `python tools/agent_queue_check.py` — passed after the final control-plane sync; queue now resolves to `current_or_next_task='perf-023'`
- `python tools/codex_verify.py` — passed after the final control-plane sync
- `git diff --check` — passed

## Notes For The Next Run

- Start with the read order in `.agent/RUNBOOK.md`.
- Reconcile `STATE.yaml` against the repo tree before selecting a task.
- Keep `PLANS.md` updated for any multi-step or code-bearing task.
- Reuse the queue checker when adjusting `.agent/STATE.yaml` or `.agent/TASK_QUEUE.yaml`.
- The default verifier covers `satsolver_fast.py`, but `satsolver_pysat.py` remains outside the default gate because it requires an optional external environment.
- External libraries or solvers may be used as short-lived research references only; do not retain them in the submission path or make them a default verifier dependency.
- Do not update `benchmark_summary.md` or `experiments.jsonl` for `perf-022`; no performance keep survived this run.
- `perf-022` showed that the supplemental slice is heterogeneous: `jnh10` and `jnh1` are overwhelmingly problem-large (`81.32%` and `87.22%` problem-large relocation pop share), not learnt-large.
- The real supplemental learnt-large cases are `uuf125-010`, `uf125-01`, and `uf125-010`; among them, the SAT-side `uf*` pair leans much more heavily into `len10+` and step-3+ successful probes than the dense UNSAT anchors.
- `perf-023` should therefore avoid more failure-tail tweaks and instead test one bounded learnt-large successful-probe bookkeeping candidate that targets the `uuf125-010` and `uf*` family while keeping `jnh10` and `jnh1` in the supplemental guard slice.

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
