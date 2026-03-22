# HANDOFF

## Current State

- The repo still uses the queue-driven autonomous control plane rooted in `AGENT.md` and `.agent/*`, plus the machine-checkable queue validator.
- `cp-001`, `cp-002`, `cp-003`, `sat-001`, `tool-001`, `perf-001`, `perf-002`, `perf-003`, `perf-004`, `perf-005`, `perf-006`, `perf-007`, `perf-008`, `perf-009`, `perf-010`, `perf-011`, `perf-012`, `perf-013`, `perf-014`, `perf-015`, `perf-016`, `perf-017`, `perf-018`, `perf-019`, and `perf-020` are complete.
- There is no active in-progress task; the next deterministic task is `perf-021`.

## What Changed This Run

- Closed `perf-020` as a measurement-only guard-refresh run; no solver code changed.
- The key finding is that the `perf-019` broad-suite reject was not mainly caused by some brand-new non-hotspot family. The existing focused seven-case slice already accounted for almost all of the full-suite regression (`+0.4541s`), while all non-focused cases netted to only `-0.0026s`.
- The strongest secondary non-focused gross regressions did cluster in `satlib_more`, so future learnt-large relocation experiments now carry one compact supplemental guard slice: `satlib_more/uuf125-010.cnf`, `satlib_more/jnh10.cnf`, `satlib_more/uf125-01.cnf`, `satlib_more/uf125-010.cnf`, and `satlib_more/jnh1.cnf`.
- A fresh retained-baseline repeat-aware exact-CLI rerun stayed `59/59` correct and kept the same slow-case ordering, even though the absolute total drifted noisily on this machine.

## Current Focus

- Start `perf-021` next: test one bounded learnt-large relocation candidate against the existing focused seven-case slice, the supplemental satlib_more slice, and the repeat-aware full suite.

## Recommended Next Tasks

- `perf-021` — test the next learnt-large relocation idea against the refreshed guard slices

## Verification From This Run

- `python - <<'PY'` parse of `/tmp/perf019_baseline_cli_repeat2.txt` vs `/tmp/sat-codex-benchmark-6_2z0guq.txt` — passed; focused seven-case delta `+0.4541s`, non-focused delta `-0.0026s`, supplemental satlib_more gross regressions identified
- `python tools/profile_solver.py large/test_6.cnf special/hard.cnf` — passed; dense hard-case decisions/conflicts and learnt-large shares stayed unchanged
- `python tools/codex_verify.py --benchmark-mode cli --repeat 2` — passed; retained solver stayed `59/59` correct at `30.3111s` representative / `60.6223s` measured on this rerun
- `python tools/agent_queue_check.py` — passed; queue now resolves to `current_or_next_task='perf-021'`
- `python tools/codex_verify.py` — passed after the final control-plane sync
- `git diff --check` — passed

## Notes For The Next Run

- Start with the read order in `.agent/RUNBOOK.md`.
- Reconcile `STATE.yaml` against the repo tree before selecting a task.
- Keep `PLANS.md` updated for any multi-step or code-bearing task.
- Reuse the queue checker when adjusting `.agent/STATE.yaml` or `.agent/TASK_QUEUE.yaml`.
- The default verifier covers `satsolver_fast.py`, but `satsolver_pysat.py` remains outside the default gate because it requires an optional external environment.
- External libraries or solvers may be used as short-lived research references only; do not retain them in the submission path or make them a default verifier dependency.
- Do not update `benchmark_summary.md` or `experiments.jsonl` for `perf-020`; no performance keep survived this run.
- For future learnt-large relocation experiments, treat the existing seven-case slice as the primary early gate and the supplemental `satlib_more` slice as a secondary early-warning slice, not as a replacement for the full-suite repeat-aware exact-CLI gate.
- `special/hard.cnf` remains the single biggest sensitivity inside the focused seven-case lane, so do not overfit the next candidate to `large/test_6.cnf` alone.

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
