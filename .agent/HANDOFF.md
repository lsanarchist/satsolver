# HANDOFF

## Current State

- The repo still uses the queue-driven autonomous control plane rooted in `AGENT.md` and `.agent/*`, plus the machine-checkable queue validator.
- `cp-001`, `cp-002`, `cp-003`, `sat-001`, `tool-001`, `perf-001`, `perf-002`, `perf-003`, `perf-004`, `perf-005`, `perf-006`, `perf-007`, `perf-008`, `perf-009`, `perf-010`, `perf-011`, `perf-012`, `perf-013`, `perf-014`, `perf-015`, `perf-016`, `perf-017`, `perf-018`, `perf-019`, `perf-020`, `perf-021`, `perf-022`, `perf-023`, `perf-024`, `perf-025`, `perf-026`, `perf-027`, `perf-028`, `perf-029`, `perf-030`, `perf-031`, and `perf-032` are complete.
- There is no active in-progress task; the next deterministic task is `perf-033`.

## What Changed This Run

- Closed `perf-032` as a retained no-op after testing one bounded dense-UNSAT solver-core rewrite on exact `sub10 step-3` learnt-large successes.
- The exact candidate kept the baseline watched-slot swap and destination append, but changed exact `step-3` source-list removal to use the popped last watcher directly so the relocating clause could skip a redundant self-assignment when it was already last in the source list.
- The dense anchor pair alone improved slightly, `25.1356s -> 24.9710s`, driven by `large/test_6.cnf`, but the focused seven-case slice still regressed from `30.1872s` to `30.4647s`, and the supplemental `satlib_more` slice regressed from `0.3643s` to `0.3799s`.
- A candidate-only `python tools/profile_solver.py large/test_6.cnf special/hard.cnf` run showed unchanged dense hard-case decisions and conflicts on both anchors, so this looks like a same-search bookkeeping split rather than heuristic drift.
- The queue now advances to `perf-033`, a measurement task that profiles exact step-3 source-pop tail-position behavior on the dense anchors before another solver-core edit.

## Current Focus

- Start `perf-033` next: profile exact step-3 source-pop tail-position behavior on `special/hard.cnf` and `large/test_6.cnf`.

## Recommended Next Tasks

- `perf-033` — profile exact step-3 source-pop tail-position behavior on the dense anchors after the self-assignment-skip reject

## Verification From This Run

- `python tools/codex_verify.py` — passed on the temporary `perf-032` candidate (`75/75` tests green, compile/checker/wrapper smoke all green)
- `python tools/hotspot_compare.py --baseline-cli-script /tmp/perf032_dense_step3_baseline/satsolver.py --candidate-cli-script satsolver.py large/test_6.cnf special/hard.cnf` — dense anchor pair improved slightly overall (`25.1356s -> 24.9710s`) but split direction across the two anchors
- `python tools/hotspot_compare.py --baseline-cli-script /tmp/perf032_dense_step3_baseline/satsolver.py --candidate-cli-script satsolver.py large/test_6.cnf special/hard.cnf large/test_10.cnf medium/test_4.cnf medium/test_3.cnf satlib_more/uuf150-01.cnf large/test_8.cnf` — rejected the candidate on the focused seven-case gate (`30.1872s -> 30.4647s`)
- `python tools/hotspot_compare.py --baseline-cli-script /tmp/perf032_dense_step3_baseline/satsolver.py --candidate-cli-script satsolver.py satlib_more/uuf125-010.cnf satlib_more/uf125-01.cnf satlib_more/uf125-010.cnf satlib_more/jnh10.cnf satlib_more/jnh1.cnf` — rejected the candidate on the supplemental slice too (`0.3643s -> 0.3799s`)
- `python tools/profile_solver.py large/test_6.cnf special/hard.cnf` — passed on the temporary candidate and showed unchanged dense hard-case search counters (`72,886/59,201` on `large/test_6.cnf`, `54,245/44,619` on `special/hard.cnf`)
- `python tools/agent_queue_check.py` — passed after the final control-plane sync; queue now resolves to `current_or_next_task='perf-033'`
- `python tools/codex_verify.py` — passed after the final control-plane sync
- `git diff --check` — passed

## Notes For The Next Run

- Start with the read order in `.agent/RUNBOOK.md`.
- Reconcile `STATE.yaml` against the repo tree before selecting a task.
- Keep `PLANS.md` updated for any multi-step or code-bearing task.
- Reuse the queue checker when adjusting `.agent/STATE.yaml` or `.agent/TASK_QUEUE.yaml`.
- The default verifier covers `satsolver_fast.py`, but `satsolver_pysat.py` remains outside the default gate because it requires an optional external environment.
- External libraries or solvers may be used as short-lived research references only; do not retain them in the submission path or make them a default verifier dependency.
- Do not update `benchmark_summary.md` or `experiments.jsonl` for `perf-032`; this run kept no solver change.
- `perf-030` rules out the direct watched-slot rewrite across the whole exact `sub10 step-3` aggregate, and `perf-032` now rules out a source-list self-assignment skip on that dense exact-step lane as a retained keep, even though it stays same-search on the dense anchors.
- The overlap lane is still ruled out by `perf-024`, the broader short-but-deep aggregate is ruled out by `perf-026`, the exact `step-3/4` aggregate is ruled out for the direct rewrite by `perf-028`, and the exact `step-3` aggregate is ruled out for that same rewrite by `perf-030`.
- Keep `special/hard.cnf` and `large/test_6.cnf` as the dense exact-step anchor pair, and do not let `perf-033` jump back into solver-core edits before measuring how often exact step-3 removals actually hit the last-slot self-assignment case on those anchors.

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
