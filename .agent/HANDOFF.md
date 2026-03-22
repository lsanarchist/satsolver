# HANDOFF

## Current State

- The repo still uses the queue-driven autonomous control plane rooted in `AGENT.md` and `.agent/*`, plus the machine-checkable queue validator.
- `cp-001`, `cp-002`, `cp-003`, `sat-001`, `tool-001`, `perf-001`, `perf-002`, `perf-003`, `perf-004`, `perf-005`, `perf-006`, `perf-007`, `perf-008`, `perf-009`, `perf-010`, `perf-011`, `perf-012`, `perf-013`, `perf-014`, `perf-015`, `perf-016`, `perf-017`, `perf-018`, `perf-019`, `perf-020`, `perf-021`, `perf-022`, and `perf-023` are complete.
- There is no active in-progress task; the next deterministic task is `perf-024`.

## What Changed This Run

- Closed `perf-023` as a retained no-op after testing one bounded learnt-large successful-probe bookkeeping candidate and reverting it.
- The candidate used a selective learnt-large success-path rewrite on clauses that were either `len10+` or reached step-3+ successful probes.
- That rewrite improved the supplemental `satlib_more` slice overall (`0.4030s -> 0.3883s`), mainly because `satlib_more/uuf125-010.cnf` improved strongly in both orders, but it still regressed the primary focused seven-case gate overall (`34.9357s -> 35.1656s`), led by losses on `large/test_6.cnf`, `medium/test_4.cnf`, and the SAT guardrail `large/test_8.cnf`.
- The durable lesson is that the broader OR-gated rewrite is still too wide for the dense anchors. The next follow-up should narrow the lane further to the true long-and-deep overlap (`len10+` and step-3+ successful probes) instead of abandoning the learnt-large success-path lane entirely.
- The queue now advances to `perf-024`, a narrower long-and-deep successful-probe experiment.

## Current Focus

- Start `perf-024` next: test one narrower learnt-large successful-probe bookkeeping candidate aimed only at the true long-and-deep supplemental lane.

## Recommended Next Tasks

- `perf-024` — narrow learnt-large successful-probe bookkeeping to the true long-and-deep lane

## Verification From This Run

- `python tools/codex_verify.py` — passed on the temporary candidate before the performance gates
- `python tools/hotspot_compare.py --baseline-cli-script /tmp/perf023_deepprobe_baseline.LEc9o4/satsolver.py --candidate-cli-script satsolver.py large/test_6.cnf special/hard.cnf large/test_10.cnf medium/test_4.cnf medium/test_3.cnf satlib_more/uuf150-01.cnf large/test_8.cnf` — candidate rejected on the primary early gate (`34.9357s -> 35.1656s`)
- `python tools/hotspot_compare.py --baseline-cli-script /tmp/perf023_deepprobe_baseline.LEc9o4/satsolver.py --candidate-cli-script satsolver.py satlib_more/uuf125-010.cnf satlib_more/uf125-01.cnf satlib_more/uf125-010.cnf satlib_more/jnh10.cnf satlib_more/jnh1.cnf` — passed as a targeted signal (`0.4030s -> 0.3883s`), but not enough to offset the focused-gate regression
- `python tools/agent_queue_check.py` — passed after the final control-plane sync; queue now resolves to `current_or_next_task='perf-024'`
- `python tools/codex_verify.py` — passed after the final control-plane sync
- `git diff --check` — passed

## Notes For The Next Run

- Start with the read order in `.agent/RUNBOOK.md`.
- Reconcile `STATE.yaml` against the repo tree before selecting a task.
- Keep `PLANS.md` updated for any multi-step or code-bearing task.
- Reuse the queue checker when adjusting `.agent/STATE.yaml` or `.agent/TASK_QUEUE.yaml`.
- The default verifier covers `satsolver_fast.py`, but `satsolver_pysat.py` remains outside the default gate because it requires an optional external environment.
- External libraries or solvers may be used as short-lived research references only; do not retain them in the submission path or make them a default verifier dependency.
- Do not update `benchmark_summary.md` or `experiments.jsonl` for `perf-023`; no performance keep survived this run.
- `perf-023` showed that the broad selective rule (`len10+` or step-3+ successful probes) is still too wide. It helped `uuf125-010` enough to lift the supplemental slice, but it still lost the primary focused seven-case gate.
- The next follow-up should narrow further to the true long-and-deep overlap instead of touching all long or all deep learnt-large successes.
- Keep `jnh10` and `jnh1` in the supplemental slice as problem-large guardrails; do not let the next learnt-large candidate silently drift into a mixed-family rewrite again.

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
