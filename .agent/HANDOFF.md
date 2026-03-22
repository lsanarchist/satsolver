# HANDOFF

## Current State

- The repo now has a queue-driven autonomous control plane rooted in `AGENT.md` and `.agent/*`, plus a machine-checkable queue validator.
- `cp-001`, `cp-002`, `cp-003`, `sat-001`, `tool-001`, `perf-001`, `perf-002`, `perf-003`, `perf-004`, and `perf-005` are complete.
- The queue has been reopened with a rolling native-only optimization program.
- There is no active in-progress task; the next deterministic task is `perf-006`.

## What Changed This Run

- Tested one bounded restart-policy classifier instead of revisiting the already-rejected branch-frontier and heap lanes: trigger an early root restart only when a conflict learns an `LBD <= 3` clause after at least half of the current Luby window has elapsed.
- Reverted that temporary solver change after the refreshed seven-case exact-CLI gate regressed on every measured case.
- Recorded `perf-005` as a retained-noop conclusion and advanced the queue to the wrapper/startup lane.

## Current Focus

- Start `perf-006` next: measure wrapper and startup overhead against the refreshed seven-case hotspot slice.

## Recommended Next Tasks

- `perf-006` — measure wrapper and startup overhead only after the solver-core heavy UNSAT slice has been rechecked
- `perf-007` — use optional external solver references only after the native-only heuristic lanes have been revisited

## Verification From This Run

- `python tools/codex_verify.py` — passed
- `python tools/hotspot_compare.py --baseline-cli-script /tmp/perf005_restart_baseline.c4riuk/satsolver.py --candidate-cli-script satsolver.py large/test_6.cnf special/hard.cnf large/test_10.cnf medium/test_4.cnf medium/test_3.cnf satlib_more/uuf150-01.cnf large/test_8.cnf` — candidate rejected (`34.7641s -> 56.2904s` two-order average; `large/test_8.cnf` rose to about `7.5s`)
- `python tools/agent_queue_check.py` — passed
- `python tools/codex_verify.py` — passed
- `git diff --check` — passed

## Notes For The Next Run

- Start with the read order in `.agent/RUNBOOK.md`.
- Reconcile `STATE.yaml` against the repo tree before selecting a task.
- Keep `PLANS.md` updated for any multi-step or code-bearing task.
- Reuse the queue checker when adjusting `.agent/STATE.yaml` or `.agent/TASK_QUEUE.yaml`.
- The default verifier covers `satsolver_fast.py`, but `satsolver_pysat.py` remains outside the default gate because it requires an optional external environment.
- External libraries or solvers may be used as short-lived research references only; do not retain them in the submission path or make them a default verifier dependency.
- After each performance experiment, either split the next evidence-backed task into `.agent/TASK_QUEUE.yaml` or record a retained-noop conclusion; do not collapse the queue back into one endless vague task.
- The refreshed baseline totaled `32.2896s` representative exact-CLI time over `59` cases, and the seven-case slice still covers `90.82%` of that total while keeping `large/test_8.cnf` as the SAT-like guardrail.
- `perf-005` showed that even a conservative low-LBD early-restart trigger can regress every hotspot case and still destabilize `large/test_8.cnf`, so future restart work should stay skeptical of conflict-quality-triggered early restarts without a much stronger classifier.
- The top two cases alone, `large/test_6.cnf` and `special/hard.cnf`, still account for `72.95%` of the exact-CLI total, but the next deterministic task is now `perf-006`, so the next run should probe wrapper/startup overhead instead of more solver-core heuristic drift.

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
- `large/test_8.cnf` is an important SAT-like guardrail for learnt-database experiments because extra retained clause load can destabilize it dramatically.
- `large/test_8.cnf` is also an important guardrail for restart-policy experiments because even conservative restart drift can destabilize it badly.
