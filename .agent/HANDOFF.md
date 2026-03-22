# HANDOFF

## Current State

- The repo now has a queue-driven autonomous control plane rooted in `AGENT.md` and `.agent/*`, plus a machine-checkable queue validator.
- `cp-001`, `cp-002`, `cp-003`, `sat-001`, `tool-001`, `perf-001`, `perf-002`, `perf-003`, and `perf-004` are complete.
- The queue has been reopened with a rolling native-only optimization program.
- There is no active in-progress task; the next deterministic task is `perf-005`.

## What Changed This Run

- Profiled the refreshed hotspot baseline and confirmed that direct `reduce_database()` bookkeeping is too small to justify another locked-set or schedule-cleanup branch by itself.
- Tested one bounded clause-storage classifier that demoted `10+`-literal learnt clauses within each LBD bucket while keeping the same top-half reduction schedule.
- Reverted that temporary solver change after the refreshed seven-case exact-CLI gate regressed catastrophically, especially on `large/test_8.cnf`, and recorded `perf-004` as a retained-noop conclusion.

## Current Focus

- Start `perf-005` next: test one bounded branching or restart heuristic change against the refreshed seven-case hotspot slice.

## Recommended Next Tasks

- `perf-005` — test one bounded branching or restart heuristic change after the new baseline
- `perf-006` — measure wrapper and startup overhead only after the solver-core heavy UNSAT slice has been rechecked
- `perf-007` — use optional external solver references only after the native-only heuristic lanes have been revisited

## Verification From This Run

- `python tools/profile_solver.py large/test_6.cnf special/hard.cnf medium/test_4.cnf large/test_8.cnf` — passed
- `python -m cProfile -s tottime satsolver.py medium/test_4.cnf /tmp/perf004_profile_medium4.txt | head -n 40` — passed
- `python tools/codex_verify.py` — passed
- `python tools/hotspot_compare.py --baseline-cli-script /tmp/perf004_lenbucket_baseline.TE0c9p/satsolver.py --candidate-cli-script satsolver.py large/test_6.cnf special/hard.cnf large/test_10.cnf medium/test_4.cnf medium/test_3.cnf satlib_more/uuf150-01.cnf large/test_8.cnf` — candidate rejected (`30.0666s -> 72.6652s` two-order average; `large/test_8.cnf` exploded to `25s..27s`)
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
- `perf-004` showed that clause-database classifier tweaks can still be wildly unstable on `large/test_8.cnf`, even when they look motivated by UNSAT-heavy learnt-large telemetry.
- The top two cases alone, `large/test_6.cnf` and `special/hard.cnf`, still account for `72.95%` of the exact-CLI total, but the next deterministic task is now `perf-005`, so the next run should probe branching or restart heuristics instead of more learnt-retention tweaks.

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
