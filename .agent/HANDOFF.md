# HANDOFF

## Current State

- The repo now has a queue-driven autonomous control plane rooted in `AGENT.md` and `.agent/*`, plus a machine-checkable queue validator.
- `cp-001`, `cp-002`, `cp-003`, `sat-001`, `tool-001`, and `perf-001` are complete.
- There is no active in-progress task and no remaining queued `todo` task.

## What Changed This Run

- Revalidated the current portfolio gate against today’s corpus and confirmed that the retained thresholds still route only `large/test_8.cnf` through the portfolio path.
- Tested one bounded scratch candidate that lowered the portfolio clause-count threshold from `1000` to `800`, which would have admitted `large/test_1.cnf`, `large/test_7.cnf`, and `large/test_9.cnf`.
- Rejected that broadened candidate after the same-day exact-CLI hotspot slice regressed from `0.4872s` to `0.6538s`, so no solver code was kept.

## Current Focus

- The queue is complete. Future identical prompts should stop cleanly unless new tasks are added to `.agent/TASK_QUEUE.yaml`.

## Recommended Next Tasks

- None. Add a new queued task before the next autonomous run.

## Verification From This Run

- `python tools/hotspot_compare.py --baseline-cli-script satsolver.py --candidate-cli-script /tmp/scratch_satsolver_portfolio_minclauses800.py --repeat 2 large/test_1.cnf large/test_7.cnf large/test_8.cnf large/test_9.cnf` — candidate rejected
- `python tools/codex_verify.py` — passed

## Notes For The Next Run

- Start with the read order in `.agent/RUNBOOK.md`.
- Reconcile `STATE.yaml` against the repo tree before selecting a task.
- If new work is queued later, keep `PLANS.md` updated for any multi-step or code-bearing task.
- Reuse the queue checker when adjusting `.agent/STATE.yaml` or `.agent/TASK_QUEUE.yaml`.
- The default verifier covers `satsolver_fast.py`, but `satsolver_pysat.py` remains outside the default gate because it requires an optional external environment.

## Immediate Constraints

- Keep the submission path standard-library only.
- Preserve `python satsolver.py input.cnf output.txt`.
- Do not update `benchmark_summary.md` or `experiments.jsonl` unless a performance result is kept.

## Repo Truths To Preserve

- `satsolver_core.py` is the shared CDCL implementation.
- `satsolver_io.py` is the shared DIMACS parsing and result-writing helper for thin wrappers.
- `tools/checker.py` is the correctness oracle for solver output format.
- `tools/agent_queue_check.py` is the control-plane consistency oracle.
- `tools/codex_verify.py` is expected to cover both `satsolver.py` and `satsolver_fast.py` smoke paths by default.
- The retained portfolio thresholds still intentionally gate only `large/test_8.cnf` until a same-day broader threshold change wins cleanly.
- Same-day exact-CLI evidence is stronger than stale benchmark history when timing signals are close.
