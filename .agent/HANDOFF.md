# HANDOFF

## Current State

- The repo now has a queue-driven autonomous control plane rooted in `AGENT.md` and `.agent/*`, plus a machine-checkable queue validator.
- `cp-001`, `cp-002`, and `cp-003` are complete.
- There is no active in-progress task; the next deterministic task is `sat-001`.

## What Changed This Run

- Added `tools/agent_queue_check.py`, a standard-library validator for `.agent/STATE.yaml` and `.agent/TASK_QUEUE.yaml`.
- Added `tests/test_agent_queue_check.py` and wired the checker into `tools/codex_verify.py` so routine verification fails fast on stale queue state.
- Updated repo docs and test-gate guidance to include the standalone queue-check command.

## Current Focus

- Move to `sat-001`, the shared DIMACS parsing and result-writing deduplication task.

## Recommended Next Tasks

1. `sat-001` — deduplicate duplicate DIMACS parsing and result-writing helpers across `satsolver.py` and `satsolver_fast.py`.
2. `tool-001` — expand wrapper-oriented verification after the shared helper extraction lands.

## Verification From This Run

- `python tools/agent_queue_check.py` — passed
- `python -m unittest discover -s tests -q` — passed
- `python tools/codex_verify.py` — passed

## Notes For The Next Run

- Start with the read order in `.agent/RUNBOOK.md`.
- Reconcile `STATE.yaml` against the repo tree before selecting a task.
- Keep `PLANS.md` updated for any multi-step or code-bearing task.
- Reuse the new queue checker when adjusting `.agent/STATE.yaml` or `.agent/TASK_QUEUE.yaml`.

## Immediate Constraints

- Keep the submission path standard-library only.
- Preserve `python satsolver.py input.cnf output.txt`.
- Do not update `benchmark_summary.md` or `experiments.jsonl` unless a performance result is kept.

## Repo Truths To Preserve

- `satsolver_core.py` is the shared CDCL implementation.
- `tools/checker.py` is the correctness oracle for solver output format.
- `tools/agent_queue_check.py` is the control-plane consistency oracle.
- Same-day exact-CLI evidence is stronger than stale benchmark history when timing signals are close.
