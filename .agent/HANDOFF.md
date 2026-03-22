# HANDOFF

## Current State

- The repo now has a queue-driven autonomous control plane rooted in `AGENT.md` and `.agent/*`, plus a machine-checkable queue validator.
- `cp-001`, `cp-002`, `cp-003`, and `sat-001` are complete.
- There is no active in-progress task; the next deterministic task is `tool-001`.

## What Changed This Run

- Added `satsolver_io.py`, a shared DIMACS parsing and result-writing helper module.
- Updated `satsolver.py`, `satsolver_fast.py`, and `satsolver_pysat.py` to use the shared helper while preserving their public APIs.
- Added `tests/test_solver_io.py` and refreshed the repo map in `AGENT.md`, `AGENTS.md`, and `README.md`.

## Current Focus

- Move to `tool-001`, the wrapper-oriented verification expansion that builds on the new shared helper.

## Recommended Next Tasks

1. `tool-001` — expand wrapper-oriented verification now that the shared helper module is in place.
2. `perf-001` — revalidate portfolio gating thresholds once wrapper and verification maintenance is settled.

## Verification From This Run

- `python tools/agent_queue_check.py` — passed
- `python -m unittest discover -s tests -q` — passed (70 tests)
- `python tools/codex_verify.py` — passed

## Notes For The Next Run

- Start with the read order in `.agent/RUNBOOK.md`.
- Reconcile `STATE.yaml` against the repo tree before selecting a task.
- Keep `PLANS.md` updated for any multi-step or code-bearing task.
- Reuse the new queue checker when adjusting `.agent/STATE.yaml` or `.agent/TASK_QUEUE.yaml`.
- The shared wrapper I/O path now lives in `satsolver_io.py`, so wrapper verification should target that path directly.

## Immediate Constraints

- Keep the submission path standard-library only.
- Preserve `python satsolver.py input.cnf output.txt`.
- Do not update `benchmark_summary.md` or `experiments.jsonl` unless a performance result is kept.

## Repo Truths To Preserve

- `satsolver_core.py` is the shared CDCL implementation.
- `satsolver_io.py` is the shared DIMACS parsing and result-writing helper for thin wrappers.
- `tools/checker.py` is the correctness oracle for solver output format.
- `tools/agent_queue_check.py` is the control-plane consistency oracle.
- Same-day exact-CLI evidence is stronger than stale benchmark history when timing signals are close.
