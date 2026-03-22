# HANDOFF

## Current State

- The repo now has a queue-driven autonomous control plane rooted in `AGENT.md` and `.agent/*`, plus a machine-checkable queue validator.
- `cp-001`, `cp-002`, `cp-003`, `sat-001`, and `tool-001` are complete.
- There is no active in-progress task; the next deterministic task is `perf-001`.

## What Changed This Run

- Expanded `tools/codex_verify.py` so the default verification gate now smoke-tests `satsolver_fast.py` in addition to the main submission CLI.
- Added regression coverage for the alternate-wrapper verification flow in `tests/test_codex_verify.py`.
- Updated repo docs and contracts so the default verification scope explicitly includes the standard-library alternate wrapper path.

## Current Focus

- Move to `perf-001`, the portfolio-threshold revalidation task.

## Recommended Next Tasks

1. `perf-001` — revalidate portfolio gating thresholds with same-day benchmark evidence.

## Verification From This Run

- `python -m unittest discover -s tests -p 'test_codex_verify.py' -q` — passed
- `python tools/codex_verify.py` — passed

## Notes For The Next Run

- Start with the read order in `.agent/RUNBOOK.md`.
- Reconcile `STATE.yaml` against the repo tree before selecting a task.
- Keep `PLANS.md` updated for any multi-step or code-bearing task.
- Reuse the new queue checker when adjusting `.agent/STATE.yaml` or `.agent/TASK_QUEUE.yaml`.
- The default verifier now covers `satsolver_fast.py`, but `satsolver_pysat.py` remains outside the default gate because it requires an optional external environment.

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
- Same-day exact-CLI evidence is stronger than stale benchmark history when timing signals are close.
