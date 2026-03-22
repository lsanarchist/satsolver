# Test Gates

## General Rules

- Do not mark a task `done` if its defined verification did not pass.
- If verification fails, either fix it in the same run or leave the task `in_progress` with the exact remainder in `HANDOFF.md`.
- Record exact verification commands and outcomes in `WORKLOG.md`.

## Build-Graph Or Wiring Changes

Applies to:

- CLI entrypoint changes
- shared helper extraction that changes imports or module boundaries
- benchmark harness wiring
- verification-helper wiring

Required verification:

- `python tools/codex_verify.py`
- Add `python tools/codex_verify.py --benchmark-mode cli --benchmark-folders small special` if the CLI path or benchmark execution flow changed materially

## Pure Logic Changes

Applies to:

- solver core heuristics
- DIMACS parsing semantics
- output formatting
- validation logic

Required verification:

- `python tools/codex_verify.py`
- Add targeted unit tests when logic branches or failure paths change
- If solver behavior or performance can change, also run:
  - `python tools/hotspot_compare.py ...`
  - `python tools/codex_verify.py --benchmark-mode cli --repeat 2`

## SQL / Migration Changes

This repo currently has no SQL or migration layer.

Rule:

- If such a task appears unexpectedly, treat it as a queue or task-definition problem and do not mark it done until the queue is corrected or the scope is explicitly justified.

## External Adapter Changes

Applies to:

- `satsolver_pysat.py`
- optional comparison tooling that depends on `.venv-external-sat` or other external environments

Required verification:

- `python tools/codex_verify.py` for the standard-library submission path
- Any adapter-specific command needed to prove the external path still works

Completion rule:

- If the required external environment is unavailable, do not mark the adapter task done; leave it `blocked` or `in_progress` with the missing dependency recorded.

## Replay / Renderer Changes

This repo has no replay engine or UI renderer. Treat rendered benchmark or comparison text output as the closest equivalent.

Applies to:

- `benchmark_suite.py` output formatting
- `tools/hotspot_compare.py` report rendering

Required verification:

- targeted unit tests for the touched reporting tool
- `python tools/codex_verify.py`

## Documentation And Control-Plane Changes

Applies to:

- `AGENT.md`
- `.agent/*`
- operator docs
- queue prompts

Required verification:

- `python tools/agent_queue_check.py`
- `python tools/codex_verify.py`
- manual consistency check that `STATE.yaml`, `TASK_QUEUE.yaml`, `HANDOFF.md`, and `WORKLOG.md` describe the same repo reality

## Failure Handling Rules

- Prefer fixing verification failures in the same run.
- If a failure reveals stale queue state, repair the queue before stopping.
- If a task is blocked, mark it `blocked`, record the blocker in `STATE.yaml`, explain the unblock condition in `HANDOFF.md`, and continue with the next eligible task if one exists.
