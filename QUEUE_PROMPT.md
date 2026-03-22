# Stable Queue Prompt

Use this prompt for repeated autonomous runs in this repository.

## Default Prompt

Continue the implementation using the repo control plane in `AGENT.md` and `.agent/*`. Read `AGENT.md`, `.agent/RUNBOOK.md`, `.agent/STATE.yaml`, `.agent/TASK_QUEUE.yaml`, `.agent/HANDOFF.md`, `.agent/DECISIONS.md`, and `.agent/TEST_GATES.md`. If `STATE.yaml` has a current in-progress task, continue it. Otherwise pick the highest-priority task whose status is `todo` and whose dependencies are done. Implement one coherent task end-to-end, run the relevant verification, update the control-plane files, and stop. Do not ask for next steps if there is any unblocked `todo` task.

## Stricter Variant

Continue the implementation using the repo control plane in `AGENT.md` and `.agent/*`. Read `AGENT.md`, `.agent/RUNBOOK.md`, `.agent/STATE.yaml`, `.agent/TASK_QUEUE.yaml`, `.agent/HANDOFF.md`, `.agent/DECISIONS.md`, and `.agent/TEST_GATES.md`. If `STATE.yaml` has a current in-progress task, continue it. Otherwise pick the highest-priority task whose status is `todo` and whose dependencies are done. Finish exactly one top-level task per run, or one tightly coupled pair only when verification overlap makes that cheaper. Implement the task end-to-end, run the relevant verification, update `STATE.yaml`, `TASK_QUEUE.yaml`, `HANDOFF.md`, `WORKLOG.md`, and `DECISIONS.md` if needed, then stop. Do not ask the user what to do next if any unblocked `todo` task remains.

## Universal Operating Rules

- Use the task queue, not intuition.
- Keep first runs small and verifiable.
- Prefer minimal coherent slices over broad rewrites.
- Keep the repo buildable and testable after each run.
- Keep exact verification commands in `WORKLOG.md`.
- Keep architecture assumptions in `DECISIONS.md`.
- Keep `STATE.yaml` and `TASK_QUEUE.yaml` synchronized with repo reality.
- Never weaken the queue system into loose note-taking.
- The queue remains the source of truth for what to do next.

## Bootstrap Behavior

When the control plane is missing or incomplete:

1. Inspect the repo and infer its actual shape from code, docs, tests, scripts, and file layout.
2. Create `AGENT.md` with concrete repo-specific guidance.
3. Create `.agent/` and all required control-plane files.
4. Build an initial phased `TASK_QUEUE.yaml` from repo reality.
5. Seed `STATE.yaml` with an honest repo snapshot.
6. Seed `HANDOFF.md` with the current state and sensible next work.
7. Seed `WORKLOG.md` with a bootstrap entry.
8. Create `QUEUE_PROMPT.md`.
9. If a first real queue task is tightly coupled and verifiable in the same run, complete it too.

## Commit Behavior

- If the environment allows commits and the project expects them, create one clean commit after a verified run.
- If commits are not wanted, stop cleanly after updating the control plane.

## Success Condition

Leave the repo in a state where this same prompt can be submitted again and the next run will continue correctly without fresh human task management.
