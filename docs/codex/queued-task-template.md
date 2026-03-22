# Queue Prompt Bridge

The canonical repeated prompt now lives in `QUEUE_PROMPT.md`.

Use that file for future autonomous runs so the agent reads `AGENT.md` and `.agent/*`, continues any current in-progress task, or deterministically selects the next eligible queued task.

If you need a one-line reminder, use:

> Continue the implementation using the repo control plane in `AGENT.md` and `.agent/*`. Read `AGENT.md`, `.agent/RUNBOOK.md`, `.agent/STATE.yaml`, `.agent/TASK_QUEUE.yaml`, `.agent/HANDOFF.md`, `.agent/DECISIONS.md`, and `.agent/TEST_GATES.md`. If `STATE.yaml` has a current in-progress task, continue it. Otherwise pick the highest-priority task whose status is `todo` and whose dependencies are done. Implement one coherent task end-to-end, run the relevant verification, update the control-plane files, and stop. Do not ask for next steps if there is any unblocked `todo` task.
