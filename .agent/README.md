# .agent Control Plane

## File Roles

- `STATE.yaml` — current snapshot of repo truth
- `TASK_QUEUE.yaml` — authoritative prioritized task list with dependencies
- `HANDOFF.md` — concise human-readable current context
- `DECISIONS.md` — append-only ADR-style decision log
- `WORKLOG.md` — append-only execution log with commands and outcomes
- `TEST_GATES.md` — verification policy by task type
- `RUNBOOK.md` — exact loop every autonomous run must follow

## Update Rule

After every meaningful coding run, update at least:

- `STATE.yaml`
- `TASK_QUEUE.yaml`
- `HANDOFF.md`
- `WORKLOG.md`

Also update `DECISIONS.md` when architecture or process assumptions change, and keep `AGENT.md` synchronized when project truths change.

## Selection Rule

- Continue `STATE.yaml.current_task_id` first if that task still exists and is `in_progress`.
- Otherwise pick the highest-priority `todo` task whose dependencies are done and that is not blocked by an active blocker in `STATE.yaml`.
- Deterministic tie-breaker: higher priority, lower phase, lexical id.

The queue is the source of truth for what to do next. Do not replace it with ad hoc notes.
