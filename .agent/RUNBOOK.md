# Autonomous Queue Runbook

## Required Read Order At The Start Of Every Run

1. `AGENT.md`
2. `.agent/STATE.yaml`
3. `.agent/TASK_QUEUE.yaml`
4. `.agent/HANDOFF.md`
5. `.agent/DECISIONS.md`
6. `.agent/TEST_GATES.md`
7. `.agent/WORKLOG.md` (tail only if the file is large)

Read `README.md`, `PLANS.md`, and `skills/autonomous-sat-maintenance/SKILL.md` when the selected task needs broader repo or workflow context.

## Selection Behavior

- If `STATE.yaml.current_task_id` exists and the corresponding task is still `in_progress`, continue it first.
- Otherwise pick the next task deterministically.
- Eligible task means:
  - `status == todo`
  - every `depends_on` task is `done`
  - the task is not explicitly blocked by an active blocker in `STATE.yaml`
- Tie-breaker order:
  - higher `priority`
  - lower `phase`
  - lexical `id`

## Bundling Policy

- Default: finish exactly one top-level task per run.
- A second task is allowed only when it is tightly coupled, trivial compared with the first, already overlaps in touched files, and is covered by the same verification.
- If in doubt, stop after one task.

## Pre-Change Behavior

- Inspect the current repo tree.
- Confirm whether target files already exist.
- Reconcile any mismatch between repo reality and `STATE.yaml`.
- If the queue is stale, update it before coding.
- For multi-step or queued work, add or refresh the active top section in `PLANS.md` before editing code or durable docs.

## Execution Style

- Prefer minimal coherent slices over giant refactors.
- Preserve forward momentum for the next run.
- Do not postpone basic testability.
- If a task is too large, split it into smaller tasks in `TASK_QUEUE.yaml` before coding.
- Prefer shared solver changes in `satsolver_core.py` and keep wrappers thin unless the task is explicitly wrapper-specific.

## Verification Rule

- Run the narrowest meaningful verification for the task plus any mandatory global gates from `TEST_GATES.md`.
- Record exact commands and high-level outcomes in `WORKLOG.md`.
- Do not mark a task `done` if its required verification failed.

## Control-Plane Update Rule After Coding

- Mark the task `done` in `TASK_QUEUE.yaml` if completed.
- If incomplete, keep it `in_progress` and record the exact remainder.
- Update `STATE.yaml` with:
  - `current_task_id`
  - `last_completed_task_id`
  - `current_phase`
  - `blockers`
  - `recent_files`
- Update `HANDOFF.md` with:
  - what changed
  - what is most sensible next
  - exact verify commands if special handling is needed
- Append a `WORKLOG.md` entry.
- Append a `DECISIONS.md` entry when architecture or process assumptions changed.
- Keep `PLANS.md` synchronized for multi-step or autonomous tasks.

## Blocker Handling

- Mark blocked tasks as `blocked` in `TASK_QUEUE.yaml`.
- Add concise blockers to `STATE.yaml`.
- Explain unblock conditions in `HANDOFF.md`.
- Pick the next unblocked task if one exists.
- Do not ask the operator for next steps unless the repo is truly blocked and no useful unblocked task remains.

## Branch Policy

- One autonomous worker per branch or per worktree.
- Never allow two active runs writing the same branch.
- If parallel workers exist, give them disjoint task sets or separate branches/worktrees.
- Before merge, refresh the control-plane files from the target branch and resolve conflicts carefully.

## What Counts As A Good Run

A good run:

- leaves the repo better than before,
- finishes one coherent task or a tightly coupled pair,
- verifies the result,
- updates the control plane so the same prompt can continue without human help.
