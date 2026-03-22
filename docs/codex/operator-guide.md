# Codex Operator Guide

## What This Workflow Does

- Gives queued Codex tasks a deterministic starting point in `AGENT.md`, `.agent/*`, and `QUEUE_PROMPT.md`.
- Standardizes routine verification through `tools/codex_verify.py`.
- Keeps durable context in repo files instead of relying on hidden chat history.
- Uses existing benchmark and validation tools instead of introducing a parallel workflow stack.

## How To Invoke It

1. Create an isolated worktree when the task is more than a tiny doc tweak.
   - `git worktree add ../satsolver-<slug> -b codex/<slug> HEAD`
2. Start Codex in that worktree and paste the stable prompt from `QUEUE_PROMPT.md`.
3. Let Codex read `AGENT.md` and `.agent/*`, select work from `.agent/TASK_QUEUE.yaml`, and keep `PLANS.md` updated for multi-step context.
4. Review the final diff plus the reported checks before merging.

## Default Commands

- Queue/control-plane check: `python tools/agent_queue_check.py`
- Fast verification: `python tools/codex_verify.py`
- Exact-CLI benchmark verification: `python tools/codex_verify.py --benchmark-mode cli --repeat 2`
- Focused same-day comparison: `python tools/hotspot_compare.py --baseline-cli-script <baseline>/satsolver.py --candidate-cli-script satsolver.py ...`

## What Remains Manual

- Choosing between multiple valid product or research directions.
- Deciding whether a noisy benchmark result is strong enough to keep.
- Handling external dependencies or credentials.
- Merging, discarding, or rewriting branches after review.

## Approvals You May Still Need

- Network access or package installs for optional comparison tooling such as `satsolver_pysat.py`.
- Destructive cleanup of datasets, benchmark history, or other repo artifacts.
- Force push, branch deletion, or non-fast-forward git operations.

## Common Failure Recovery

- Dirty worktree before the run:
  - Commit or stash unrelated work, or start a new worktree.
- Queue state disagrees with the repo:
  - Run `python tools/agent_queue_check.py`, then reconcile `.agent/STATE.yaml` and `.agent/TASK_QUEUE.yaml` with reality before touching code.
- `python tools/codex_verify.py` fails:
  - Fix compile, unit-test, or smoke-check failures before benchmarking.
- Hotspot comparison is positive but the broader benchmark is noisy or negative:
  - Trust same-day exact-CLI evidence more than old artifacts and record the mixed result in `PLANS.md`.
- Portfolio or parallel behavior muddies debugging:
  - Rerun with `SATSOLVER_DISABLE_PORTFOLIO=1` for a serial baseline.
- Need to discard an experiment:
  - Revert the candidate cleanly, keep the lesson in `PLANS.md`, and only promote benchmark or history updates for kept results.
