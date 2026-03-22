# Queued Task Template

Use this as the initial prompt for future queued Codex runs in this repository.

## Task

- Family: autonomous SAT solver maintenance
- Objective:
- Why it matters:
- Expected outputs: code diff, docs, tests, report
- Priority:

## Context To Read First

- `AGENTS.md`
- `PLANS.md`
- `skills/autonomous-sat-maintenance/SKILL.md`
- `benchmark_summary.md`
- `experiments.jsonl`

## Constraints

- Keep changes small, reviewable, and reversible.
- Prefer existing tools, scripts, and dependencies over adding new ones.
- Use a dedicated worktree and branch when possible.
- Resolve routine ambiguity autonomously.
- Escalate only for destructive actions, missing secrets, approval-gated network access, or product-direction forks.
- Leave durable guidance in repo files, not only in the chat response.

## Execution

1. Create or update the active `PLANS.md` section before editing.
2. Follow `AGENTS.md` and the local skill.
3. Run `python tools/codex_verify.py` after meaningful edits.
4. If solver behavior or performance can change, run a same-day hotspot comparison and the appropriate benchmark path.
5. Update `benchmark_summary.md` and `experiments.jsonl` only for kept or explicitly requested results.
6. Finish with files changed, checks run, remaining risks, and the next sensible follow-up.

## Done When

- `PLANS.md` captures the task and outcome.
- Relevant code, docs, and tests are updated.
- Verification passes.
- The final report is precise and reviewable.
