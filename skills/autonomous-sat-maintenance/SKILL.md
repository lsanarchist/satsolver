---
name: autonomous-sat-maintenance
description: Use for queued or minimally supervised work in this SAT solver repo: solver-core changes, tooling updates, benchmark-driven performance experiments, and durable docs or reporting. Follow AGENTS.md and PLANS.md, validate with tools/codex_verify.py, and use hotspot or benchmark tools when performance is involved.
---

# Autonomous SAT Maintenance

## Start

1. Read `AGENTS.md`.
2. Read the active or most recent relevant section in `PLANS.md`.
3. If the task is queued or multi-step, create or update a new top section in `PLANS.md` before editing.

## Choose The Lane

- Correctness or parser or output fix: run `python tools/codex_verify.py`.
- Tooling or docs change: run `python tools/codex_verify.py`; skip benchmark unless behavior changed.
- Solver-core or wrapper performance change: run `python tools/codex_verify.py`, then a same-day A or B with `tools/hotspot_compare.py`, then `python tools/codex_verify.py --benchmark-mode cli --repeat 2` when the hotspot signal is promising.
- Optional external comparison work: keep it out of the submission path and use a separate interpreter or environment explicitly.

## Operating Rules

- Prefer existing tools over ad hoc scripts.
- Keep changes small and reviewable.
- Use a dedicated worktree or branch when the task is not trivial.
- Treat same-day exact-CLI results as stronger than stale artifacts when the signal is small.
- Only update `benchmark_summary.md` and `experiments.jsonl` for kept results or when the task explicitly asks for reporting.
- If a performance idea loses, revert it cleanly and keep the durable lesson in `PLANS.md` or the repo docs instead of leaving half-applied code around.

## Minimal Deliverables

- Updated code, docs, and tests as needed.
- A `PLANS.md` entry with assumptions, verification, and outcome.
- A final handoff that lists changed files, checks, risks, and the next sensible follow-up.
