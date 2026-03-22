# PLANS.md

Use this file for queued or multi-step Codex work so the execution state survives beyond a single chat turn.

## How To Use This File

- Add a new section at the top for each queued task.
- Keep one active section at a time.
- Record assumptions, plan steps, commands run, and the final outcome.
- Use short durable notes, not a full transcript.
- When the task is finished, mark the section completed and keep only the verification and conclusion that future runs need.

## Template

## YYYY-MM-DD `<task-slug>`

- Status: active
- Task family:
- Branch/worktree:
- Prompt summary:
- Assumptions:
- Escalations:

### Plan

- [ ] Step 1
- [ ] Step 2
- [ ] Step 3

### Verification

- `command`
- result

### Outcome

- Short summary

### Remaining risks

- Risk or `none`

## 2026-03-22 `codex-autonomous-workflow-bootstrap`

- Status: completed
- Task family: autonomous SAT solver maintenance
- Branch/worktree: current checkout
- Prompt summary: bootstrap a repo-native Codex workflow for future queued tasks with minimal human steering
- Assumptions:
  - The missing task-family placeholder should default to benchmark-driven SAT solver maintenance for this repo.
  - Existing benchmark and experiment files remain the durable history for future solver work.
- Escalations: none

### Plan

- [x] Inspect repo structure, commands, and current benchmark conventions.
- [x] Create durable repo instructions in `AGENTS.md`.
- [x] Add a reusable skill, operator guide, and queued-task template.
- [x] Add a small verification helper and test coverage for it.
- [x] Run verification and capture outcomes here.

### Verification

- `python -m unittest discover -s tests -q`
- `python tools/codex_verify.py`
- `python tools/codex_verify.py --benchmark-mode cli --benchmark-folders small special`

### Outcome

- Added a repo-native Codex workflow layer that routes autonomous runs through `AGENTS.md`, this plan file, a local skill, a reusable verification helper, and operator-facing docs.
- Kept the workflow bounded: default checks are fast, benchmark verification is opt-in, and existing repo tools remain the underlying validation surface.

### Remaining risks

- Worktree creation is documented rather than scripted.
- Performance experiments still require judgment about how much benchmark evidence is enough for a keep or revert decision.
