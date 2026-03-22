# Decisions

## D-001 — 2026-03-22

- Context: The repo already had `AGENTS.md`, `PLANS.md`, and some Codex docs, but no deterministic repo-local queue source of truth.
- Decision: Use `AGENT.md` plus `.agent/STATE.yaml`, `.agent/TASK_QUEUE.yaml`, `.agent/HANDOFF.md`, `.agent/DECISIONS.md`, `.agent/WORKLOG.md`, `.agent/TEST_GATES.md`, and `.agent/RUNBOOK.md` as the authoritative autonomous control plane.
- Consequence: Future unattended runs can continue from repo state rather than relying on operator-written task prompts.

## D-002 — 2026-03-22

- Context: `PLANS.md` already exists and captures durable execution notes for multi-step work.
- Decision: Keep `PLANS.md` as a durable narrative plan and outcome log, but not as the task-selection source of truth.
- Consequence: The queue stays deterministic while historical reasoning and verification notes remain easy to review.

## D-003 — 2026-03-22

- Context: This repo is benchmark-driven, but many queued tasks are tooling or documentation updates.
- Decision: Default autonomous verification remains `python tools/codex_verify.py`, with heavier hotspot or exact-CLI benchmark gates added only for solver-behavior or performance-sensitive tasks.
- Consequence: Routine tasks stay cheap to verify without weakening the safety bar for solver changes.

## D-004 — 2026-03-22

- Context: The queue control plane needs a machine-checkable guard so stale `STATE.yaml` and `TASK_QUEUE.yaml` cannot silently drift during unattended runs.
- Decision: Add `tools/agent_queue_check.py` as the repo-local control-plane consistency oracle and run it from `python tools/codex_verify.py` before unit tests.
- Consequence: Routine verification now fails fast when queue state, task selection hints, or dependency status drift out of sync.

## D-005 — 2026-03-22

- Context: `satsolver.py` and `satsolver_fast.py` duplicated the same DIMACS parsing and result-writing logic, which made wrapper maintenance noisier and risked drift.
- Decision: Introduce `satsolver_io.py` as the shared standard-library helper for DIMACS parsing and result writing, and keep the solver wrappers thin by delegating to it.
- Consequence: Wrapper behavior stays centralized without changing the required CLI contract or solver-core ownership boundaries.
