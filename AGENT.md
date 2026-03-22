# AGENT.md

## Project Goal

Maintain a benchmark-driven, standard-library Python SAT solver that stays correct on DIMACS CNF inputs, preserves the required submission CLI contract, and improves through small, verified, durable changes.

## Project Operating Model

- Correctness and repeatability come before speculative speedups.
- Solver changes are benchmark-driven: keep or reject them based on same-day evidence, not intuition alone.
- Prefer small, reviewable, reversible slices over broad rewrites.
- Preserve forward progress for unattended runs by keeping queue state in repo files instead of chat history.
- Use existing repo tools and tests before inventing new workflows.

## Architecture Overview

- `satsolver.py` is the required submission CLI: it parses DIMACS, routes solving, validates internal models, and writes `SAT` or `UNSAT`.
- `satsolver_core.py` contains the shared CDCL implementation, watched literals, activity heuristics, restart logic, root-pure preprocessing, and portfolio gating constants.
- `satsolver_io.py` contains the shared DIMACS parsing and result-writing helpers used by the thin wrappers.
- `satsolver_fast.py` is an alternate comparison wrapper over the shared core with a lighter preprocessing path.
- `satsolver_blaze.py` is a legacy comparison solver kept for benchmark reference.
- `satsolver_pysat.py` is an optional external-library wrapper that must stay outside the standard-library submission path.
- `benchmark_suite.py` runs validated module-mode or exact-CLI benchmarks across the benchmark folders.
- `tools/checker.py` is the output-format and small-UNSAT correctness oracle.
- `tools/codex_verify.py` is the default verification gate: compile, unit tests, SAT smoke, UNSAT smoke, and optional benchmark modes.
- `tools/hotspot_compare.py` and `tools/profile_solver.py` are the focused performance investigation tools.
- `tests/` covers solver regressions, validation tools, benchmark tooling, profiler helpers, and optional wrapper behavior.

## Explicit Non-Goals

- Adding non-standard-library dependencies to the submission path.
- Replacing the required CLI contract with a different interface.
- Keeping speculative performance edits without same-day benchmark evidence.
- Treating benchmark scratch files as durable repo artifacts.
- Introducing a second autonomous workflow that competes with the queue control plane.

## Hard Constraints / Truths To Preserve

- The required invocation stays `python satsolver.py input.cnf output.txt`.
- Submission-path code must remain standard-library only.
- `satsolver_core.py` is the preferred home for shared solving behavior; wrappers stay thin unless the task is explicitly wrapper-specific.
- `tools/checker.py` is the correctness oracle for solver output format.
- `python tools/codex_verify.py` is the default repo-wide verification gate after meaningful changes.
- Performance-sensitive work must use same-day comparison evidence, with exact-CLI validation favored when signals are close.
- `benchmark_summary.md` and `experiments.jsonl` are only updated for kept results or explicitly requested durable reporting.
- Datasets and historical benchmark artifacts are not deleted or rewritten unless the task explicitly calls for it.

## Coding Rules

- Keep changes small, coherent, and reversible.
- Reuse existing parsing, validation, benchmark, and profiling tools where possible.
- Add regression tests for behavior changes or new tooling logic.
- Prefer shared helpers over copy-and-diverge when wrappers have duplicate logic.
- Keep operator-facing docs synchronized with the queue control plane when process assumptions change.
- For non-trivial autonomous work, prefer a dedicated branch or worktree.

## Verification Policy Summary

- Default gate for almost all tasks: `python tools/codex_verify.py`
- Solver-behavior or performance changes: `python tools/codex_verify.py`, then `python tools/hotspot_compare.py ...`, then `python tools/codex_verify.py --benchmark-mode cli --repeat 2` when the focused signal is promising.
- Tooling or docs changes that do not affect solver behavior still run `python tools/codex_verify.py` unless the task is strictly editorial and clearly isolated.
- Do not mark a task done unless its defined verification passes.

## Milestone / Phase Plan

- Phase 0: keep the autonomous queue control plane trustworthy, deterministic, and documented.
- Phase 1: improve solver correctness, maintainability, and shared-code hygiene.
- Phase 2: pursue benchmark-validated performance work and durable experiment reporting.
- Phase 3: polish operator tooling, recovery paths, and secondary documentation.

## Acceptance Criteria

A task is complete when:

- the selected queue task is implemented or conclusively advanced,
- code, docs, and tests needed for that task are updated,
- the required verification passes,
- `.agent/STATE.yaml`, `.agent/TASK_QUEUE.yaml`, `.agent/HANDOFF.md`, and `.agent/WORKLOG.md` reflect repo reality,
- `PLANS.md` captures durable assumptions, verification, and the outcome for multi-step work,
- remaining risks and the next sensible task are recorded for the next unattended run.

## Autonomous Operating Model

This repo uses a repo-local queue control plane:

- `AGENT.md` is the master project contract.
- `.agent/RUNBOOK.md` defines the exact execution loop for autonomous runs.
- `.agent/STATE.yaml` captures the current repo snapshot.
- `.agent/TASK_QUEUE.yaml` is the authoritative prioritized task queue.
- `.agent/HANDOFF.md` is the concise bridge to the next run.
- `.agent/DECISIONS.md` stores durable ADR-style decisions.
- `.agent/WORKLOG.md` is the append-only execution log.
- `.agent/TEST_GATES.md` defines task-type-specific verification expectations.
- `QUEUE_PROMPT.md` contains the stable repeated operator prompt.

Queue rules:

- Every run starts by reading `AGENT.md` and the `.agent/*` files in the runbook order.
- If `.agent/STATE.yaml` names a current in-progress task and that task is still `in_progress`, continue it first.
- Otherwise pick the next task deterministically from `.agent/TASK_QUEUE.yaml`.
- Finish one coherent top-level task per run unless a second task is tightly coupled, trivial by comparison, touches the same files, and is covered by the same verification.
- Update the control-plane files after every meaningful coding run so the same prompt can continue without human task management.

`AGENTS.md` is a supporting Codex-facing shim. If it ever drifts from this file, align `AGENTS.md` back to `AGENT.md` instead of inventing a third workflow.
