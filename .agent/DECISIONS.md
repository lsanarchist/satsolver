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

## D-006 — 2026-03-22

- Context: After the shared wrapper I/O extraction, routine verification still only smoke-tested the main submission CLI.
- Decision: Make `python tools/codex_verify.py` cover `satsolver_fast.py` smoke checks by default, while keeping `satsolver_pysat.py` out of the default gate because it depends on an optional external environment.
- Consequence: The standard-library alternate wrapper path is now exercised automatically on routine runs without making the default verifier depend on external tooling.

## D-007 — 2026-03-22

- Context: The project now has an open-ended user request to keep optimizing the solver indefinitely while still preserving the standard-library-only submission path.
- Decision: Represent that direction as a rolling queue of bounded benchmark-driven tasks, and allow external libraries or solvers only as short-lived research references that must never become retained submission dependencies.
- Consequence: Future runs can keep making deterministic progress on native-only performance work without weakening the queue discipline or the standard-library constraint.

## D-008 — 2026-03-22

- Context: Fresh same-day external-reference comparison showed that the retained solver still wins the repo-specific structural fast-exit families but trails a mature external backend massively on the dense UNSAT hotspot slice.
- Decision: Treat the external PySAT path as a research ceiling only, and aim the next native-only queue tasks at dense-UNSAT CDCL watch traversal and downstream conflict-analysis rather than at wrapper/startup cleanup or structural fast-exit rewrites.
- Consequence: The queue now preserves the existing structural presolvers as strengths while focusing future native-only experiments on the dense search-heavy core where the remaining gap is largest.

## D-009 — 2026-03-22

- Context: A true watch-family split removed mixed problem-ternary batches as intended, but it also changed the dense UNSAT search path enough to blow up `large/test_6.cnf` from `59,201` to `81,161` conflicts.
- Decision: Treat future watcher-layout or family-order changes as heuristic experiments, not as neutral data-layout refactors, and require the same exact-CLI guardrails as other search-policy work.
- Consequence: The queue should prefer conflict-analysis or other bounded core work next instead of assuming another watch-list rearrangement is a low-risk cleanup.

## D-010 — 2026-03-22

- Context: `perf-009` tried the narrowest plausible relaxed-minimization selector, skipping scans only for learnt `10+`-literal reasons, after fresh dense-UNSAT counters showed that bucket removed very few literals.
- Decision: Treat minimization-result relaxations as SAT-guardrail-sensitive heuristic changes, not as safe bookkeeping cleanup, and prefer same-clause-content conflict-analysis work before revisiting selector-based minimization shortcuts.
- Consequence: Future queue tasks should avoid more “skip these minimization checks” rules for now and instead focus on overhead reductions that preserve the learnt clause contents.

## D-011 — 2026-03-22

- Context: Recent `prepare_learnt_clause()` loop rewrites and primitive substitutions kept losing even when they reduced visible profiler costs, but `perf-012` won by computing best backtrack level and LBD metadata during the learnt-compaction pass itself.
- Decision: Prefer conflict-analysis boundary changes that delete a whole post-minimization pass while preserving learnt clause contents and search counters, rather than smaller `prepare_learnt_clause()` loop-shape or primitive-substitution cleanups.
- Consequence: Future queue tasks can keep exploring same-search analyze-to-finalization boundary work, but should treat isolated final-pass rewrites as low-priority unless they remove materially more work than those rejected micro-optimizations did.

## D-012 — 2026-03-22

- Context: `perf-019` improved the focused seven-case exact-CLI hotspot and the structural fast-exit guardrail, and it preserved dense hard-case decisions/conflicts, but it still regressed the stronger repeat-aware 59-case exact-CLI suite.
- Decision: Treat future learnt-large relocation experiments as needing a broader exact-CLI guard slice than the focused seven-case hotspot before any solver-core keep is accepted.
- Consequence: Follow-on queue tasks on the learnt-large lane should refresh or widen their exact-CLI guard cases before another keep attempt, even when the dense hotspot counters look stable.

## D-013 — 2026-03-22

- Context: `perf-020` showed that the `perf-019` full-suite regression came almost entirely from repeat-aware movement inside the existing focused seven-case slice, while non-focused cases netted nearly flat and only a small `satlib_more` cluster stood out as secondary gross regressions.
- Decision: Keep the existing seven-case learnt-large hotspot slice as the primary early gate, add a compact supplemental `satlib_more` guard slice (`uuf125-010`, `jnh10`, `uf125-01`, `uf125-010`, `jnh1`), and still require the repeat-aware 59-case exact-CLI suite before any keep.
- Consequence: Future learnt-large tasks should not assume that every broad-suite miss implies a totally new hotspot family; instead they should use the focused slice plus the supplemental `satlib_more` slice as early gates and treat the full-suite repeat-aware benchmark as the final keep authority.
