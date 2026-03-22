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

## 2026-03-22 `perf-001-portfolio-gate-revalidation`

- Status: completed
- Task family: benchmark-driven portfolio-threshold revalidation
- Branch/worktree: current checkout
- Prompt summary: continue the next deterministic queue task, `perf-001`, by revalidating the current portfolio gating thresholds against same-day evidence and either keeping a threshold change or recording a retained-noop conclusion with rationale
- Assumptions:
  - The current gate still appears to collapse to a single live benchmark case, so the first bounded revalidation should test whether a nearby threshold broadening earns enough same-day hotspot improvement to justify a broader exact-CLI run.
  - Temporary scratch candidates in `/tmp` are acceptable for rejected performance probes as long as the retained repo is restored cleanly and the durable outcome is recorded here.
  - `python tools/codex_verify.py` remains the retained-code verification gate, while `tools/hotspot_compare.py` and exact-CLI repeat runs provide the same-day performance evidence for keep/reject decisions.
- Escalations: none

### Plan

- [x] Mark `perf-001` active in the queue state and capture the current portfolio-gate shape from the live corpus.
- [x] Build a bounded scratch candidate that broadens the portfolio gate in one plausible way and compare it against the retained solver on a same-day hotspot slice.
- [x] If the hotspot signal is promising, run the broader exact-CLI repeat-aware gate; otherwise keep a retained-noop conclusion and document why the current thresholds remain.
- [x] Run retained-code verification and record the final outcome.

### Verification

- `python - <<'PY' ... corpus scan for current portfolio hits and near-miss all-ternary cases ... PY`
- passed: current retained gate still matches only `large/test_8.cnf`; the nearest dense miss is `special/hard.cnf` at density `4.25`, while low-density near misses are `large/test_1.cnf`, `large/test_7.cnf`, and `large/test_9.cnf`
- `python -m py_compile /tmp/scratch_satsolver_portfolio_minclauses800.py`
- passed
- `python /tmp/scratch_satsolver_portfolio_minclauses800.py small/test_1.cnf /tmp/perf001_sat.txt`
- `python tools/checker.py small/test_1.cnf /tmp/perf001_sat.txt`
- passed
- `python /tmp/scratch_satsolver_portfolio_minclauses800.py special/tseitin.cnf /tmp/perf001_unsat.txt`
- `python tools/checker.py special/tseitin.cnf /tmp/perf001_unsat.txt --bruteforce-var-limit 0`
- passed
- `python tools/hotspot_compare.py --baseline-cli-script satsolver.py --candidate-cli-script /tmp/scratch_satsolver_portfolio_minclauses800.py --repeat 2 large/test_1.cnf large/test_7.cnf large/test_8.cnf large/test_9.cnf`
- passed: candidate regressed the two-order average from `0.4872s` to `0.6538s`, with the newly admitted cases roughly doubling in runtime and `large/test_8.cnf` also slightly worse
- `python tools/codex_verify.py`
- passed: retained solver still compiles, passes 73 tests, and clears both `satsolver.py` and `satsolver_fast.py` smoke checks

### Outcome

- Revalidated the live portfolio gate against today’s corpus and confirmed that the retained thresholds still narrow the portfolio path to exactly one benchmark case: `large/test_8.cnf`.
- Tested one bounded threshold broadening by lowering only the clause-count gate from `1000` to `800`, which admitted `large/test_1.cnf`, `large/test_7.cnf`, and `large/test_9.cnf`.
- Rejected that broadened candidate immediately because the same-day exact-CLI hotspot slice regressed decisively, so the retained solver keeps the current portfolio thresholds unchanged.

### Remaining risks

- This revalidation only ruled out the most plausible low-clause broadening; if future solver-core changes materially alter process-launch or portfolio-worker cost, the threshold space may deserve another focused rescan.

## 2026-03-22 `tool-001-wrapper-verification`

- Status: completed
- Task family: verification tooling
- Branch/worktree: current checkout
- Prompt summary: continue the next deterministic queue task, `tool-001`, by expanding routine verification coverage for the alternate standard-library wrapper path after the shared `satsolver_io.py` extraction
- Assumptions:
  - The smallest useful slice is to make `python tools/codex_verify.py` smoke-test `satsolver_fast.py` in addition to the main submission CLI.
  - `satsolver_pysat.py` should remain outside the default gate because it depends on an optional external environment.
  - This is primarily a tooling-and-wiring task, so `python tools/codex_verify.py` remains the primary verification gate.
- Escalations: none

### Plan

- [x] Mark `tool-001` active in the queue state and inspect the existing verification helper flow.
- [x] Extend `tools/codex_verify.py` to cover the alternate standard-library wrapper smoke path.
- [x] Add regression coverage for the new verification flow and update durable docs if needed.
- [x] Run verification and record the final outcome.

### Verification

- `python -m unittest discover -s tests -p 'test_codex_verify.py' -q`
- passed: 7 tests
- `python tools/codex_verify.py`
- passed: compile, queue check, 73 tests, submission smoke checks, and `satsolver_fast.py` smoke checks all completed successfully

### Outcome

- Expanded `tools/codex_verify.py` so the routine verification gate now smoke-tests `satsolver_fast.py` alongside the main submission CLI.
- Added regression coverage for the alternate-wrapper step generation in `tests/test_codex_verify.py`.
- Updated repo docs and contracts so the default verification scope explicitly includes the standard-library alternate wrapper path.

### Remaining risks

- The default verification gate still excludes `satsolver_pysat.py` because that wrapper depends on an optional external environment.

## 2026-03-22 `sat-001-shared-io-helper`

- Status: completed
- Task family: solver maintainability refactor
- Branch/worktree: current checkout
- Prompt summary: continue the next deterministic queue task, `sat-001`, by deduplicating shared DIMACS parsing and result-writing helpers across `satsolver.py` and `satsolver_fast.py`
- Assumptions:
  - A dedicated standard-library helper module for parsing and output formatting is the smallest reversible slice that removes the duplication without changing solver behavior.
  - `satsolver_blaze.py` can stay untouched because its parser is separate legacy comparison code, while `satsolver_pysat.py` can safely use the same helper to avoid indirect dependence on `satsolver.py`.
  - `python tools/codex_verify.py` remains the right verification gate because this is a behavior-preserving shared-code refactor.
- Escalations: none

### Plan

- [x] Extract shared DIMACS parsing and result-writing helpers into a dedicated module.
- [x] Update `satsolver.py`, `satsolver_fast.py`, and any overlapping wrapper call sites to use the shared helper without changing public APIs.
- [x] Add targeted regression coverage for the shared helper path.
- [x] Run verification and record the final outcome.

### Verification

- `python tools/agent_queue_check.py`
- passed: live `.agent/STATE.yaml` and `.agent/TASK_QUEUE.yaml` remained consistent during the refactor
- `python -m unittest discover -s tests -q`
- passed: 70 tests
- `python tools/codex_verify.py`
- passed: compile, queue check, 70 tests, SAT smoke, and UNSAT smoke all completed successfully

### Outcome

- Added `satsolver_io.py` as the shared DIMACS parsing and result-writing helper for the thin wrapper modules.
- Updated `satsolver.py`, `satsolver_fast.py`, and `satsolver_pysat.py` to use the shared helper without changing their public APIs.
- Added regression coverage in `tests/test_solver_io.py` and refreshed the repo map in `AGENT.md`, `AGENTS.md`, and `README.md`.

### Remaining risks

- `satsolver_blaze.py` still carries its own legacy parser and output path, so future unification work should treat it as a separate comparison-solver task instead of silently folding it into the new helper.

## 2026-03-22 `cp-003-queue-consistency-checker`

- Status: completed
- Task family: autonomous queue control-plane hardening
- Branch/worktree: current checkout
- Prompt summary: continue from the queue control plane and implement the next deterministic task, `cp-003`, by adding a standard-library consistency checker for `.agent/STATE.yaml` and `.agent/TASK_QUEUE.yaml`
- Assumptions:
  - Wiring the new checker into `python tools/codex_verify.py` is the most reliable way to make stale queue state fail fast in routine autonomous verification.
  - A small repo-specific YAML subset parser is acceptable because the control-plane files are intentionally simple and standard-library only.
  - This task should stay in the tooling-and-docs lane, so `python tools/codex_verify.py` remains the primary verification gate.
- Escalations: none

### Plan

- [x] Inspect the current verification helper and define the queue invariants to enforce.
- [x] Implement `tools/agent_queue_check.py` plus focused regression tests.
- [x] Wire the checker into the routine verification flow and update the durable docs if needed.
- [x] Run verification and record the final outcome.

### Verification

- `python tools/agent_queue_check.py`
- passed: live `.agent/STATE.yaml` and `.agent/TASK_QUEUE.yaml` are consistent
- `python -m unittest discover -s tests -q`
- passed: 67 tests
- `python tools/codex_verify.py`
- passed: compile, queue check, 67 tests, SAT smoke, and UNSAT smoke all completed successfully

### Outcome

- Added `tools/agent_queue_check.py`, a standard-library validator for the repo’s YAML control-plane subset plus queue-selection and state/queue consistency checks.
- Added focused regression coverage for the validator and updated `tools/codex_verify.py` so routine verification now fails fast on stale queue state.
- Documented the standalone queue-check command in repo docs and test gates.

### Remaining risks

- The YAML parser is intentionally narrow and repo-specific; if future control-plane files adopt more complex YAML features, the checker will need to expand with them.

## 2026-03-22 `queue-control-plane-bootstrap`

- Status: completed
- Task family: repo-local autonomous queue control plane bootstrap
- Branch/worktree: current checkout
- Prompt summary: create a deterministic repo-local queue system, seed it from repo reality, and complete the first tightly coupled doc-sync task so repeated identical prompts can continue without human task management
- Assumptions:
  - The existing `AGENTS.md` plus `PLANS.md` flow is useful context but not deterministic enough to be the only control plane.
  - `python tools/codex_verify.py` is the right default gate for control-plane and documentation changes in this repo.
  - Syncing legacy docs and agent instructions is tightly coupled with the control-plane bootstrap and can share the same verification.
- Escalations: none

### Plan

- [x] Inspect the repo, current docs, verification tools, and solver layout to infer the real project shape.
- [x] Create `AGENT.md`, `.agent/*`, and `QUEUE_PROMPT.md` with repo-specific queue rules.
- [x] Seed an initial phased task queue and honest repo state snapshot.
- [x] Complete the tightly coupled follow-up task of aligning legacy workflow docs and agent instructions with the new queue model.
- [x] Run verification and record the outcome.

### Verification

- `python tools/codex_verify.py`
- passed: compile, unit tests, SAT smoke, and UNSAT smoke all completed successfully

### Outcome

- Added a deterministic repo-local control plane rooted in `AGENT.md` and `.agent/*`, plus a stable repeated prompt in `QUEUE_PROMPT.md`.
- Synced `AGENTS.md`, `README.md`, and the Codex operator docs so future runs read one queue-driven workflow instead of split guidance.
- Seeded the next concrete task as `cp-003`, a control-plane consistency checker.

### Remaining risks

- Queue consistency is still enforced by process and manual review until `cp-003` adds a machine-checkable validator.

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
