# AGENTS.md

## Scope

This repository is a benchmark-driven, standard-library Python SAT solver. The default autonomous task family is SAT solver maintenance: correctness fixes, tooling improvements, benchmark-driven performance experiments, and durable docs/report updates around those changes. Long-running optimization work should be expressed as a rolling queue of bounded experiments rather than as one open-ended mega-task.

## Read First

1. `AGENT.md`
2. `.agent/STATE.yaml`
3. `.agent/TASK_QUEUE.yaml`
4. `.agent/HANDOFF.md`
5. `.agent/RUNBOOK.md`
6. `README.md`
7. `PLANS.md`
8. `skills/autonomous-sat-maintenance/SKILL.md`
9. `benchmark_summary.md` when the task is performance-sensitive
10. `experiments.jsonl` when prior keep/reject context matters

## Repo Layout

- `satsolver.py`: required submission CLI entrypoint
- `satsolver_core.py`: shared CDCL core
- `satsolver_io.py`: shared DIMACS parsing and result-writing helpers
- `satsolver_fast.py`: alternate wrapper used for comparisons
- `satsolver_blaze.py`: legacy comparison solver
- `satsolver_pysat.py`: optional external-library comparison solver
- `benchmark_suite.py`: validated benchmark harness
- `tools/checker.py`: SAT-format validator and small-UNSAT brute-force checker
- `tools/profile_solver.py`: profiler for hotspot cases
- `tools/hotspot_compare.py`: same-day baseline-vs-candidate comparator
- `tools/codex_verify.py`: repo-standard verification helper for queued Codex tasks
- `tests/`: regression and tooling tests
- `small/`, `medium/`, `large/`, `special/`, `satlib_subset/`, `satlib_more/`: benchmark datasets

## Default Workflow

1. Treat `.agent/TASK_QUEUE.yaml` as the source of truth for task selection.
2. If `.agent/STATE.yaml.current_task_id` points to an `in_progress` task, continue it first; otherwise pick the next eligible `todo` task deterministically.
3. Add or update the active task section at the top of `PLANS.md` before non-trivial editing.
4. For queued or minimally supervised SAT-maintenance work, open `skills/autonomous-sat-maintenance/SKILL.md` and follow its lane selection and validation rules.
5. Keep the change small, reviewable, and reversible.
6. Run `python tools/codex_verify.py` after meaningful edits.
7. If the task can change solver behavior or performance, also run a same-day comparison path:
   - focused A/B: `python tools/hotspot_compare.py ...`
   - broader validation: `python tools/codex_verify.py --benchmark-mode cli --repeat 2`
8. After a performance experiment, either queue the next evidence-backed slice or record a retained-noop conclusion instead of leaving an endless vague task behind.
9. Update `.agent/STATE.yaml`, `.agent/TASK_QUEUE.yaml`, `.agent/HANDOFF.md`, and `.agent/WORKLOG.md` before finishing.
10. Leave durable guidance in repo files, not only in the final chat message.

## Commands

- Quick verification: `python tools/codex_verify.py`
- Exact-CLI benchmark verification: `python tools/codex_verify.py --benchmark-mode cli --repeat 2`
- Full module benchmark: `python benchmark_suite.py satsolver /tmp/bench.txt small medium large special satlib_subset satlib_more --bruteforce-var-limit 16`
- Full exact-CLI benchmark: `python benchmark_suite.py satsolver /tmp/bench_cli.txt small medium large special satlib_subset satlib_more --bruteforce-var-limit 16 --cli-script satsolver.py`
- Hotspot comparison: `python tools/hotspot_compare.py --baseline-cli-script <baseline>/satsolver.py --candidate-cli-script satsolver.py large/test_6.cnf special/hard.cnf medium/test_4.cnf large/test_10.cnf large/test_8.cnf`

## Conventions

- Keep the submission path standard-library only.
- Preserve the required CLI contract: `python satsolver.py input.cnf output.txt`.
- External solvers or libraries may be used only as research references; never retain them in the submission path or make them a default verification dependency.
- Prefer shared solver changes in `satsolver_core.py`; keep wrappers thin unless the task is explicitly wrapper/startup related.
- Treat `tools/checker.py` as the correctness oracle for solver output format.
- Treat `AGENT.md` plus `.agent/*` as the authoritative autonomous control plane.
- Treat `python tools/codex_verify.py` as covering both the main submission CLI and the standard-library alternate wrapper smoke path.
- Treat same-day exact-CLI evidence as stronger than stale historical artifacts when the timing signal is small.
- Update `benchmark_summary.md` and `experiments.jsonl` only when a performance result is kept or when the task explicitly asks for durable reporting.
- Keep benchmark artifacts and scratch outputs out of the repo unless the task explicitly wants a retained artifact.

## Safety Limits

- Use a dedicated worktree and branch when the task is more than a trivial doc fix.
- Preferred pattern: `git worktree add ../satsolver-<slug> -b codex/<slug> HEAD`
- Resolve routine ambiguity autonomously.
- Escalate only for destructive repo actions, missing credentials or secrets, approval-gated network access, or product decisions with multiple valid directions.
- Do not delete datasets, benchmark history, or comparison files unless the task explicitly calls for cleanup.
- Do not add external dependencies to the submission path. Optional comparison tooling may use a separate environment only if the task explicitly allows it.

## Definition Of Done

A queued autonomous task is done when:

- `.agent/STATE.yaml`, `.agent/TASK_QUEUE.yaml`, `.agent/HANDOFF.md`, and `.agent/WORKLOG.md` match repo reality.
- `PLANS.md` reflects the final plan, assumptions, verification, and outcome.
- The code, docs, and tests needed for the task are updated.
- `python tools/codex_verify.py` passes.
- Performance-sensitive tasks run the appropriate hotspot and or benchmark verification.
- The final handoff names files changed, checks run, remaining risks, and the next sensible follow-up.
