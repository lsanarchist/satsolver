# HANDOFF

## Current State

- The repo now has a queue-driven autonomous control plane rooted in `AGENT.md` and `.agent/*`, plus a machine-checkable queue validator.
- `cp-001`, `cp-002`, `cp-003`, `sat-001`, `tool-001`, `perf-001`, `perf-002`, `perf-003`, `perf-004`, `perf-005`, `perf-006`, `perf-007`, and `perf-008` are complete.
- The queue has been reopened with a rolling native-only optimization program.
- There is no active in-progress task; the next deterministic task is `perf-009`.

## What Changed This Run

- Tested one true watch-family split by moving problem ternary clauses onto their own watcher lists, mirrored that change in the profiler, and added a routing regression while the candidate was under test.
- Rejected the candidate after the seven-case exact-CLI hotspot gate regressed from `24.6075s` to `28.1011s`, even though the structural fast-exit slice stayed healthy and the SAT guardrail `large/test_8.cnf` improved slightly.
- The decisive failure was search-path drift on `large/test_6.cnf`: the profiler showed the split removed mixed problem-ternary batches as intended, but it also raised that case from `59,201` to `81,161` conflicts, so no solver code was retained and the queue now advances to `perf-009`.

## Current Focus

- Start `perf-009` next: revisit dense-UNSAT conflict-analysis with the refreshed reason counters now that the watch-family lane has been rejected.

## Recommended Next Tasks

- `perf-009` — revisit dense-UNSAT conflict-analysis after the watch-family reject

## Verification From This Run

- `python tools/codex_verify.py` — passed on the temporary candidate before the performance gate
- `python tools/hotspot_compare.py --baseline-cli-script /tmp/perf008_watchsplit_baseline/satsolver.py --candidate-cli-script satsolver.py large/test_6.cnf special/hard.cnf large/test_10.cnf medium/test_4.cnf medium/test_3.cnf satlib_more/uuf150-01.cnf large/test_8.cnf` — candidate rejected (`24.6075s` baseline versus `28.1011s` candidate)
- `python tools/hotspot_compare.py --baseline-cli-script /tmp/perf008_watchsplit_baseline/satsolver.py --candidate-cli-script satsolver.py special/pigeonhole.cnf special/tseitin.cnf` — passed (`0.0757s` baseline versus `0.0604s` candidate)
- `python tools/profile_solver.py large/test_6.cnf special/hard.cnf` — passed
- `python tools/agent_queue_check.py` — passed
- `python tools/codex_verify.py` — passed
- `git diff --check` — passed

## Notes For The Next Run

- Start with the read order in `.agent/RUNBOOK.md`.
- Reconcile `STATE.yaml` against the repo tree before selecting a task.
- Keep `PLANS.md` updated for any multi-step or code-bearing task.
- Reuse the queue checker when adjusting `.agent/STATE.yaml` or `.agent/TASK_QUEUE.yaml`.
- The default verifier covers `satsolver_fast.py`, but `satsolver_pysat.py` remains outside the default gate because it requires an optional external environment.
- External libraries or solvers may be used as short-lived research references only; do not retain them in the submission path or make them a default verifier dependency.
- After each performance experiment, either split the next evidence-backed task into `.agent/TASK_QUEUE.yaml` or record a retained-noop conclusion; do not collapse the queue back into one endless vague task.
- The refreshed baseline totaled `32.2896s` representative exact-CLI time over `59` cases, and the seven-case slice still covers `90.82%` of that total while keeping `large/test_8.cnf` as the SAT-like guardrail.
- `perf-006` showed that the remaining tiny exact-CLI floor is now dominated by Python startup on this machine, so future wrapper/startup work should be skeptical unless a materially different environment or a clearly new surface area appears.
- `perf-007` confirmed that the main remaining native-only gap is the dense search-heavy UNSAT core, not the structural fast-exit families: PySAT cut the seven-case hotspot slice from `24.6944s` to `1.2486s`, while the retained solver still beat it on `special/pigeonhole.cnf` and `special/tseitin.cnf` by about `49x`.
- `perf-008` showed that a true watcher split is not “just layout” in this solver: even though it removed mixed problem-ternary batches and preserved the structural fast-exit families, it perturbed propagation order enough to inflate `large/test_6.cnf` from `59,201` to `81,161` conflicts.
- The next run should therefore leave the watch-family lane alone for now and move to the already-queued dense conflict-analysis slice in `perf-009`.

## Immediate Constraints

- Keep the submission path standard-library only.
- Preserve `python satsolver.py input.cnf output.txt`.
- Do not update `benchmark_summary.md` or `experiments.jsonl` unless a performance result is kept.
- External comparison tooling is allowed only for research and must not become a retained submission dependency.

## Repo Truths To Preserve

- `satsolver_core.py` is the shared CDCL implementation.
- `satsolver_io.py` is the shared DIMACS parsing and result-writing helper for thin wrappers.
- `tools/checker.py` is the correctness oracle for solver output format.
- `tools/agent_queue_check.py` is the control-plane consistency oracle.
- `tools/codex_verify.py` is expected to cover both `satsolver.py` and `satsolver_fast.py` smoke paths by default.
- The retained portfolio thresholds still intentionally gate only `large/test_8.cnf` until a same-day broader threshold change wins cleanly.
- Same-day exact-CLI evidence is stronger than stale benchmark history when timing signals are close.
- External solvers or libraries may inform research, but only native-only wins belong in the retained solver path.
- `large/test_8.cnf` is an important SAT-like guardrail for learnt-database experiments because extra retained clause load can destabilize it dramatically.
- `large/test_8.cnf` is also an important guardrail for restart-policy experiments because even conservative restart drift can destabilize it badly.
- On the current machine, Python interpreter startup is now the dominant floor on tiny exact-CLI runs, so most remaining wrapper-path deltas are likely to be small and noisy.
- The current solver still owns the structural fast-exit families (`special/pigeonhole.cnf`, `special/tseitin.cnf`) even though the optional PySAT reference is dramatically faster on the dense search-heavy UNSAT hotspot slice.
- Changing the watched-clause family order can materially change the dense UNSAT search path, so future watcher-layout experiments should assume they are heuristic changes, not neutral refactors.
