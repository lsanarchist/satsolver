# HANDOFF

## Current State

- The repo now has a queue-driven autonomous control plane rooted in `AGENT.md` and `.agent/*`, plus a machine-checkable queue validator.
- `cp-001`, `cp-002`, `cp-003`, `sat-001`, `tool-001`, `perf-001`, `perf-002`, `perf-003`, `perf-004`, `perf-005`, `perf-006`, `perf-007`, `perf-008`, `perf-009`, `perf-010`, `perf-011`, and `perf-012` are complete.
- The queue has been reopened with a rolling native-only optimization program.
- There is no active in-progress task; the next deterministic task is `perf-013`.

## What Changed This Run

- Kept one same-clause-content conflict-analysis boundary change in `satsolver_core.py`: `analyze()` now uses the learnt-compaction pass itself to finalize best backtrack level and LBD metadata, removing the separate post-minimization `prepare_learnt_clause()` pass.
- The seven-case exact-CLI hotspot slice improved from `30.2756s` to `29.8805s`, the structural fast-exit guardrail stayed slightly positive (`0.0748s -> 0.0725s`), and the repeat-aware exact-CLI 59-case suite improved from `32.2896s` to `31.9532s` with `59/59` correct outputs.
- `tools/profile_solver.py` now mirrors the retained boundary, and the dense hard-case profiler counters stayed unchanged at `72,886` decisions / `59,201` conflicts on `large/test_6.cnf` and `54,245` decisions / `44,619` conflicts on `special/hard.cnf`, so this looks like deleted bookkeeping work rather than heuristic drift.

## Current Focus

- Start `perf-013` next: refresh the dense-UNSAT conflict-analysis profile after the new metadata-boundary keep before choosing another solver-core experiment.

## Recommended Next Tasks

- `perf-013` — refresh dense-UNSAT conflict-analysis profiling after the metadata-boundary keep

## Verification From This Run

- `python tools/codex_verify.py` — passed on the temporary candidate before the performance gate
- `python tools/hotspot_compare.py --baseline-cli-script /tmp/perf012_metadata_baseline/satsolver.py --candidate-cli-script satsolver.py large/test_6.cnf special/hard.cnf large/test_10.cnf medium/test_4.cnf medium/test_3.cnf satlib_more/uuf150-01.cnf large/test_8.cnf` — passed (`30.2756s` baseline versus `29.8805s` candidate)
- `python tools/hotspot_compare.py --baseline-cli-script /tmp/perf012_metadata_baseline/satsolver.py --candidate-cli-script satsolver.py special/pigeonhole.cnf special/tseitin.cnf` — passed (`0.0748s` baseline versus `0.0725s` candidate)
- `python tools/codex_verify.py --benchmark-mode cli --repeat 2` — passed (`59/59` correct, `32.2896s` retained same-day baseline versus `31.9532s` candidate)
- `python tools/profile_solver.py large/test_6.cnf special/hard.cnf` — passed; dense hard-case decisions and conflicts stayed unchanged on both cases
- `python tools/agent_queue_check.py` — passed; queue now resolves to `current_or_next_task='perf-013'`
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
- The retained baseline now totals `31.9532s` representative exact-CLI time over `59` cases, and the seven-case slice still covers about `90.77%` of that total while keeping `large/test_8.cnf` as the SAT-like guardrail.
- `perf-006` showed that the remaining tiny exact-CLI floor is now dominated by Python startup on this machine, so future wrapper/startup work should be skeptical unless a materially different environment or a clearly new surface area appears.
- `perf-007` confirmed that the main remaining native-only gap is the dense search-heavy UNSAT core, not the structural fast-exit families: PySAT cut the seven-case hotspot slice from `24.6944s` to `1.2486s`, while the retained solver still beat it on `special/pigeonhole.cnf` and `special/tseitin.cnf` by about `49x`.
- `perf-008` showed that a true watcher split is not “just layout” in this solver: even though it removed mixed problem-ternary batches and preserved the structural fast-exit families, it perturbed propagation order enough to inflate `large/test_6.cnf` from `59,201` to `81,161` conflicts.
- `perf-009` showed that even the apparently low-yield learnt `10+` minimization removals still matter to search quality: skipping only those scans regressed every heavy dense case and blew up `large/test_8.cnf` into the `5s` range.
- `perf-010` showed that even a same-content ternary-first branch reorder inside `minimize_learnt()` still regressed the seven-case exact-CLI gate overall, so reason-size branch ordering itself is not a promising bookkeeping surface.
- `perf-011` showed that peeling the first two learnt literals out of `prepare_learnt_clause()` also regressed the seven-case exact-CLI gate overall, so future learnt-finalization work should move away from pure loop-shape cleanup.
- `perf-012` kept the first win in this recent conflict-analysis sequence by deleting a whole post-minimization metadata pass while leaving the dense hard-case decision/conflict counters unchanged. The retained repeat-aware exact-CLI baseline is now `31.9532s` over `59` cases.
- The next run should therefore start with `perf-013`, refreshing the dense-UNSAT profile after this keep before choosing another bounded same-search candidate.

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
- Even low-yield long learnt-reason removals can be important search signal, so relaxed minimization selectors should be treated as SAT-guardrail-sensitive rather than as safe bookkeeping cuts.
- Even same-content reason-size branch-order changes inside `minimize_learnt()` can regress the dense exact-CLI gate, so future conflict-analysis bookkeeping should target a different surface than ternary-vs-binary branch ordering.
- Even pure `prepare_learnt_clause()` loop-shape cleanup can regress the dense exact-CLI gate, so future learnt-finalization work should target a different metadata surface instead of another first-literals peel or similar loop rewrite.
- A whole-pass post-minimization metadata deletion can still win cleanly when it preserves learnt contents and dense hard-case search counters, so future boundary work should prefer that style over smaller primitive substitutions or isolated final-pass rewrites.
