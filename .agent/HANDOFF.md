# HANDOFF

## Current State

- The repo still uses the queue-driven autonomous control plane rooted in `AGENT.md` and `.agent/*`, plus the machine-checkable queue validator.
- `cp-001`, `cp-002`, `cp-003`, `sat-001`, `tool-001`, `perf-001`, `perf-002`, `perf-003`, `perf-004`, `perf-005`, `perf-006`, `perf-007`, `perf-008`, `perf-009`, `perf-010`, `perf-011`, `perf-012`, `perf-013`, `perf-014`, `perf-015`, `perf-016`, `perf-017`, `perf-018`, `perf-019`, `perf-020`, `perf-021`, `perf-022`, `perf-023`, `perf-024`, `perf-025`, `perf-026`, `perf-027`, `perf-028`, `perf-029`, `perf-030`, `perf-031`, `perf-032`, `perf-033`, `perf-034`, `perf-035`, `perf-036`, `perf-037`, `perf-038`, `perf-039`, `perf-040`, `perf-041`, and `perf-042` are complete.
- There is no active in-progress task; the next deterministic task is `perf-043`.

## What Changed This Run

- Closed `perf-042` as a retained no-op with no solver change.
- Tested one bounded solver-core candidate that applied the earlier pop-first source-pop rewrite only to exact `sub10 step-3` learnt-large non-last deep-overwrite removals at source index `5+`, then reverted it after all three early gates stayed negative.
- The dense anchor pair stayed slightly negative on the two-order average (`22.4346s -> 22.5260s`), the focused seven-case gate rejected the candidate more clearly (`26.5830s -> 27.5761s`), and the supplemental `satlib_more` slice rejected it too (`0.3316s -> 0.3512s`).
- The clearest recurring damage landed on `large/test_6.cnf`, `special/hard.cnf`, `medium/test_4.cnf`, `satlib_more/uuf150-01.cnf`, and reverse-order `satlib_more/uf125-010.cnf`, so the exact `index 5+` aggregate is still too broad.

## Current Focus

- Start `perf-043` next: stay measurement-only and split the exact `sub10 step-3` deep-overwrite `index 5+` lane into exact source index `5` versus `index 6+`, while keeping the retained solver path unchanged.

## Recommended Next Tasks

- `perf-043` — profile the exact index-5-plus deep overwrite tail after the perf-042 reject

## Verification From This Run

- `python tools/codex_verify.py` — passed on the temporary candidate (`80/80` tests green plus compile/checker/wrapper smoke checks)
- `python tools/hotspot_compare.py --baseline-cli-script /tmp/perf042_index5plus_baseline.1gYnb9/satsolver.py --candidate-cli-script satsolver.py large/test_6.cnf special/hard.cnf` — slightly negative on the dense anchor pair (`22.4346s -> 22.5260s`)
- `python tools/hotspot_compare.py --baseline-cli-script /tmp/perf042_index5plus_baseline.1gYnb9/satsolver.py --candidate-cli-script satsolver.py large/test_6.cnf special/hard.cnf large/test_10.cnf medium/test_4.cnf medium/test_3.cnf satlib_more/uuf150-01.cnf large/test_8.cnf` — candidate rejected on the focused seven-case gate (`26.5830s -> 27.5761s`)
- `python tools/hotspot_compare.py --baseline-cli-script /tmp/perf042_index5plus_baseline.1gYnb9/satsolver.py --candidate-cli-script satsolver.py satlib_more/uuf125-010.cnf satlib_more/uf125-01.cnf satlib_more/uf125-010.cnf satlib_more/jnh10.cnf satlib_more/jnh1.cnf` — candidate rejected on the supplemental slice too (`0.3316s -> 0.3512s`)
- `python tools/agent_queue_check.py` — passed after the final control-plane sync; queue now resolves to `current_or_next_task='perf-043'`
- `python tools/codex_verify.py` — passed after the final control-plane sync
- `git diff --check` — passed after the final control-plane sync

## Notes For The Next Run

- Start with the read order in `.agent/RUNBOOK.md`.
- Reconcile `STATE.yaml` against the repo tree before selecting a task.
- Keep `PLANS.md` updated for any multi-step or code-bearing task.
- Reuse the queue checker when adjusting `.agent/STATE.yaml` or `.agent/TASK_QUEUE.yaml`.
- The default verifier covers `satsolver_fast.py`, but `satsolver_pysat.py` remains outside the default gate because it requires an optional external environment.
- External libraries or solvers may be used as short-lived research references only; do not retain them in the submission path or make them a default verifier dependency.
- Do not update `benchmark_summary.md` or `experiments.jsonl` for `perf-042`; this run kept no solver change.
- `perf-030` rules out the direct watched-slot rewrite across the whole exact `sub10 step-3` aggregate, `perf-032` rules out a source-list self-assignment skip as a retained dense-anchor keep, `perf-034` rules out the matching pop-first rewrite on the whole non-last overwrite lane, `perf-035` says that the remaining overwrite traffic is mostly in deeper `index 2+` slots, `perf-036` says that the whole deeper aggregate is still too broad, `perf-037` narrows the real surviving lane to exact source index `3+`, `perf-038` says even that aggregate is still too broad, `perf-039` narrows the real surviving tail to exact `index 4+`, `perf-040` says even that aggregate is still too broad for a retained keep, `perf-041` narrows the surviving tail again to exact source index `5+`, and `perf-042` says even that aggregate is still too broad.
- The overlap lane is still ruled out by `perf-024`, the broader short-but-deep aggregate is ruled out by `perf-026`, the exact `step-3/4` aggregate is ruled out for the direct rewrite by `perf-028`, and the exact `step-3` aggregate is ruled out for that same rewrite by `perf-030`.
- Keep `special/hard.cnf` and `large/test_6.cnf` as the dense exact-step anchor pair, and keep the supplemental `satlib_more` slice (`uuf125-010`, `uf125-01`, `uf125-010`, `jnh10`, `jnh1`) in view because the target trio still shows real deep-overwrite traffic while `jnh10` and `jnh1` remain mostly guardrails.
- `perf-043` should stay measurement-only and split the exact `sub10 step-3` deep-overwrite `index 5+` lane into exact source index `5` versus `index 6+` before another solver-core edit; do not widen the solver change again until that narrower split is measured.

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
- `large/test_8.cnf` remains an important SAT-like guardrail for learnt-database and restart-sensitive changes.
- On the current machine, repeat-aware exact-CLI totals are still noisy enough that case ordering is usually more stable than one raw rerun total.
- The current solver still owns the structural fast-exit families (`special/pigeonhole.cnf`, `special/tseitin.cnf`) even though optional external references are dramatically faster on the dense search-heavy UNSAT hotspot slice.
- Changing the watched-clause family order can materially change the dense UNSAT search path, so future watcher-layout experiments should assume they are heuristic changes, not neutral refactors.
- Even low-yield long learnt-reason removals can be important search signal, so relaxed minimization selectors should be treated as SAT-guardrail-sensitive rather than safe bookkeeping cuts.
- Future learnt-large relocation work should use the focused seven-case slice plus the supplemental `satlib_more` slice (`uuf125-010`, `jnh10`, `uf125-01`, `uf125-010`, `jnh1`) before the full repeat-aware exact-CLI keep gate.
