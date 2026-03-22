# HANDOFF

## Current State

- The repo still uses the queue-driven autonomous control plane rooted in `AGENT.md` and `.agent/*`, plus the machine-checkable queue validator.
- `cp-001`, `cp-002`, `cp-003`, `sat-001`, `tool-001`, `perf-001`, `perf-002`, `perf-003`, `perf-004`, `perf-005`, `perf-006`, `perf-007`, `perf-008`, `perf-009`, `perf-010`, `perf-011`, `perf-012`, `perf-013`, `perf-014`, `perf-015`, `perf-016`, `perf-017`, `perf-018`, `perf-019`, `perf-020`, `perf-021`, `perf-022`, `perf-023`, and `perf-024` are complete.
- There is no active in-progress task; the next deterministic task is `perf-025`.

## What Changed This Run

- Closed `perf-024` as a retained no-op after testing one narrower learnt-large successful-probe bookkeeping candidate and reverting it.
- The candidate used the direct watched-slot rewrite only on learnt clauses that satisfied the true long-and-deep overlap: `len10+` and step-3+ successful probes.
- That narrower rule was still not a win. It slightly regressed the primary focused seven-case gate overall (`26.2060s -> 26.2748s`) and also regressed the supplemental `satlib_more` slice (`0.3201s -> 0.3316s`), with `satlib_more/uuf125-010.cnf` worse in both orders.
- The durable lesson is that the overlap lane itself is not where the earlier `perf-023` supplemental gains came from. The next sensible step is to profile the remaining non-overlap success buckets so the following solver-core candidate targets the actual surviving sublane instead of guessing between long-but-shallow and short-but-deep work.
- The queue now advances to `perf-025`, a measurement-only non-overlap profiling task.

## Current Focus

- Start `perf-025` next: profile the remaining non-overlap learnt-large success buckets before another solver-core edit.

## Recommended Next Tasks

- `perf-025` — profile the non-overlap learnt-large success buckets after the overlap reject

## Verification From This Run

- `python tools/codex_verify.py` — passed on the temporary candidate before the performance gates
- `python tools/hotspot_compare.py --baseline-cli-script /tmp/perf024_longdeep_baseline.vA1sej/satsolver.py --candidate-cli-script satsolver.py large/test_6.cnf special/hard.cnf large/test_10.cnf medium/test_4.cnf medium/test_3.cnf satlib_more/uuf150-01.cnf large/test_8.cnf` — candidate rejected on the primary early gate (`26.2060s -> 26.2748s`)
- `python tools/hotspot_compare.py --baseline-cli-script /tmp/perf024_longdeep_baseline.vA1sej/satsolver.py --candidate-cli-script satsolver.py satlib_more/uuf125-010.cnf satlib_more/uf125-01.cnf satlib_more/uf125-010.cnf satlib_more/jnh10.cnf satlib_more/jnh1.cnf` — candidate rejected on the supplemental slice too (`0.3201s -> 0.3316s`)
- `python tools/agent_queue_check.py` — passed after the final control-plane sync; queue now resolves to `current_or_next_task='perf-025'`
- `python tools/codex_verify.py` — passed after the final control-plane sync
- `git diff --check` — passed

## Notes For The Next Run

- Start with the read order in `.agent/RUNBOOK.md`.
- Reconcile `STATE.yaml` against the repo tree before selecting a task.
- Keep `PLANS.md` updated for any multi-step or code-bearing task.
- Reuse the queue checker when adjusting `.agent/STATE.yaml` or `.agent/TASK_QUEUE.yaml`.
- The default verifier covers `satsolver_fast.py`, but `satsolver_pysat.py` remains outside the default gate because it requires an optional external environment.
- External libraries or solvers may be used as short-lived research references only; do not retain them in the submission path or make them a default verifier dependency.
- Do not update `benchmark_summary.md` or `experiments.jsonl` for `perf-024`; no performance keep survived this run.
- `perf-024` showed that the overlap lane itself is not a winner: even the narrowed `len10+` and step-3+ rewrite lost both the primary focused gate and the supplemental slice.
- `perf-025` should therefore be a profiling run, not another immediate solver edit. The next run should determine whether the surviving potential from `perf-023` came from long-but-shallow or short-but-deep learnt-large successes.
- Keep `jnh10` and `jnh1` in the supplemental slice as problem-large guardrails; do not let the next learnt-large task drift back into a mixed-family rewrite.

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
