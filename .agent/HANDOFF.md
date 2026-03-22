# HANDOFF

## Current State

- The repo still uses the queue-driven autonomous control plane rooted in `AGENT.md` and `.agent/*`, plus the machine-checkable queue validator.
- `cp-001`, `cp-002`, `cp-003`, `sat-001`, `tool-001`, `perf-001`, `perf-002`, `perf-003`, `perf-004`, `perf-005`, `perf-006`, `perf-007`, `perf-008`, `perf-009`, `perf-010`, `perf-011`, `perf-012`, `perf-013`, `perf-014`, `perf-015`, `perf-016`, `perf-017`, `perf-018`, and `perf-019` are complete.
- There is no active in-progress task; the next deterministic task is `perf-020`.

## What Changed This Run

- Closed `perf-019` as a retained no-op after testing one bounded learnt-large relocation bookkeeping deletion and reverting it.
- The candidate improved the focused seven-case exact-CLI hotspot (`26.4626s -> 25.8086s`) and the structural fast-exit guardrail (`0.0657s -> 0.0564s`), and it preserved the dense hard-case search counters.
- The stronger repeat-aware 59-case exact-CLI suite still regressed (`28.8865s -> 29.3380s`), so no solver code was kept.
- The queue now advances to `perf-020`, which should refresh the broader exact-CLI guard slice for future learnt-large relocation work before another solver-core change.

## Current Focus

- Start `perf-020` next: refresh the broader exact-CLI guard cases that future learnt-large relocation experiments must satisfy.

## Recommended Next Tasks

- `perf-020` — refresh learnt-large exact-CLI guard slices after the broad-suite reject

## Verification From This Run

- `python tools/codex_verify.py` — passed on the temporary candidate before the performance gates
- `python tools/hotspot_compare.py --baseline-cli-script /tmp/perf019_largebook_baseline.9uppKV/satsolver.py --candidate-cli-script satsolver.py large/test_6.cnf special/hard.cnf large/test_10.cnf medium/test_4.cnf medium/test_3.cnf satlib_more/uuf150-01.cnf large/test_8.cnf` — passed; focused seven-case gate improved (`26.4626s -> 25.8086s`)
- `python tools/hotspot_compare.py --baseline-cli-script /tmp/perf019_largebook_baseline.9uppKV/satsolver.py --candidate-cli-script satsolver.py special/pigeonhole.cnf special/tseitin.cnf` — passed; structural guardrail improved (`0.0657s -> 0.0564s`)
- `python tools/profile_solver.py large/test_6.cnf special/hard.cnf` — passed; dense hard-case decisions/conflicts stayed unchanged
- `python benchmark_suite.py satsolver /tmp/perf019_baseline_cli_repeat2.txt small medium large special satlib_subset satlib_more --bruteforce-var-limit 16 --cli-script /tmp/perf019_largebook_baseline.9uppKV/satsolver.py --python-executable /usr/bin/python --repeat 2` — passed; frozen baseline `59/59` correct at `28.8865s` representative / `57.7730s` measured
- `python tools/codex_verify.py --benchmark-mode cli --repeat 2` — passed as a correctness run but rejected as a keep gate; candidate `59/59` correct at `29.3380s` representative / `58.6760s` measured
- `python tools/agent_queue_check.py` — passed; queue now resolves to `current_or_next_task='perf-020'`
- `python tools/codex_verify.py` — passed again after the candidate revert and control-plane sync
- `git diff --check` — passed

## Notes For The Next Run

- Start with the read order in `.agent/RUNBOOK.md`.
- Reconcile `STATE.yaml` against the repo tree before selecting a task.
- Keep `PLANS.md` updated for any multi-step or code-bearing task.
- Reuse the queue checker when adjusting `.agent/STATE.yaml` or `.agent/TASK_QUEUE.yaml`.
- The default verifier covers `satsolver_fast.py`, but `satsolver_pysat.py` remains outside the default gate because it requires an optional external environment.
- External libraries or solvers may be used as short-lived research references only; do not retain them in the submission path or make them a default verifier dependency.
- Do not update `benchmark_summary.md` or `experiments.jsonl` for `perf-019`; no performance keep survived this run.
- The `perf-019` reject means future learnt-large relocation work should not trust the focused seven-case slice alone, even when the dense hard-case counters stay unchanged.
- `perf-020` should use the broad repeat-aware exact-CLI evidence to name the extra guard cases or slices that future learnt-large relocation experiments must carry before another solver-core edit.

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
- On the current machine, Python interpreter startup is the dominant floor on tiny exact-CLI runs, so most remaining wrapper-path deltas are likely to be small and noisy.
- The current solver still owns the structural fast-exit families (`special/pigeonhole.cnf`, `special/tseitin.cnf`) even though optional external references are dramatically faster on the dense search-heavy UNSAT hotspot slice.
- Changing the watched-clause family order can materially change the dense UNSAT search path, so future watcher-layout experiments should assume they are heuristic changes, not neutral refactors.
- Even low-yield long learnt-reason removals can be important search signal, so relaxed minimization selectors should be treated as SAT-guardrail-sensitive rather than safe bookkeeping cuts.
- Learnt-large relocation work now needs a broader exact-CLI guard slice than the focused seven-case hotspot before a solver-core keep is safe.
