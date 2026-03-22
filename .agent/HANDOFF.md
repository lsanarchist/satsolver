# HANDOFF

## Current State

- The repo now has a queue-driven autonomous control plane rooted in `AGENT.md` and `.agent/*`, plus a machine-checkable queue validator.
- `cp-001`, `cp-002`, `cp-003`, `sat-001`, `tool-001`, `perf-001`, `perf-002`, `perf-003`, `perf-004`, `perf-005`, and `perf-006` are complete.
- The queue has been reopened with a rolling native-only optimization program.
- There is no active in-progress task; the next deterministic task is `perf-007`.

## What Changed This Run

- Re-read the wrapper/startup keep/reject history and measured the current exact-CLI startup floor directly instead of forcing another low-confidence wrapper patch.
- Confirmed that on this machine `python -c pass` is already about `27.5ms`, `python -c 'import satsolver'` about `31.2ms`, and the full `small/test_1.cnf` CLI path about `36.0ms`.
- Recorded `perf-006` as a retained-noop conclusion because the remaining repo-local wrapper cost is only a few milliseconds on the tiny exact-CLI cases and the obvious surface-trim lanes are already exhausted.

## Current Focus

- Start `perf-007` next: use optional external solver references to derive the next native-only gap targets.

## Recommended Next Tasks

- `perf-007` — use optional external solver references only after the native-only heuristic lanes have been revisited

## Verification From This Run

- `python - <<'PY' ... repeated tiny exact-CLI timings for small/test_1.cnf, special/tseitin.cnf, and large/test_8.cnf ... PY` — passed (`0.0532s`, `0.0382s`, `0.4148s` means)
- `python -X importtime -c 'import satsolver' 2>&1 | tail -n 40` — passed (`satsolver_core` about `3.4ms` cumulative, `satsolver_io` about `0.2ms`, `satsolver` about `4.0ms`)
- `python - <<'PY' ... repeated subprocess timings for python -c pass, python -c 'import satsolver', and python satsolver.py small/test_1.cnf /tmp/_probe.txt ... PY` — passed (`27.5ms`, `31.2ms`, `36.0ms` means)
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
- The top two cases alone, `large/test_6.cnf` and `special/hard.cnf`, still account for `72.95%` of the exact-CLI total, but the next deterministic task is now `perf-007`, so the next run should use external references only to sharpen the next native-only target rather than keep shaving the already-thin wrapper path.

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
