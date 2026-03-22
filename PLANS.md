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

## 2026-03-22 `perf-007-external-gap-targets`

- Status: completed
- Task family: external-reference performance gap analysis
- Branch/worktree: current checkout
- Prompt summary: continue the next deterministic queue task, `perf-007`, by using optional external solver references to sharpen the next native-only optimization target without retaining any non-standard-library dependency
- Assumptions:
  - The repo already has one suitable short-lived external reference path in `satsolver_pysat.py` backed by `.venv-external-sat`, so the highest-signal comparison is to remeasure that path on the refreshed hotspot slice instead of inventing a new adapter.
  - The current seven-case exact-CLI hotspot slice remains the right first gate for dense search-heavy gap analysis, but one or two structural-presolver cases should also be checked so the next native-only task does not blindly chase an area where the current solver already has unique strengths.
  - This task is primarily research and queue refinement, so a retained-noop on solver code is acceptable as long as the next native-only task is narrowed from same-day evidence.
- Escalations: none

### Plan

- [x] Revalidate the optional PySAT comparison path on small SAT and UNSAT smoke cases in the external environment.
- [x] Run a same-day external-reference comparison on the refreshed hotspot slice and targeted structural-presolver cases.
- [x] Translate the observed gap into one concrete next native-only task, then update the control plane and verification log.

### Verification

- `.venv-external-sat/bin/python satsolver_pysat.py small/test_1.cnf /tmp/perf007_pysat_small_sat.txt && python tools/checker.py small/test_1.cnf /tmp/perf007_pysat_small_sat.txt`
- passed: the optional external wrapper still produced a valid SAT model on the shared DIMACS/output path
- `.venv-external-sat/bin/python satsolver_pysat.py special/tseitin.cnf /tmp/perf007_pysat_small_unsat.txt && python tools/checker.py special/tseitin.cnf /tmp/perf007_pysat_small_unsat.txt --bruteforce-var-limit 0`
- passed: the external wrapper still produced a valid UNSAT result in the external environment
- `python - <<'PY' ... backend sweep across minisat22, glucose4, cadical195, mergesat3, kissat404 on large/test_6.cnf and special/hard.cnf ... PY`
- passed: `minisat22` remained the strongest local PySAT backend on the two heaviest dense UNSAT cases (`0.5813s` total versus `1.0239s` for `glucose4`, `1.1116s` for `kissat404`, `1.1983s` for `cadical195`, and `2.4508s` for `mergesat3`)
- `SATSOLVER_PYSAT_BACKEND=minisat22 python tools/hotspot_compare.py --baseline-cli-script satsolver.py --candidate-cli-script satsolver_pysat.py --candidate-python-executable .venv-external-sat/bin/python large/test_6.cnf special/hard.cnf large/test_10.cnf medium/test_4.cnf medium/test_3.cnf satlib_more/uuf150-01.cnf large/test_8.cnf`
- passed: the refreshed seven-case exact-CLI comparison stayed fully checker-valid and showed a huge dense-UNSAT ceiling gap, with the retained solver at `24.6944s` versus PySAT at `1.2486s` on the two-order average; the current solver only kept the SAT guardrail edge on `large/test_8.cnf` (about `0.2841s` versus `0.3218s`)
- `SATSOLVER_PYSAT_BACKEND=minisat22 python tools/hotspot_compare.py --baseline-cli-script satsolver.py --candidate-cli-script satsolver_pysat.py --candidate-python-executable .venv-external-sat/bin/python special/pigeonhole.cnf special/tseitin.cnf`
- passed: the structural fast-exit slice confirmed the opposite side of the story, with the retained solver at `0.0702s` versus PySAT at `3.4322s` on the two-order average
- `python tools/profile_solver.py large/test_6.cnf special/hard.cnf`
- passed: dense UNSAT profiling still shows massive mixed watch-family traffic on the hard cases, including `problem_ternary_mixed_batch_share=0.6193` on `large/test_6.cnf` and `0.7078` on `special/hard.cnf`, plus millions of problem-ternary visits and high learnt-large coexistence inside those batches
- `python tools/agent_queue_check.py`
- passed: final queue edits resolve cleanly to `current_or_next_task='perf-008'`
- `python tools/codex_verify.py`
- passed: the retained native-only solver plus control-plane updates still compile, pass the queue check, pass all 73 tests, and clear both default wrapper smoke paths
- `git diff --check`
- passed

### Outcome

- Revalidated the optional PySAT comparison path and confirmed that `minisat22` is still the strongest local external backend worth using as a speed ceiling in this repo.
- Fresh same-day exact-CLI evidence shows that the retained native-only solver still trails a mature external backend badly on dense search-heavy UNSAT families: the refreshed seven-case slice fell from `24.6944s` to `1.2486s` under PySAT, with the biggest gaps on `large/test_6.cnf` (`11.9414s` average versus `0.3395s`) and `special/hard.cnf` (`8.0909s` versus `0.2627s`).
- The same evidence also reconfirmed that the current repo-specific structural presolvers are real strengths, not dead weight: the retained solver crushed PySAT on `special/pigeonhole.cnf` and `special/tseitin.cnf` (`0.0702s` versus `3.4322s` two-order average).
- Combined with the refreshed profiler counters, that points the next native-only task away from more wrapper work or structural fast-exit changes and toward the dense UNSAT CDCL core, specifically the mixed watch-family traversal where problem ternary traffic and learnt-large watchers are still heavily interleaved.
- Completed `perf-007` as a research-only queue-refinement task with no retained solver-code change, and added `perf-008` as the next concrete native-only experiment: test a true watch-family split on the dense UNSAT hotspot slice while preserving the SAT guardrail and structural fast-exit families.

### Remaining risks

- PySAT is only a ceiling reference, not a search-trace oracle, so the next native-only task still needs to validate its candidate directly on the repo's exact-CLI slices instead of cargo-culting external-solver behavior.
- The profiler strongly suggests a watch-family split lane, but previous lighter-weight propagation micro-optimizations have often lost on `large/test_8.cnf`, so the new structural and SAT guardrail slices must remain part of the next experiment's gate.

## 2026-03-22 `perf-006-wrapper-startup-overhead`

- Status: completed
- Task family: native-only wrapper and startup measurement
- Branch/worktree: current checkout
- Prompt summary: continue the next deterministic queue task, `perf-006`, by measuring remaining wrapper and startup overhead on the refreshed exact-CLI path and keeping only a clearly justified native-only win
- Assumptions:
  - The remaining exact-CLI wrapper lane is narrow because the repo has already kept CLI-mode import gating, runtime-`typing` cleanup, and targeted CLI-local aliasing while rejecting many broader wrapper-surface trims.
  - A retained-noop conclusion is acceptable if fresh measurement shows the remaining repo-local wrapper cost is too small or too exhausted to justify another low-confidence patch.
  - The startup-sensitive tiny SAT/UNSAT cases are still the right place to estimate wrapper overhead, while the seven-case hotspot slice remains the guardrail against weakening the real exact-CLI path.
- Escalations: none

### Plan

- [x] Re-read the wrapper/startup keep/reject history and inspect the current exact-CLI wrapper shape for any non-duplicate candidate.
- [x] Measure the current exact-CLI startup floor directly and compare interpreter-only, import-only, and tiny full-CLI timings.
- [x] Conclude the task with either one bounded wrapper candidate or a retained-noop result grounded in the fresh measurements.
- [x] Update the control plane with the verified outcome.

### Verification

- `python - <<'PY' ... repeated tiny exact-CLI timings for small/test_1.cnf, special/tseitin.cnf, and large/test_8.cnf ... PY`
- passed: current exact-CLI means were about `0.0532s` on `small/test_1.cnf`, `0.0382s` on `special/tseitin.cnf`, and `0.4148s` on `large/test_8.cnf`, confirming that the startup-sensitive cases are still well below the dense UNSAT bottlenecks
- `python -X importtime -c 'import satsolver' 2>&1 | tail -n 40`
- passed: retained wrapper import time was only about `4.0ms` on top of Python/site startup, with `satsolver_core` around `3.4ms` cumulative and `satsolver_io` around `0.2ms`
- `python - <<'PY' ... repeated subprocess timings for python -c pass, python -c 'import satsolver', and python satsolver.py small/test_1.cnf /tmp/_probe.txt ... PY`
- passed: `python -c pass` averaged about `27.5ms`, `python -c 'import satsolver'` about `31.2ms`, and the full small SAT CLI about `36.0ms`, leaving only a few milliseconds of repo-local wrapper plus solve-path overhead beyond interpreter startup and import
- `python tools/agent_queue_check.py`
- passed: the final queue state resolves cleanly to `current_or_next_task='perf-007'`
- `python tools/codex_verify.py`
- passed: retained solver baseline plus final control-plane edits compile, pass the queue check, pass all 73 tests, and clear both wrapper smoke paths
- `git diff --check`
- passed

### Outcome

- Re-read the current wrapper/startup history and confirmed that the repo has already exhausted the most plausible exact-CLI surface trims: CLI-mode import gating, runtime-`typing` cleanup, targeted CLI-local aliasing, and no-root-pure wrapper selection are already kept, while broader alias, import-surface, parse-summary, and output-path rewrites are already rejected.
- Measured the current startup floor directly and found that most of the smallest exact-CLI runtime is now outside meaningful repo-local control on this machine: Python process startup alone is about `27.5ms`, `import satsolver` adds only about `3.7ms`, and the full `small/test_1.cnf` CLI path averages only about `36.0ms`.
- Completed `perf-006` as a retained-noop conclusion because the remaining repo-local wrapper overhead is too small, too noisy, and too exhaustively mined to justify another low-confidence patch.
- Advanced the queue to `perf-007`, where any further speed gains are more likely to come from external-reference gap analysis than from more exact-CLI wrapper trimming.

### Remaining risks

- The retained measurements are machine-specific, so a future environment with materially different Python startup cost or filesystem behavior could reopen a wrapper lane. On the current machine, though, the remaining exact-CLI floor is dominated by interpreter startup rather than repo-local wrapper logic.

## 2026-03-22 `perf-005-branching-restart-heuristics`

- Status: completed
- Task family: native-only branching and restart heuristic experiment
- Branch/worktree: current checkout
- Prompt summary: continue the next deterministic queue task, `perf-005`, by testing one bounded branching or restart heuristic change against the refreshed seven-case exact-CLI hotspot slice
- Assumptions:
  - The next viable heuristic experiment should avoid already-rejected branch-frontier, heap, and simple parameter-sweep lanes.
  - A retained-noop conclusion is acceptable if the bounded heuristic candidate loses cleanly on same-day exact-CLI evidence.
  - The refreshed seven-case slice remains the right first gate before any broader exact-CLI rerun.
- Escalations: none

### Plan

- [x] Inspect current branching and restart behavior plus recent keep/reject history to choose one non-duplicate heuristic candidate.
- [x] Implement or stage the candidate, validate correctness locally, and run the refreshed seven-case hotspot A/B.
- [x] If the hotspot signal is promising, run the broader exact-CLI repeat-aware gate; otherwise revert to a retained-noop conclusion.
- [x] Update the control plane with the verified outcome.

### Verification

- `python tools/codex_verify.py`
- passed: the temporary candidate compiled, passed the queue check, passed all 73 tests, and stayed valid on the main plus alternate-wrapper smoke cases
- `python tools/hotspot_compare.py --baseline-cli-script /tmp/perf005_restart_baseline.c4riuk/satsolver.py --candidate-cli-script satsolver.py large/test_6.cnf special/hard.cnf large/test_10.cnf medium/test_4.cnf medium/test_3.cnf satlib_more/uuf150-01.cnf large/test_8.cnf`
- candidate rejected: the low-LBD early-restart trigger regressed the seven-case two-order average from `34.7641s` to `56.2904s`, made every hotspot case slower, and still inflated `large/test_8.cnf` from about `0.35s` to about `7.5s`
- `python tools/agent_queue_check.py`
- passed: the final queue state resolves cleanly to `current_or_next_task='perf-006'`
- `python tools/codex_verify.py`
- passed: the retained solver baseline plus final control-plane edits compile, pass the queue check, pass all 73 tests, and clear both wrapper smoke paths after the revert
- `git diff --check`
- passed

### Outcome

- Chose a bounded restart-policy experiment instead of revisiting already-rejected branch-frontier or heap schemes: trigger an early root restart only when a conflict learns an `LBD <= 3` clause after at least half of the current Luby window has elapsed.
- Rejected that heuristic immediately after the refreshed seven-case exact-CLI gate regressed decisively on every measured case, including a fresh SAT-side blow-up on `large/test_8.cnf`.
- Retained no solver code from `perf-005` and advanced the queue to `perf-006`, which now becomes the next deterministic wrapper/startup lane.

### Remaining risks

- The branching/restart lane still lacks a winning classifier-based change, and `large/test_8.cnf` remains highly sensitive to restart-policy drift even when a candidate is aimed at dense UNSAT cases.

## 2026-03-22 `perf-004-propagation-clause-storage`

- Status: completed
- Task family: native-only propagation and clause-database experiment
- Branch/worktree: current checkout
- Prompt summary: continue the next deterministic queue task, `perf-004`, by testing one bounded propagation or clause-storage micro-optimization against the refreshed seven-case exact-CLI hotspot slice
- Assumptions:
  - The best candidate should come from the current `propagate()` or `reduce_database()` shape plus the latest keep/reject history, not from stale generic SAT heuristics.
  - A retained-noop conclusion is acceptable if the bounded candidate loses cleanly on same-day exact-CLI evidence.
  - The refreshed seven-case slice is the right focused A/B gate before any broader exact-CLI rerun.
- Escalations: none

### Plan

- [x] Inspect the current propagation and clause-database hot paths plus recent experiment history to choose one non-redundant bounded candidate.
- [x] Implement or stage the candidate, validate correctness locally, and run the refreshed seven-case hotspot A/B.
- [x] If the hotspot signal is promising, run the broader exact-CLI repeat-aware gate; otherwise revert to a retained-noop conclusion.
- [x] Update the control plane with the verified outcome.

### Verification

- `python tools/profile_solver.py large/test_6.cnf special/hard.cnf medium/test_4.cnf large/test_8.cnf`
- passed: the current retained baseline still shows `reduce_database()` operating on only a few hundred candidates per reduction, while learnt-large watch traffic remains real but secondary to original ternary propagation
- `python -m cProfile -s tottime satsolver.py medium/test_4.cnf /tmp/perf004_profile_medium4.txt | head -n 40`
- passed: `reduce_database()` stayed tiny (`0.021s` tottime, `0.052s` cumtime) versus `propagate()` (`2.145s` tottime), so the only justified clause-storage experiment was a retention-policy classifier change rather than reduction bookkeeping cleanup
- `python tools/codex_verify.py`
- passed: the temporary candidate compiled, passed the queue check, passed all 73 tests, and stayed valid on the main plus alternate-wrapper smoke cases
- `python tools/hotspot_compare.py --baseline-cli-script /tmp/perf004_lenbucket_baseline.TE0c9p/satsolver.py --candidate-cli-script satsolver.py large/test_6.cnf special/hard.cnf large/test_10.cnf medium/test_4.cnf medium/test_3.cnf satlib_more/uuf150-01.cnf large/test_8.cnf`
- candidate rejected: the coarse `10+`-literal learnt-clause penalty regressed the seven-case two-order average from `30.0666s` to `72.6652s`, roughly doubled `large/test_6.cnf`, and exploded `large/test_8.cnf` from about `0.31s` to `25s..27s`
- `python tools/agent_queue_check.py`
- passed: the final queue state resolves cleanly to `current_or_next_task='perf-005'`
- `python tools/codex_verify.py`
- passed: the retained solver baseline plus final control-plane edits compile, pass the queue check, pass all 73 tests, and clear both wrapper smoke paths after the revert
- `git diff --check`
- passed

### Outcome

- Profiled the refreshed hotspot baseline before changing code and confirmed that direct `reduce_database()` bookkeeping remains too small to justify another locked-set or schedule cleanup branch on its own.
- Tested one bounded clause-storage classifier: within each LBD bucket, demote `10+`-literal learnt clauses behind shorter candidates while keeping the existing top-half retention schedule unchanged.
- Rejected that candidate immediately after the refreshed seven-case exact-CLI gate regressed catastrophically, especially on `large/test_8.cnf`, so no solver code was retained.
- Completed `perf-004` as a retained-noop conclusion and advanced the queue to `perf-005`, which now becomes the next deterministic heuristic lane.

### Remaining risks

- The clause-database lane still lacks a winning native-only classifier, and `large/test_8.cnf` is highly sensitive to extra learnt-clause load. Future storage experiments should use the SAT-like guardrail early rather than trusting UNSAT-only wins.

## 2026-03-22 `perf-003-native-cli-baseline-refresh`

- Status: completed
- Task family: benchmark-driven native-only baseline refresh
- Branch/worktree: current checkout
- Prompt summary: continue the next deterministic queue task, `perf-003`, by refreshing the same-day exact-CLI native-only baseline, selecting the current hotspot slice, and grounding the next optimization targets in fresh evidence
- Assumptions:
  - The most useful first step is a same-day repeat-aware exact-CLI benchmark on the retained standard-library solver across the default benchmark folders.
  - The hotspot slice should be chosen from representative exact-CLI time contribution, not from stale historical notes alone.
  - This task is primarily measurement and planning, so the retained solver code may stay unchanged if the refreshed evidence is the only durable outcome.
- Escalations: none

### Plan

- [x] Run a same-day repeat-aware exact-CLI benchmark for the retained solver and capture a machine-readable report.
- [x] Summarize the heaviest representative cases and choose a refreshed hotspot slice with rationale.
- [x] Translate the fresh baseline into concrete next native-only optimization recommendations and update the control plane.
- [x] Run the required verification gates and record the final outcome.

### Verification

- `python tools/codex_verify.py --benchmark-mode cli --repeat 2 --benchmark-output /tmp/perf003_cli_benchmark.txt`
- passed: exact-CLI report landed at `/tmp/perf003_cli_benchmark.txt`, with `59/59` correct, `32.2896s` representative total, `64.5793s` measured total, and `64.8235s` wall clock
- `python tools/agent_queue_check.py`
- passed: final control-plane edits still resolve to `current_or_next_task='perf-004'`
- `python tools/codex_verify.py`
- passed: compile, queue check, 73 tests, and both main plus alternate-wrapper smoke paths stayed green after the hotspot-slice sync
- `git diff --check`
- passed

### Outcome

- Refreshed the same-day repeat-aware exact-CLI baseline for the retained native-only solver and confirmed that runtime is now heavily concentrated in a small UNSAT-dominant slice.
- The top two cases, `large/test_6.cnf` (`14.1187s`) and `special/hard.cnf` (`9.4353s`), account for `72.95%` of the exact-CLI total by themselves, while the top five cases reach `88.24%`.
- Chose a refreshed seven-case hotspot slice of `large/test_6.cnf`, `special/hard.cnf`, `large/test_10.cnf`, `medium/test_4.cnf`, `medium/test_3.cnf`, `satlib_more/uuf150-01.cnf`, and `large/test_8.cnf`, which together cover `90.82%` of the exact-CLI total while still preserving a SAT-like guardrail via `large/test_8.cnf`.
- Synced that seven-case slice into the future hotspot-compare verification commands for `perf-004`, `perf-005`, and `perf-006`, and pointed the next run at `perf-004` because the current baseline still argues for propagation or clause-database work before branching-policy exploration.

### Remaining risks

- The refreshed slice is still benchmark-only evidence; the next run needs a concrete bounded solver candidate before we can tell whether propagation or clause-database changes actually beat the retained baseline.

## 2026-03-22 `perf-002-native-optimization-queue`

- Status: completed
- Task family: queue seeding for native-only performance research
- Branch/worktree: current checkout
- Prompt summary: create a long-running SAT-solver optimization direction that may use external libraries during research while keeping the final retained solver standard-library only
- Assumptions:
  - The control plane should not encode this as one endless vague task because queued work in this repo must stay bounded and verifiable.
  - External libraries or solvers are acceptable only as short-lived comparison references; retained code and default verification must remain native-only.
  - The best single-run slice is to reopen the queue with a deterministic performance program and leave the first concrete benchmark task ready for the next run.
- Escalations: none

### Plan

- [x] Reframe the open-ended optimization goal as a rolling queue of bounded performance tasks.
- [x] Sync the native-only policy and external-reference rule into the durable repo guidance.
- [x] Reopen the queue, point the next run at the first exact-CLI baseline refresh task, and verify the control plane.

### Verification

- `python tools/agent_queue_check.py`
- passed: the refreshed queue, state, and next-task hint are consistent
- `python tools/codex_verify.py`
- passed: compile, queue check, unit tests, and standard smoke checks all remained green after the queue refresh
- `git diff --check`
- passed

### Outcome

- Reopened the autonomous queue with a rolling native-only optimization program instead of leaving the repo without queued work.
- Added concrete benchmark-driven tasks for baseline refresh, propagation experiments, heuristic experiments, wrapper-overhead work, and optional external-reference research.
- Clarified in the durable docs that external libraries are allowed only as short-lived research references and that only native-only wins may be retained in the submission path.

### Remaining risks

- The new optimization lane still needs same-day baseline refresh work in `perf-003` before any specific solver-change experiment should be attempted.

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
