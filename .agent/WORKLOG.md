# Worklog

## 2026-03-22 10:20 UTC — cp-001
- Status: done
- Summary: Bootstrapped a repo-local autonomous queue control plane with a repo-specific master contract, runbook, state snapshot, phased task queue, handoff, decision log, test gates, worklog, and stable repeated prompt.
- Files changed: `AGENT.md`, `.agent/README.md`, `.agent/RUNBOOK.md`, `.agent/STATE.yaml`, `.agent/TASK_QUEUE.yaml`, `.agent/HANDOFF.md`, `.agent/DECISIONS.md`, `.agent/WORKLOG.md`, `.agent/TEST_GATES.md`, `QUEUE_PROMPT.md`
- Verification: `python tools/codex_verify.py` — passed
- Follow-up: Complete `cp-002` whenever the queue bootstrap is coupled with legacy-doc alignment in the same run; otherwise move to `cp-003`.

## 2026-03-22 10:20 UTC — cp-002
- Status: done
- Summary: Synced the legacy Codex-facing instructions and operator docs to the new queue control plane so future identical prompts read one deterministic workflow.
- Files changed: `AGENTS.md`, `README.md`, `PLANS.md`, `docs/codex/operator-guide.md`, `docs/codex/queued-task-template.md`
- Verification: `python tools/codex_verify.py` — passed
- Follow-up: Start `cp-003` next to add a machine-checkable control-plane consistency validator.

## 2026-03-22 10:47 UTC — cp-003
- Status: done
- Summary: Added a repo-local control-plane consistency checker, regression tests, and default verification wiring so stale queue state fails fast during autonomous runs.
- Files changed: `tools/agent_queue_check.py`, `tests/test_agent_queue_check.py`, `tools/codex_verify.py`, `tests/test_codex_verify.py`, `README.md`, `docs/codex/operator-guide.md`, `.agent/TEST_GATES.md`, `PLANS.md`, `.agent/STATE.yaml`, `.agent/TASK_QUEUE.yaml`, `.agent/HANDOFF.md`, `.agent/DECISIONS.md`, `.agent/WORKLOG.md`
- Verification: `python tools/agent_queue_check.py` — passed; `python -m unittest discover -s tests -q` — passed; `python tools/codex_verify.py` — passed
- Follow-up: Continue with `sat-001`, the shared DIMACS parsing and result-writing deduplication task.

## 2026-03-22 12:40 UTC — sat-001
- Status: done
- Summary: Extracted shared DIMACS parsing and result-writing helpers into `satsolver_io.py`, switched the thin wrappers to that helper, and added regression coverage for the shared path.
- Files changed: `satsolver_io.py`, `satsolver.py`, `satsolver_fast.py`, `satsolver_pysat.py`, `tests/test_solver_io.py`, `AGENT.md`, `AGENTS.md`, `README.md`, `PLANS.md`, `.agent/STATE.yaml`, `.agent/TASK_QUEUE.yaml`, `.agent/HANDOFF.md`, `.agent/DECISIONS.md`, `.agent/WORKLOG.md`
- Verification: `python tools/agent_queue_check.py` — passed; `python -m unittest discover -s tests -q` — passed; `python tools/codex_verify.py` — passed
- Follow-up: Continue with `tool-001`, the wrapper-verification expansion that now builds on `satsolver_io.py`.

## 2026-03-22 12:45 UTC — tool-001
- Status: done
- Summary: Expanded the default verification helper so it smoke-tests `satsolver_fast.py` alongside the main submission CLI, and added regression coverage for the alternate-wrapper verification flow.
- Files changed: `tools/codex_verify.py`, `tests/test_codex_verify.py`, `AGENT.md`, `AGENTS.md`, `README.md`, `docs/codex/operator-guide.md`, `PLANS.md`, `.agent/STATE.yaml`, `.agent/TASK_QUEUE.yaml`, `.agent/HANDOFF.md`, `.agent/DECISIONS.md`, `.agent/WORKLOG.md`
- Verification: `python -m unittest discover -s tests -p 'test_codex_verify.py' -q` — passed; `python tools/codex_verify.py` — passed
- Follow-up: Continue with `perf-001`, the same-day benchmark revalidation of the portfolio gating thresholds.

## 2026-03-22 12:51 UTC — perf-001
- Status: done
- Summary: Revalidated the retained portfolio thresholds with same-day corpus inspection and a bounded broadened-threshold exact-CLI A/B, then kept the current gate unchanged because the candidate regressed decisively.
- Files changed: `PLANS.md`, `.agent/STATE.yaml`, `.agent/TASK_QUEUE.yaml`, `.agent/HANDOFF.md`, `.agent/WORKLOG.md`
- Verification: `python - <<'PY' ... corpus scan for current portfolio hits and near misses ... PY` — passed; `python -m py_compile /tmp/scratch_satsolver_portfolio_minclauses800.py` — passed; `python /tmp/scratch_satsolver_portfolio_minclauses800.py small/test_1.cnf /tmp/perf001_sat.txt` and `python tools/checker.py small/test_1.cnf /tmp/perf001_sat.txt` — passed; `python /tmp/scratch_satsolver_portfolio_minclauses800.py special/tseitin.cnf /tmp/perf001_unsat.txt` and `python tools/checker.py special/tseitin.cnf /tmp/perf001_unsat.txt --bruteforce-var-limit 0` — passed; `python tools/hotspot_compare.py --baseline-cli-script satsolver.py --candidate-cli-script /tmp/scratch_satsolver_portfolio_minclauses800.py --repeat 2 large/test_1.cnf large/test_7.cnf large/test_8.cnf large/test_9.cnf` — candidate rejected; `python tools/codex_verify.py` — passed
- Follow-up: No queued tasks remain. Add a new task to `.agent/TASK_QUEUE.yaml` before the next autonomous run.

## 2026-03-22 13:31 UTC — perf-002
- Status: done
- Summary: Reopened the queue with a rolling native-only optimization program, clarified that external libraries are research-only references, and queued the next exact-CLI baseline refresh task.
- Files changed: `AGENT.md`, `AGENTS.md`, `PLANS.md`, `.agent/DECISIONS.md`, `.agent/HANDOFF.md`, `.agent/STATE.yaml`, `.agent/TASK_QUEUE.yaml`, `.agent/WORKLOG.md`
- Verification: `python tools/agent_queue_check.py` — passed; `python tools/codex_verify.py` — passed; `git diff --check` — passed
- Follow-up: Start `perf-003` next to refresh the same-day native-only exact-CLI baseline and hotspot slice before attempting further solver optimizations.

## 2026-03-22 13:59 UTC — perf-003
- Status: done
- Summary: Refreshed the same-day repeat-aware exact-CLI baseline, selected a new seven-case hotspot slice covering 90.82% of total runtime, and retargeted future performance tasks to that slice.
- Files changed: `AGENTS.md`, `PLANS.md`, `.agent/HANDOFF.md`, `.agent/STATE.yaml`, `.agent/TASK_QUEUE.yaml`, `.agent/WORKLOG.md`
- Verification: `python tools/codex_verify.py --benchmark-mode cli --repeat 2 --benchmark-output /tmp/perf003_cli_benchmark.txt` — passed; `python tools/agent_queue_check.py` — passed; `python tools/codex_verify.py` — passed; `git diff --check` — passed
- Follow-up: Start `perf-004` next and keep the candidate evaluation centered on the refreshed seven-case exact-CLI hotspot slice.

## 2026-03-22 14:11 UTC — perf-004
- Status: done
- Summary: Profiled the refreshed hotspot baseline, tested one bounded clause-storage classifier that penalized `10+`-literal learnt clauses within each LBD bucket, and retained no solver change after the seven-case exact-CLI A/B regressed catastrophically.
- Files changed: `PLANS.md`, `.agent/HANDOFF.md`, `.agent/STATE.yaml`, `.agent/TASK_QUEUE.yaml`, `.agent/WORKLOG.md`
- Verification: `python tools/profile_solver.py large/test_6.cnf special/hard.cnf medium/test_4.cnf large/test_8.cnf` — passed; `python -m cProfile -s tottime satsolver.py medium/test_4.cnf /tmp/perf004_profile_medium4.txt | head -n 40` — passed; `python tools/codex_verify.py` — passed; `python tools/hotspot_compare.py --baseline-cli-script /tmp/perf004_lenbucket_baseline.TE0c9p/satsolver.py --candidate-cli-script satsolver.py large/test_6.cnf special/hard.cnf large/test_10.cnf medium/test_4.cnf medium/test_3.cnf satlib_more/uuf150-01.cnf large/test_8.cnf` — candidate rejected (`30.0666s -> 72.6652s` two-order average, `large/test_8.cnf` exploded to `25s..27s`); `python tools/agent_queue_check.py` — passed; `python tools/codex_verify.py` — passed; `git diff --check` — passed
- Follow-up: Continue with `perf-005`; treat `large/test_8.cnf` as an early guardrail for any future learnt-database or clause-retention experiments.

## 2026-03-22 14:21 UTC — perf-005
- Status: done
- Summary: Tested one bounded restart-policy classifier that triggered early root restarts after low-LBD conflicts late in the current Luby window, then retained no solver change after the seven-case exact-CLI A/B regressed on every measured case.
- Files changed: `PLANS.md`, `.agent/HANDOFF.md`, `.agent/STATE.yaml`, `.agent/TASK_QUEUE.yaml`, `.agent/WORKLOG.md`
- Verification: `python tools/codex_verify.py` — passed; `python tools/hotspot_compare.py --baseline-cli-script /tmp/perf005_restart_baseline.c4riuk/satsolver.py --candidate-cli-script satsolver.py large/test_6.cnf special/hard.cnf large/test_10.cnf medium/test_4.cnf medium/test_3.cnf satlib_more/uuf150-01.cnf large/test_8.cnf` — candidate rejected (`34.7641s -> 56.2904s` two-order average, `large/test_8.cnf` rose to about `7.5s`); `python tools/agent_queue_check.py` — passed; `python tools/codex_verify.py` — passed; `git diff --check` — passed
- Follow-up: Continue with `perf-006`; treat `large/test_8.cnf` as an early guardrail for future restart-policy experiments too.

## 2026-03-22 14:28 UTC — perf-006
- Status: done
- Summary: Re-measured the remaining exact-CLI wrapper and startup floor, confirmed that interpreter startup now dominates the tiny-case path on this machine, and retained no solver change because the obvious native-only wrapper trims are already exhausted.
- Files changed: `PLANS.md`, `.agent/HANDOFF.md`, `.agent/STATE.yaml`, `.agent/TASK_QUEUE.yaml`, `.agent/WORKLOG.md`
- Verification: `python - <<'PY' ... repeated tiny exact-CLI timings for small/test_1.cnf, special/tseitin.cnf, and large/test_8.cnf ... PY` — passed (`0.0532s`, `0.0382s`, `0.4148s` means); `python -X importtime -c 'import satsolver' 2>&1 | tail -n 40` — passed (`satsolver_core` about `3.4ms`, `satsolver_io` about `0.2ms`, `satsolver` about `4.0ms` cumulative); `python - <<'PY' ... repeated subprocess timings for python -c pass, python -c 'import satsolver', and python satsolver.py small/test_1.cnf /tmp/_probe.txt ... PY` — passed (`27.5ms`, `31.2ms`, `36.0ms` means); `python tools/agent_queue_check.py` — passed; `python tools/codex_verify.py` — passed; `git diff --check` — passed
- Follow-up: Continue with `perf-007`, using optional external solver references only to sharpen the next native-only optimization target rather than revisiting the already-thin wrapper lane.

## 2026-03-22 14:38 UTC — perf-007
- Status: done
- Summary: Revalidated the optional PySAT comparison path, refreshed the external ceiling on the current dense hotspot and structural fast-exit slices, and used that same-day evidence plus a fresh profiler run to queue the next native-only task around dense watch-family traversal instead of more wrapper work.
- Files changed: `PLANS.md`, `.agent/STATE.yaml`, `.agent/TASK_QUEUE.yaml`, `.agent/HANDOFF.md`, `.agent/DECISIONS.md`, `.agent/WORKLOG.md`
- Verification: `.venv-external-sat/bin/python satsolver_pysat.py small/test_1.cnf /tmp/perf007_pysat_small_sat.txt && python tools/checker.py small/test_1.cnf /tmp/perf007_pysat_small_sat.txt` — passed; `.venv-external-sat/bin/python satsolver_pysat.py special/tseitin.cnf /tmp/perf007_pysat_small_unsat.txt && python tools/checker.py special/tseitin.cnf /tmp/perf007_pysat_small_unsat.txt --bruteforce-var-limit 0` — passed; `python - <<'PY' ... backend sweep across minisat22, glucose4, cadical195, mergesat3, kissat404 on large/test_6.cnf and special/hard.cnf ... PY` — passed (`minisat22` best at `0.5813s`); `SATSOLVER_PYSAT_BACKEND=minisat22 python tools/hotspot_compare.py --baseline-cli-script satsolver.py --candidate-cli-script satsolver_pysat.py --candidate-python-executable .venv-external-sat/bin/python large/test_6.cnf special/hard.cnf large/test_10.cnf medium/test_4.cnf medium/test_3.cnf satlib_more/uuf150-01.cnf large/test_8.cnf` — passed (`24.6944s` baseline versus `1.2486s` external ceiling); `SATSOLVER_PYSAT_BACKEND=minisat22 python tools/hotspot_compare.py --baseline-cli-script satsolver.py --candidate-cli-script satsolver_pysat.py --candidate-python-executable .venv-external-sat/bin/python special/pigeonhole.cnf special/tseitin.cnf` — passed (`0.0702s` baseline versus `3.4322s` external ceiling); `python tools/profile_solver.py large/test_6.cnf special/hard.cnf` — passed; `python tools/agent_queue_check.py` — passed; `python tools/codex_verify.py` — passed; `git diff --check` — passed
- Follow-up: Continue with `perf-008`, testing a true watch-family split on the dense UNSAT hotspot slice while keeping `large/test_8.cnf`, `special/pigeonhole.cnf`, and `special/tseitin.cnf` as guardrails.

## 2026-03-22 14:50 UTC — perf-008
- Status: done
- Summary: Tested one true problem-ternary watcher split, rejected it after the dense seven-case exact-CLI gate regressed, and recorded that the layout change also perturbed the dense UNSAT search path badly enough to blow up `large/test_6.cnf`.
- Files changed: `PLANS.md`, `.agent/DECISIONS.md`, `.agent/HANDOFF.md`, `.agent/STATE.yaml`, `.agent/TASK_QUEUE.yaml`, `.agent/WORKLOG.md`
- Verification: `python tools/codex_verify.py` — passed on the temporary candidate before the performance gate; `python tools/hotspot_compare.py --baseline-cli-script /tmp/perf008_watchsplit_baseline/satsolver.py --candidate-cli-script satsolver.py large/test_6.cnf special/hard.cnf large/test_10.cnf medium/test_4.cnf medium/test_3.cnf satlib_more/uuf150-01.cnf large/test_8.cnf` — candidate rejected (`24.6075s -> 28.1011s`, with `large/test_6.cnf` worsening from about `12.0s` to about `16.5s`); `python tools/hotspot_compare.py --baseline-cli-script /tmp/perf008_watchsplit_baseline/satsolver.py --candidate-cli-script satsolver.py special/pigeonhole.cnf special/tseitin.cnf` — passed (`0.0757s -> 0.0604s`); `python tools/profile_solver.py large/test_6.cnf special/hard.cnf` — passed (`large/test_6.cnf` conflicts `59,201 -> 81,161`, `special/hard.cnf` conflicts `44,619 -> 39,511`, `problem_ternary_mixed_batch_share=0.0000`); `python tools/agent_queue_check.py` — passed; `python tools/codex_verify.py` — passed; `git diff --check` — passed
- Follow-up: Continue with `perf-009`, focusing on dense-UNSAT conflict-analysis rather than another watcher-layout rearrangement.

## 2026-03-22 15:08 UTC — perf-009
- Status: done
- Summary: Probed the current dense-UNSAT minimization selector mix, tested one narrow relaxed-minimization candidate that skipped scans for learnt `10+`-literal reasons, and retained no solver change after the seven-case exact-CLI gate regressed badly.
- Files changed: `PLANS.md`, `.agent/DECISIONS.md`, `.agent/HANDOFF.md`, `.agent/STATE.yaml`, `.agent/TASK_QUEUE.yaml`, `.agent/WORKLOG.md`
- Verification: `python - <<'PY' ... MeasureSolver selector probe over large/test_6.cnf and special/hard.cnf ... PY` — passed (`learnt 10+` reasons removed only `4,012 / 36,846` literals on `large/test_6.cnf` and `1,885 / 21,289` on `special/hard.cnf`); `python tools/codex_verify.py` — passed on the temporary candidate before the performance gate; `python tools/hotspot_compare.py --baseline-cli-script /tmp/perf009_minlearn10_baseline/satsolver.py --candidate-cli-script satsolver.py large/test_6.cnf special/hard.cnf large/test_10.cnf medium/test_4.cnf medium/test_3.cnf satlib_more/uuf150-01.cnf large/test_8.cnf` — candidate rejected (`35.7221s -> 51.1322s`, with `large/test_8.cnf` rising from about `0.38s` to about `5.07s`); `python tools/agent_queue_check.py` — passed; `python tools/codex_verify.py` — passed; `git diff --check` — passed
- Follow-up: Continue with `perf-010`, targeting same-clause-content conflict-analysis bookkeeping instead of more minimization-relaxation rules.

## 2026-03-22 15:17 UTC — perf-010
- Status: done
- Summary: Tested one same-content conflict-analysis bookkeeping candidate by making `minimize_learnt()` ternary-first, then retained no solver change after the seven-case exact-CLI hotspot gate regressed overall.
- Files changed: `PLANS.md`, `.agent/HANDOFF.md`, `.agent/STATE.yaml`, `.agent/TASK_QUEUE.yaml`, `.agent/WORKLOG.md`
- Verification: `python -m cProfile -s tottime satsolver.py large/test_6.cnf /tmp/perf010_profile_large6.txt | head -n 45` — passed (`analyze()` `3.045s`, `minimize_learnt()` `0.949s`, `prepare_learnt_clause()` `0.347s`); `python tools/codex_verify.py` — passed on the temporary candidate before the performance gate; `python tools/hotspot_compare.py --baseline-cli-script /tmp/perf010_ternaryfirst_baseline/satsolver.py --candidate-cli-script satsolver.py large/test_6.cnf special/hard.cnf large/test_10.cnf medium/test_4.cnf medium/test_3.cnf satlib_more/uuf150-01.cnf large/test_8.cnf` — candidate rejected (`30.6097s -> 32.9908s`, with `large/test_6.cnf` regressing in both orders); `python tools/agent_queue_check.py` — passed; `python tools/codex_verify.py` — passed; `git diff --check` — passed
- Follow-up: Continue with `perf-011`, probing learnt-finalization bookkeeping instead of more `minimize_learnt()` reason-size branch-order tweaks.

## 2026-03-22 15:25 UTC — perf-011
- Status: done
- Summary: Tested one same-content learnt-finalization bookkeeping candidate by peeling the first two literals out of `prepare_learnt_clause()`, then retained no solver change after the seven-case exact-CLI hotspot gate regressed overall.
- Files changed: `PLANS.md`, `.agent/STATE.yaml`, `.agent/TASK_QUEUE.yaml`, `.agent/HANDOFF.md`, `.agent/WORKLOG.md`
- Verification: `python tools/codex_verify.py` — passed on the temporary candidate before the performance gate; `python tools/hotspot_compare.py --baseline-cli-script /tmp/perf011_prepare_baseline/satsolver.py --candidate-cli-script satsolver.py large/test_6.cnf special/hard.cnf large/test_10.cnf medium/test_4.cnf medium/test_3.cnf satlib_more/uuf150-01.cnf large/test_8.cnf` — candidate rejected (`29.3900s -> 30.4121s`, with the largest loss on `large/test_6.cnf` in forward order at `13.5296s -> 14.9891s`); `python tools/agent_queue_check.py` — passed; `python tools/codex_verify.py` — passed; `git diff --check` — passed
- Follow-up: Continue with `perf-012`, targeting a different post-minimization learnt-metadata or analyze-to-finalization boundary surface instead of more pure `prepare_learnt_clause()` loop-shape cleanup.

## 2026-03-22 15:42 UTC — perf-012
- Status: done
- Summary: Kept one same-content conflict-analysis boundary change by computing best backtrack and LBD metadata during post-minimization learnt compaction, deleting the separate finalization pass while preserving the dense hard-case search counters.
- Files changed: `satsolver_core.py`, `tools/profile_solver.py`, `PLANS.md`, `benchmark_summary.md`, `experiments.jsonl`, `.agent/STATE.yaml`, `.agent/TASK_QUEUE.yaml`, `.agent/HANDOFF.md`, `.agent/DECISIONS.md`, `.agent/WORKLOG.md`
- Verification: `python -m cProfile -s tottime satsolver.py large/test_6.cnf /tmp/perf012_profile_large6.txt | head -n 50` — passed (`analyze()` `2.206s`, `minimize_learnt()` `0.674s`, `prepare_learnt_clause()` `0.246s` on the retained baseline); `python tools/codex_verify.py` — passed on the temporary candidate before the performance gates; `python tools/hotspot_compare.py --baseline-cli-script /tmp/perf012_metadata_baseline/satsolver.py --candidate-cli-script satsolver.py large/test_6.cnf special/hard.cnf large/test_10.cnf medium/test_4.cnf medium/test_3.cnf satlib_more/uuf150-01.cnf large/test_8.cnf` — passed (`30.2756s -> 29.8805s`); `python tools/hotspot_compare.py --baseline-cli-script /tmp/perf012_metadata_baseline/satsolver.py --candidate-cli-script satsolver.py special/pigeonhole.cnf special/tseitin.cnf` — passed (`0.0748s -> 0.0725s`); `python tools/codex_verify.py --benchmark-mode cli --repeat 2` — passed (`59/59` correct, `32.2896s -> 31.9532s` representative total); `python tools/profile_solver.py large/test_6.cnf special/hard.cnf` — passed (still `72,886/59,201` decisions/conflicts on `large/test_6.cnf` and `54,245/44,619` on `special/hard.cnf`); `python tools/agent_queue_check.py` — passed; `python tools/codex_verify.py` — passed; `git diff --check` — passed
- Follow-up: Continue with `perf-013`, refreshing the dense-UNSAT conflict-analysis profile after this metadata-boundary keep before choosing the next bounded solver-core experiment.
