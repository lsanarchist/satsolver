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
