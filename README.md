# SAT Solver

Benchmark-driven Python SAT solver with a submission CLI at `satsolver.py`.

## Quick Start

```bash
python satsolver.py small/test_1.cnf /tmp/result.txt
python tools/checker.py small/test_1.cnf /tmp/result.txt
python tools/codex_verify.py
```

## Repo Map

- `satsolver.py`: required `python satsolver.py input.cnf output.txt` entrypoint
- `satsolver_core.py`: shared CDCL solver core
- `satsolver_fast.py`: alternate comparison wrapper over the shared core
- `satsolver_blaze.py`: legacy comparison solver
- `satsolver_pysat.py`: optional external-library comparison wrapper
- `benchmark_suite.py`: validated benchmark harness
- `tools/checker.py`: SAT/UNSAT output validator
- `tools/profile_solver.py`: solver profiler for hotspot cases
- `tools/hotspot_compare.py`: same-day baseline-vs-candidate comparator
- `tests/`: regression and tooling tests
- `small/`, `medium/`, `large/`, `special/`, `satlib_subset/`, `satlib_more/`: benchmark inputs

## Codex Workflow

- `AGENTS.md`: repo-specific agent instructions and definition of done
- `PLANS.md`: durable plan and execution log for queued autonomous tasks
- `skills/autonomous-sat-maintenance/SKILL.md`: reusable repo-local skill for benchmark-driven solver work
- `docs/codex/operator-guide.md`: operator instructions for future queued runs
- `docs/codex/queued-task-template.md`: prompt template for future queued Codex tasks

## Verification Commands

- Fast verification: `python tools/codex_verify.py`
- Exact-CLI benchmark verification: `python tools/codex_verify.py --benchmark-mode cli --repeat 2`
- Full exact-CLI benchmark: `python benchmark_suite.py satsolver /tmp/bench_cli.txt small medium large special satlib_subset satlib_more --bruteforce-var-limit 16 --cli-script satsolver.py`
