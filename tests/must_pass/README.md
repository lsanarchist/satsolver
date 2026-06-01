# Must-Pass SAT Solver Regression Suite

Run this suite after solver or packaging changes:

```bash
python tests/scripts/generate_regression_cases.py
python tests/scripts/run_regression_smoke.py --solver ./satsolver.py --suite tests/must_pass --timeout 60
```

The suite intentionally mixes hard CDCL cases, structural detector cases, phase-portfolio SAT cases, parser/generated guards, and false-positive checks for the Mycielski graph-coloring detector.

The current submission is modular. A grader or archive must include:

```text
satsolver.py
satsolver_core.py
satsolver_io.py
```

Use this packaging check before delivery:

```bash
python tests/scripts/check_single_file_submission.py --solver ./satsolver.py
```
