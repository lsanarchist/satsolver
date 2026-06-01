# CNFgen regression pack

This folder contains a deterministic CNFgen-generated regression corpus for
solver robustness checks. The generated DIMACS cases live in the flat
`cnfgen_cases/` directory so they can be used directly by `benchmark_suite.py`.

Current pack: **228** cases across **30** CNFgen families:

- `152` SAT
- `76` UNSAT
- `126` easy, `82` moderate, `20` stress

Pack constraints:

- `vars <= 500`
- `clauses <= 2000`
- every case has known `SAT` or `UNSAT` status
- smoke timeout is `60s` per case

## Generate

CNFgen is only needed to rebuild the pack. It is not a solver dependency.

```bash
python cnfgen_regression_pack/generate_cnfgen_pack.py --cnfgen /path/to/cnfgen
```

The generator writes:

- `cnfgen_cases/*.cnf`
- `CNF_LIST.md` with one row for every retained `.cnf`
- `MANIFEST.tsv` for `tests/scripts/run_regression_smoke.py`
- `manifest.csv` with family, status, size, timeout, and source command metadata

## Validate

```bash
python tests/scripts/run_regression_smoke.py --solver ./satsolver.py --suite cnfgen_regression_pack --timeout 60
```

Last full smoke result: `228/228` passed, max per-case time `35.4312s`.

For timing-oriented CLI validation:

```bash
python benchmark_suite.py satsolver /tmp/cnfgen_pack_bench.txt cnfgen_regression_pack/cnfgen_cases --bruteforce-var-limit 16 --cli-script satsolver.py
```

The benchmark harness validates SAT assignments and brute-force checks UNSAT
only for instances within its variable limit. The smoke runner additionally
compares solver `SAT` or `UNSAT` output against `MANIFEST.tsv`.
