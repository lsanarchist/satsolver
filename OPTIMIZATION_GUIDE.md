# SAT Solver Optimization Guide

This repo is now assignment-focused, so every optimization must preserve the required CLI contract:

```bash
python satsolver.py input.cnf output.txt
```

The submission path must stay standard-library only.

## Current Bottleneck

Profiling the 278-case course set shows the solver spends most of its time in CDCL propagation:

- `satsolver_core.py:337 propagate`: main hot path
- `satsolver_core.py:555 analyze`: conflict analysis
- `satsolver_core.py:470 _minimize_learnt_and_prepare`: learned-clause minimization
- `satsolver_core.py:622 pick_branch_literal`: variable selection

`propagate()` dominates, so optimize it before changing branching.

## Optimization Loop

Use small, reversible changes:

1. Change one hot path at a time.
2. Run syntax and smoke checks.
3. Run the original 35 benchmark.
4. Run at least a focused 278 benchmark or hotspot benchmark.
5. Keep the change only if correctness stays perfect and timing improves beyond normal noise.

Useful commands:

```bash
python -m py_compile satsolver.py satsolver_core.py satsolver_io.py
python benchmark_suite.py satsolver /tmp/bench35.txt /tmp/satsolver_original_35/small /tmp/satsolver_original_35/medium /tmp/satsolver_original_35/large /tmp/satsolver_original_35/special --bruteforce-var-limit 16 --cli-script satsolver.py --repeat 5
python benchmark_suite.py satsolver /tmp/bench278.txt /tmp/satsolver_course278 --bruteforce-var-limit 16 --cli-script satsolver.py --repeat 2
```

For profiling:

```bash
SATSOLVER_DISABLE_PORTFOLIO=1 python -m cProfile -o /tmp/profile.out benchmark_suite.py satsolver /tmp/profile_bench.txt /tmp/satsolver_course278 --bruteforce-var-limit 16
```

## First Targets

Preferred order:

1. `propagate()` micro-optimizations: reduce global lookups, repeated method lookup, and list mutation overhead.
2. `analyze()` and learned-clause minimization: reduce repeated `abs()` and list scans.
3. `pick_branch_literal()`: consider a heap only after propagation/analyze changes settle.

Avoid large rewrites unless the previous small experiments show a clear ceiling.

## Result Hygiene

Keep benchmark artifacts only when they answer a question. Name them by dataset and mode, for example:

- `satsolver_original_35_avg5.txt`
- `satsolver_course_cnf_tests_278_avg5.txt`
- `satsolver_course278_profile.txt`

Do not compare fullCPU portfolio numbers to normal assignment numbers. They measure different things.

## Retained Experiments

### Replace `abs(literal)` In Analysis Hot Paths

Status: retained.

Change: in `analyze()` and `_minimize_learnt_and_prepare()`, use the solver's precomputed `literal_var[literal]` mapping instead of repeated `abs(literal)` calls.

Reason: profile data showed tens of millions of `abs()` calls across the 278-case profile. The solver already maintains `literal_var` for positive and negative literal indexing.

Validation:

- Syntax and SAT/UNSAT smoke checks passed.
- 35-case avg5: `35/35`, `0 errors`, representative total `9.4389s`.
- 278-case repeat2: `278/278`, `0 errors`, representative total `25.9634s`.
