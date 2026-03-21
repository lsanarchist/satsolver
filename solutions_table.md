# Solutions Table

This file summarizes the solver solutions and the benchmark results currently recorded for them in the repository.

Scope note:
- This covers retained tracked solver variants and their benchmark-output files.
- It does not try to list every temporary scratch branch ever tested and reverted.
- Source of truth for the notes below: `satsolver.py`, `satsolver_core.py`, `satsolver_fast.py`, `satsolver_blaze.py`, `benchmark_summary.md`, `out_extended.txt`, `out_cli_extended.txt`, `out_fast_cli_extended.txt`, and `out_blaze_extended.txt`.

Benchmark note:
- “Current retained artifact” means the benchmark file that is currently in the repo.
- “Historical best recorded” means the best snapshot explicitly called out in `benchmark_summary.md`.
- Those are not always the same thing.

## Times At A Glance

| Solution | Current exact-CLI time | Best recorded exact-CLI time | Current in-process time | Best recorded in-process time | Worst-case note |
| --- | --- | --- | --- | --- | --- |
| Main retained solver (`satsolver.py`) | `31.6015s` on `35` cases from `out_cli_extended.txt` | `25.7027s` on `59` cases from `benchmark_summary.md` | `27.6294s` on `59` cases from `out_extended.txt` | `25.1541s` on `59` cases from `benchmark_summary.md` | Current CLI artifact worst case: `large/test_6.cnf` at `14.7695s`; best recorded exact-CLI worst case: `11.4367s` |
| Fast alternate (`satsolver_fast.py`) | `27.5074s` on `59` cases from `out_fast_cli_extended.txt` | `27.3829s` on `59` cases from `benchmark_summary.md` | No retained in-process artifact | No recorded in-process best | Current worst case: `large/test_6.cnf` at `11.8449s` |
| Blaze legacy (`satsolver_blaze.py`) | `41.0408s` on `59` cases from `out_blaze_extended.txt` | No separate better recorded snapshot surfaced in current summary | No retained in-process artifact | No recorded in-process best | Current worst case: `large/test_6.cnf` at `17.1070s` |

## Quick Time Ranking

| Comparison lane | 1st | 2nd | 3rd |
| --- | --- | --- | --- |
| Current retained exact-CLI artifacts | `satsolver_fast.py` at `27.5074s` | `satsolver.py` at `31.6015s` | `satsolver_blaze.py` at `41.0408s` |
| Best recorded exact-CLI results in repo notes | `satsolver.py` at `25.7027s` | `satsolver_fast.py` at `27.3829s` | `satsolver_blaze.py` not recorded as competitive |

## Solver Variants

| Solution | Main files | Type | Current role | Submission-ready | Key traits | Benchmark note |
| --- | --- | --- | --- | --- | --- | --- |
| Main retained solver | `satsolver.py`, `satsolver_core.py` | Exact-CLI wrapper over shared core | Current mainline and best-known submission configuration in the repo summary | Yes | Byte-level DIMACS parse/write path, import-gated wrapper, structural XOR/pigeonhole UNSAT presolvers, no root-pure on the main fast path, narrow portfolio gate, shared CDCL core | `benchmark_summary.md` names this as the best-known submission configuration; current retained CLI artifact is `out_cli_extended.txt` |
| Shared core engine | `satsolver_core.py` | Shared CDCL engine | Core implementation used by main and fast wrappers | Not by itself | Watched literals, VSIDS-style activity, Luby restarts, clause database reduction, ternary fast path, conflict analysis, portfolio gate helpers | Not benchmarked as a standalone script; performance is observed through the wrappers |
| Fast alternate solver | `satsolver_fast.py`, `satsolver_core.py` | Alternate exact-CLI wrapper | Comparison / alternate candidate kept around because it has been competitive on real exact-CLI runs | Yes | Lean wrapper, byte-level DIMACS parse/write path, direct use of the shared core, alternate no-root-pure solve path | `benchmark_summary.md` records a historical best repeat-aware exact-CLI snapshot of `27.3829s`; current merged artifact is `out_fast_cli_extended.txt` |
| Blaze legacy solver | `satsolver_blaze.py` | Older standalone alternate solver | Historical comparison baseline only | Yes | Older monolithic solver variant with its own implementation and older branching/polarity behavior | Recent logs say it is slower than the retained main solver on current hotspot comparisons |

## Current Retained Benchmark Results

| Solution | Mode | Source artifact | Suite size | Validation summary | Runtime summary | Worst case |
| --- | --- | --- | ---: | --- | --- | --- |
| Main retained solver (`satsolver.py`) | Exact CLI, repeat-aware (`repeat_count=2`) | `out_cli_extended.txt` | `35` cases | `35/35` solved correctly, `16` SAT, `19` UNSAT, `0` errors | Representative total `31.6015s`, measured total `63.2029s`, wall clock `63.3686s`, avg `0.9029s`, median `0.0406s` | `large/test_6.cnf` at `14.7695s` |
| Main retained solver (`satsolver.py`) | In-process / module, repeat-aware (`repeat_count=2`) | `out_extended.txt` | `59` cases | `59/59` solved correctly, `28` SAT, `31` UNSAT, `0` errors | Representative total `27.6294s`, measured total `55.2588s`, wall clock `55.4222s`, avg `0.4683s`, median `0.0046s` | `large/test_6.cnf` at `12.8131s` |
| Fast alternate solver (`satsolver_fast.py`) | Exact CLI, repeat-aware (`repeat_count=2`) | `out_fast_cli_extended.txt` | `59` cases | `59/59` solved correctly, `28` SAT, `31` UNSAT, `0` errors | Representative total `27.5074s`, measured total `55.0148s`, wall clock `55.2459s`, avg `0.4662s`, median `0.0352s` | `large/test_6.cnf` at `11.8449s` |
| Blaze legacy solver (`satsolver_blaze.py`) | Standalone run, single-shot artifact format | `out_blaze_extended.txt` | `59` cases | Older artifact format; summary does not include solved-correctly counters in the final line | Total `41.0408s`, wall clock `41.0849s`, avg `0.6956s`, median `0.0052s` | `large/test_6.cnf` at `17.1070s` |

## Historical Best Recorded Results

| Solution | Mode | Source | Suite size | Recorded best |
| --- | --- | --- | ---: | --- |
| Main retained solver (`satsolver.py`) | Exact CLI, repeat-aware | `benchmark_summary.md` “Best repeat-aware exact-CLI 59-case snapshot” | `59` cases | `25.7027s` representative, `59/59` correct, worst case `11.4367s` on `large/test_6.cnf` |
| Main retained solver (`satsolver.py`) | In-process / module, repeat-aware | `benchmark_summary.md` “Latest repeat-aware in-process 59-case snapshot” | `59` cases | `25.1541s` representative, `59/59` correct, worst case `11.6988s` on `large/test_6.cnf` |
| Main retained solver (`satsolver.py`) | Exact CLI, single run | `benchmark_summary.md` “Best single-run exact-CLI validated 59-case snapshot” | `59` cases | `28.4550s` total, `59/59` correct, mean `0.4823s`, median `0.0478s` |
| Main retained solver (`satsolver.py`) | In-process / module, single run | `benchmark_summary.md` “Best single-run in-process validated 59-case snapshot” | `59` cases | `26.4178s` total, `59/59` correct, mean `0.4478s`, median `0.0042s` |
| Fast alternate solver (`satsolver_fast.py`) | Exact CLI, repeat-aware | `benchmark_summary.md` “Historical best repeat-aware snapshot” | `59` cases | `27.3829s` representative, `59/59` correct |

## Benchmark / Output Artifacts

| Artifact file | Related solution | What it records | Current meaning |
| --- | --- | --- | --- |
| `out_cli_extended.txt` | Main retained solver (`satsolver.py`) | Exact-CLI benchmark artifact | Current retained exact-CLI output snapshot for the main submission solver |
| `out_extended.txt` | Main retained solver (`satsolver.py`) | In-process / module benchmark artifact | Current retained module-mode benchmark snapshot for the main solver path |
| `out_fast_cli_extended.txt` | Fast alternate solver (`satsolver_fast.py`) | Exact-CLI benchmark artifact | Current retained exact-CLI output snapshot for the fast alternate wrapper |
| `out_blaze_extended.txt` | Blaze legacy solver (`satsolver_blaze.py`) | Extended benchmark artifact | Historical comparison snapshot for the blaze variant |
| `out_blaze.txt` | Blaze legacy solver (`satsolver_blaze.py`) | Benchmark artifact | Older comparison output for the blaze variant |
| `out.txt` | Earlier main solver runs | Benchmark artifact | Historical output file kept for comparison history |
| `out_old.txt` | Earlier main solver runs | Benchmark artifact | Older retained benchmark snapshot |

## Quick Reading Guide

| If you want to know... | Read... |
| --- | --- |
| What should be submitted right now | `satsolver.py` and `benchmark_summary.md` |
| What the current retained benchmark numbers are | The “Current Retained Benchmark Results” table above |
| What the best recorded numbers are, even if the current artifact is slower | The “Historical Best Recorded Results” table above |
| What code actually does the solving | `satsolver_core.py` |
| What alternate exact-CLI solution still matters | `satsolver_fast.py` and `out_fast_cli_extended.txt` |
| What old alternate exists mostly for comparison | `satsolver_blaze.py` |
| What the benchmark artifacts mean | `benchmark_summary.md` plus the relevant `out*.txt` file |
