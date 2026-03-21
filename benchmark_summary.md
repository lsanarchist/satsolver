# Benchmark Summary

Updated: `2026-03-21T01:08:55+01:00`

Best-known submission configuration:
- `satsolver.py`
- CDCL core with watched literals, VSIDS-style activity, Luby restarts, clause database reduction
- Structural UNSAT presolvers for pigeonhole cores and XOR contradictions
- Iterative root pure-literal presolve, but only when the root fixpoint reaches at least two assignments
- Precomputed per-literal lookup tables in the propagation hot path
- Per-literal truth-value cache updated on enqueue/backtrack and read directly in propagation
- Inlined assignment updates for already-known-unassigned binary and watched-clause units inside `propagate()`
- Ternary-clause fast path inside watched-literal propagation
- Explicit `decision_level` tracking and cached trail/watch-list bounds inside `propagate()`
- In-place learnt minimization and single-pass backtrack-level/LBD finalization in conflict analysis
- Binary/ternary reason fast paths inside one-hop `minimize_learnt()`
- Density-limited two-process standard-library portfolio for large SAT-like pure-3-SAT cases on multi-core POSIX systems, with `SATSOLVER_DISABLE_PORTFOLIO` as an escape hatch
- Parser hardening for misplaced clauses, repeated headers, and out-of-range literals
- `tools/checker.py` for SAT-format validation and tiny-UNSAT brute-force checks
- `benchmark_suite.py` now validates written outputs and reports solved-correctly counts
- `benchmark_suite.py --cli-script` can benchmark the exact required solver invocation path
- `benchmark_suite.py --repeat N` now records per-case samples and median representative totals for repeat-aware comparisons

Latest full-suite command:

```bash
python benchmark_suite.py satsolver out_extended.txt small medium large special satlib_subset satlib_more --bruteforce-var-limit 16
```

Repeat-aware benchmark commands:

```bash
python benchmark_suite.py satsolver out_extended.txt small medium large special satlib_subset satlib_more --bruteforce-var-limit 16 --repeat 2
python benchmark_suite.py satsolver out_cli_extended.txt small medium large special satlib_subset satlib_more --bruteforce-var-limit 16 --cli-script satsolver.py --repeat 2
```

Latest repeat-aware in-process 59-case snapshot:
- Instances attempted: `59`
- Solved correctly: `59`
- SAT solved: `28`
- UNSAT solved: `31`
- Errors: `0`
- Representative total runtime: `25.1541s`
- Measured total across both repeats: `50.3082s`
- Wall clock: `50.4568s`
- Worst-case representative runtime: `11.6988s` on `large/test_6.cnf`

Best repeat-aware exact-CLI 59-case snapshot:
- Instances attempted: `59`
- Solved correctly: `59`
- SAT solved: `28`
- UNSAT solved: `31`
- Errors: `0`
- Representative total runtime: `27.1974s`
- Measured total across both repeats: `54.3948s`
- Wall clock: `54.6329s`
- Worst-case representative runtime: `11.5797s` on `large/test_6.cnf`

Latest repeat-aware exact-CLI reruns this cycle:
- Rerun 1: `27.7868s` representative, `55.5737s` measured, `55.8209s` wall clock, `59/59` correct
- Rerun 2: `27.6136s` representative, `55.2273s` measured, `55.4582s` wall clock, `59/59` correct

Current alternate exact-CLI candidate (`satsolver_fast.py`):
- Historical best repeat-aware snapshot: `27.3829s` representative, `54.7658s` measured, `59/59` correct
- Same-day retained-wrapper rerun before the bytes-parser keep: `27.6459s` representative, `55.2917s` measured, `59/59` correct
- Same-day scratch bytes-parser branch before merge: `27.4523s` representative, `54.9045s` measured, `59/59` correct
- Refreshed merged artifact in `out_fast_cli_extended.txt`: `27.5074s` representative, `55.0148s` measured, `55.2459s` wall clock, `59/59` correct

Best single-run in-process validated 59-case snapshot:
- Instances attempted: `59`
- Solved correctly: `59`
- SAT solved: `28`
- UNSAT solved: `31`
- Errors: `0`
- Total runtime: `26.4178s`
- Mean runtime: `0.4478s`
- Median runtime: `0.0042s`
- Worst-case runtime: `12.5231s` on `large/test_6.cnf`

Best single-run exact-CLI validated 59-case snapshot:
- Command:
  `python benchmark_suite.py satsolver out_cli_extended.txt small medium large special satlib_subset satlib_more --bruteforce-var-limit 16 --cli-script satsolver.py`
- Instances attempted: `59`
- Solved correctly: `59`
- SAT solved: `28`
- UNSAT solved: `31`
- Errors: `0`
- Total runtime: `28.4550s`
- Mean runtime: `0.4823s`
- Median runtime: `0.0478s`
- Worst-case runtime: `12.1124s` on `large/test_6.cnf`

Latest cycle note:
- This cycle rejected applying the same byte-level DIMACS parse/write path to the main submission file `satsolver.py`.
- The early exact-CLI slices looked plausible: the SAT-heavy root-hit slice improved (`0.4960s -> 0.4718s`) and the mixed nine-case hotspot slice was effectively tied (`24.6647s -> 24.6994s`). But the real same-day repeat-aware exact-CLI 59-case suite regressed badly from `27.6153s` on the temp baseline to `29.3807s` on the candidate, both still `59/59` correct.
- So the main solver stays on the previous parser/output path, and the new boundary is clear: parser/read/write experimentation can pay off on alternate exact-CLI wrappers like `satsolver_fast.py`, but it should not be merged into `satsolver.py` without clearing a same-day repeat-aware full-suite gate.

Cumulative improvement since the first archived 59-case snapshot:
- Full suite: `50.2815s -> 26.4178s` (`-47.46%`)

Profiling note:
- `tools/profile_solver.py` has been repaired to track explicit `decision_level` correctly again, and it now exposes watch-path and learnt-shrink counters in addition to time/decision/conflict counts.
- Current profiling still points to watched-clause traversal plus downstream conflict-analysis as the most promising path: binary checks are tiny, deleted-watch skips are modest, and the dominant work on the hard UNSAT runs is specifically ternary relocation plus ternary unit propagation. The already-known-unassigned assignment handoff inside propagation has now been optimized and no longer looks like the next big win.
- The new probe-depth counters make the large-clause story narrower: average replacement scans stay fairly short on the hard UNSAT cases, so a future large-clause optimization needs to be more selective than a generic scan rewrite and should be checked against `large/test_8.cnf`, where scan failures run deeper and learnt clauses stay longer.
- The recent ternary branch tested after the profiler upgrade, eager relocation on already-satisfied ternary clauses, also regressed badly enough that future satisfied-skip work needs a stronger selector than “the other watch is already true”.
- Another watch-metadata branch tested after the profiler upgrade, encoded watch-slot payloads, also regressed; future propagation work should be wary of richer watcher-list payloads in pure Python unless they remove much more work than just watched-slot normalization.
- The newest propagation reject adds another boundary: avoiding watched-slot normalization unless relocation actually happens still lost (`27.8534s -> 28.3930s` on the serial five-case slice), so future watch-path work should be skeptical of branchier “lazy normalization” ideas that do not remove larger chunks of traversal work.
- The newest profiler upgrade explains that reject more precisely: watched-slot normalization is frequent, but only about `20%..27%` of those normalizations are immediately followed by a satisfied skip on the main hotspots. The majority still feed relocation/unit/conflict work, and ternary clauses dominate the normalization counts, so future propagation work should target larger ternary traversal chunks instead of just trying to dodge the swap.
- The latest reject adds one more caution flag for propagation micro-work: a tiny per-visit `len(lits)` cache inside `propagate()` still regressed the serial five-case slice (`27.5712s -> 29.1215s`), so future work should not assume every visible `len()` hotspot in `cProfile` translates into a real end-to-end win.
- The latest keep materially reduced backtrack overhead: on `large/test_6.cnf`, the new reverse-index-plus-tail-delete `backtrack()` path kept the same conflict count while cutting `backtrack()` `tottime` from `2.189s` to `0.558s` and `pop()` calls from `10,107,994` to `6,745,603`. So future work should move back toward watched-clause traversal and conflict-analysis again rather than more backtrack micro-work.
- The newest profiler upgrade narrows that further by clause family: on the dense pure-3-SAT bottlenecks, active ternary watch traffic is about `95%..97%` original-clause work, while the active large-clause watch path is entirely learnt-clause work on those instances. `analyze()` and one-hop minimization also lean strongly toward original-clause reasons (`~80%..87%` problem-clause in `analyze()`, `~62%..75%` in minimization checks). That makes broad learnt-retention/layout changes look less central to the main UNSAT hotspots than raw original-clause ternary propagation or reason-traversal speedups.
- The newest large-watch size split makes the learnt-clause side of that story more concrete: active large-clause traffic is not dominated by 4-literal clauses. On the main hotspot cases, length `4` accounts for only about `24.7%..32.9%` of large-watch visits, length `5..9` is usually the biggest bucket at `34.3%..45.3%`, and length `10+` still accounts for `25.2%..40.4%`. So a narrow 4-literal fast path is unlikely to cover most of the remaining learnt-large workload by itself.
- The newest large-scan reject tightens that boundary again: even with average large-clause probe depth only around `2.3..3.4`, manually unrolling the first replacement candidates in Python still regressed the five-case serial hotspot slice in both forward and reverse order while keeping identical conflict counts. So “the first few scan steps are common” is not enough, by itself, to justify a manual large-scan unroll.
- The newest success-depth buckets make that boundary more precise: the first two probe steps really do dominate successful large relocations on the hard UNSAT cases (`69.75%..75.59%` on `large/test_6.cnf`, `special/hard.cnf`, and `medium/test_4.cnf`), but `large/test_8.cnf` still has a materially fatter `5+` tail at `20.30%`. So future learnt-large work should treat “head-heavy” as a real signal, but not as sufficient justification for another Python scan-head micro-unroll.
- The newest root-pure reject tightens the presolve warning too: even a stronger classifier piggybacking on the same fixpoint, using removed-clause ratio in addition to assignment count, can still win the pure-hit and mixed exact-CLI slices yet fail badly on the real repeat-aware exact-CLI 59-case suite (`31.4387s`). So future root-pure tuning still needs a stronger full-suite classifier than assignment count or removed-clause ratio alone.
- The recent phase-policy resweep also says the parallelism story has not fundamentally changed after the latest solver-core wins: `phase_bias` remains a narrow `large/test_8` specialist, `all_true` is too close to default to justify another worker, and `all_false` is still unstable.
- The upgraded reason-bucket counters narrow the conflict-analysis target further: within the old `2..3` bucket, binary reasons are negligible and ternary reasons dominate. On `large/test_6.cnf`, only `1,248 / 1,057,846` traversed reasons are size `2`, while `930,068` are size `3`; removals are `12,293` via size `2`, `100,492` via size `3`, `27,850` via `4..9`, and only `4,012` via `10+`. `special/hard.cnf` and `medium/test_4.cnf` show the same shape, so any future conflict-analysis fast path should be ternary-first, with `4..9` as a secondary target and `10+` still treated skeptically.
- The one minimization branch tested after the profiler upgrade, recursive redundancy traversal, regressed badly enough that future minimization work should be cheaper or more selective than that approach.
- The latest branch adds a useful nuance: a narrow binary/ternary fast path inside `minimize_learnt()` appears worthwhile, but a broader manual unroll of `analyze()` plus `minimize_learnt()` regressed badly. Future conflict-analysis tuning should stay selective instead of trying to unroll the whole reason-traversal path in Python.
- The newest reject adds one more boundary: even a much narrower ternary-only `analyze()` rewrite can still lose if it mainly reshapes the clause loop rather than removing enough work. The profiled search counts stayed identical, so this specific branch was just extra overhead.
- The newest reject tightens that boundary once more: even an original-clause-only ternary fast path inside `analyze()` did not clear the bar. It helped a few per-case timings, but the focused forward/reverse average still regressed slightly while keeping the same decisions/conflicts/processed-literal counts on the main profiled cases, so future conflict-analysis work still needs a stronger simplification than manually spelling out the three-literal case.
- The newest keep adds the complementary positive case: removing a very high-frequency helper call inside `analyze()` can pay off even when clause-shape unrolling does not. `cProfile` had `bump_var_activity()` at `0.394s` on `large/test_6.cnf`, `0.286s` on `special/hard.cnf`, and `0.117s` on `large/test_8.cnf`, and inlining just that call path produced a same-search exact-CLI hotspot improvement while keeping the conflict-analysis structure intact.
- The latest keep also reinforces a measurement rule: when the claimed gain is around 1% or less, same-day exact-CLI confirmation matters. The in-process repeat-aware suite improved, but the exact-CLI repeat-aware reruns did not beat the historical best.
- This cycle adds a more general version of that rule: if the module-mode and exact-CLI full-suite reruns disagree, use same-search hotspot A/B and exact-CLI results to break the tie, and record the mixed outcome explicitly instead of pretending the signal is cleaner than it is.
- The newest reject sharpens the branching side of that same lesson: even a modest local-alias cleanup in `pick_branch_literal()` can look positive on both hotspot slices and still lose the repeat-aware exact-CLI suite. So future branching work still needs a stronger structural win than loop-local caching or attribute-hoisting alone.
- The newest reject extends that lesson to `solve()` bookkeeping too: even trimming three very frequent helper calls around decay and reduction can still wash out to a near-tie on the exact-CLI hotspot slice. Future helper-boundary work in the outer loop needs a cleaner signal than that before it earns a full-suite run.
- The newest reject closes another clause-local-state direction on the propagation side: fixed-order problem ternary clauses plus watched-position side arrays preserved exact conflict counts on the five-case hotspot slice and still regressed in both orders. So future original-ternary work should be skeptical of replacing `clause.lits` mutation with extra watched-position side state unless it removes substantially more work than this branch did.
- The newest cross-solver comparison closes another tempting portfolio lead too: on the current five-case hotspot slice, the retained solver now beats `satsolver_blaze.py` clearly in both forward and reverse order, with blaze only stealing one forward `large/test_10.cnf` run. So the old sibling-solver speed note is stale as a current alternate-worker lead; future portfolio work needs a more materially different search identity than simply reviving `satsolver_blaze.py`.
- The immediately previous profiler split also says active watcher batches containing problem ternary clauses are frequently mixed with other families rather than already homogeneous: mixed-share is `47.21%..70.78%` on the four main hotspots, with learnt-large traffic as the dominant co-resident family. So true physical watch-list separation is still not ruled out on homogeneity grounds alone, even though branch-hoisting and clause-local side-state ideas remain rejected.
- The newest workflow keep tightens measurement hygiene in the same area: forward/reverse hotspot A/B is now a first-class tool instead of a pile of ad hoc shell snippets, so future small candidate branches should use `tools/hotspot_compare.py` before spending full-suite benchmark time.
- The latest rejected branching branch adds another rule: `pick_branch_literal()` may look tempting in `cProfile`, but cheap best-variable hint caches can still lose even when they preserve the exact same decisions/conflicts on the hotspot cases. If branching is revisited again, it needs a more substantive design than local memoization.
- The newest keep adds a second positive pattern on the conflict-analysis side: token-scoped state can sometimes be left stale safely. `analyze()` was already using `seen_token` for membership tests, so removing the touched-list cleanup loop produced a cleaner win than several earlier clause-shape rewrites. Future bookkeeping work should prefer deleting redundant cleanup passes outright when token scoping already provides correctness.
- The latest `maybe.md` parallelism revisit adds a caution flag on portfolio plumbing: even when a raw-`fork` rewrite makes the one gated case faster, that does not automatically translate into a better same-day exact-CLI suite. Future portfolio work should demand a broad exact-CLI win, not just a cleaner `large/test_8.cnf` microbenchmark.
- The newest alternate-worker sweep tightens that portfolio warning further: even with a clean density split between the SAT-like `large/test_8.cnf` family and the denser pure-3-SAT UNSAT family, simple worker variants built from local restart-base, decay, or fixed-phase changes still lost to the retained default on the dense cases. Future portfolio work needs a materially different alternate search identity than small local parameter moves.
- The newest inline-reason reject adds the corresponding warning on the conflict-analysis side: even a more structural-looking attempt to remove clause dereferences from the dominant original problem-reason path can still lose badly if it adds extra per-variable side state and propagation bookkeeping. Future reason-traversal work needs a stronger simplification story than “store the two other literals early and read them back later.”
- The newest relocation-outcome profiler upgrade sharpens the propagation side in the complementary direction: ternary relocation work is mostly not about moving watches onto already-satisfied literals. On the main hotspot cases, only about `13.5%..17.2%` of ternary relocations go to `TRUE` candidates, so future watched-ternary work should primarily target the much larger `UNASSIGNED`-candidate relocation path or a broader traversal simplification.
- The newest other-watch-state profiler upgrade tightens that boundary again: only about `1.5%..2.0%` of ternary relocations happen with the other watched literal already `FALSE`. So future propagation work should also stop treating “rescue the clause when the other watch is already false” as the main relocation story; the bulk path is ordinary `UNASSIGNED`/`UNASSIGNED` maintenance.
- The newest reject adds the same caution flag on conflict-analysis cleanup: even another helper-boundary removal inside `analyze()` can look mildly positive on the module hotspot slice and still lose clearly on the exact-CLI repeat-aware full suite. Future `analyze()` bookkeeping changes of this size still need same-day exact-CLI confirmation before they earn a keep.
- The newest propagation reject adds the same kind of warning on the watched tail: even when the profiler says units massively outnumber conflicts after failed ternary and large replacement scans, simply checking `UNASSIGNED` before conflict did not produce a stable exact-CLI win. The branch preserved exact search counts on the main profiled cases and still failed the stricter same-day repo-vs-baseline exact-CLI hotspot A/B, so future propagation work should remove bigger ternary traversal chunks than just swapping rare-tail branch order.
- The newest clause-ingest reject adds another caution flag on “structural” wins that only show up under the serial harness: raw signed phase-bias watch ordering for problem ternary clauses dramatically helped `large/test_8.cnf` and improved the serial five-case slice, but still lost badly on the actual exact-CLI hotspot slice by making `large/test_6.cnf` and `large/test_10.cnf` too much worse. Future clause-order heuristics need a much better classifier than raw phase bias alone.
- The newest propagation reject adds the same caution flag inside the watcher loop itself: even a dedicated early fast path for non-learnt ternary clauses still regressed the serial five-case slice overall, helping `large/test_6.cnf` but hurting the other main hotspot families. Future original-ternary work still needs to remove more real relocation/unit/conflict work than simply hoisting that family ahead of the general loop.
- The newest learnt-path reject extends the same warning to tiny conflict-path object-lifecycle cleanups: even removing the extra learnt-clause list copy in `add_learnt_clause()` split by order and regressed on average, so future helper-boundary work around learnt storage still needs a stronger structural story than “one less list copy”.
- The newest propagation reject adds an even stronger warning against naive side caches on the ternary path: a blocker-style “known satisfied literal” cache for original ternary clauses catastrophically regressed both the hard UNSAT cases and SAT-like `large/test_8.cnf`. Future original-ternary work should be skeptical of auxiliary mutable blocker state in pure Python unless it removes far more work than this did.
- The newest large-clause reject extends that warning to the learnt path too: a rotating scan-hint side cache for large clauses also regressed badly, so future large-scan work should be skeptical of per-clause mutable scan state in pure Python unless it has a much stronger story than “start scanning somewhere else next time.”
- The newest reject sharpens the same warning in a more structural direction: even replacing watched propagation for original ternary problem clauses with a static per-literal trigger network made the hotspot families much worse, especially `large/test_8.cnf`. Future original-ternary work should preserve more watched-literal selectivity than a blunt “visit every false-literal incidence” network does.
- The newest profiler upgrade adds an important complementary constraint: the remaining original-ternary workload is not dominated by a small handful of clauses. Coverage is effectively total on the hotspot cases, and the hottest single problem ternary clause still accounts for only about `0.16%..0.26%` of problem-ternary visits. That lowers the priority of clause-specific caches or ordering heuristics even further and points back toward broad hot-loop savings.
- The newest trigger-literal concentration upgrade closes the analogous door on the watch-list side too: trigger-literal coverage is also essentially total, and the hottest single trigger literal still accounts for only about `0.41%..0.67%` of problem-ternary visits on the main hotspot cases. That makes literal-specific watch-list tricks look much less promising than broad original-ternary hot-loop simplification.
- The newest reject sharpens the helper-boundary lesson inside `analyze()`: not every small call site follows the successful `bump_var_activity()` pattern. Inlining `bump_clause_activity()` preserved identical conflicts on every hotspot case and still regressed, so future conflict-analysis cleanup should target a materially larger or more structurally awkward cost than learnt-clause activity bumping.
- The newest branch-picker reject adds the same warning on the branching side in a more structural form: maintaining an explicit active prefix of unassigned variables did not just add bookkeeping overhead, it changed the search path badly on the very first dense gate. On `large/test_6.cnf`, the scratch baseline took `15.0435s` with `72,886` decisions and `59,201` conflicts, while the active-unassigned branch took `28.8075s` with `134,042` decisions and `108,066` conflicts. Future branching work should be skeptical of mutable active-set schemes unless they come with a much stronger invariance story than this.
- The newest branch-frontier profiler upgrade tightens that warning in a more specific way: on the main hotspot cases, average decision frontiers are still fairly large (`161.67..247.72` unassigned variables), but the winning best-activity variable is almost always unique (`9`, `13`, `15`, and `15` multiway ties total across tens of thousands of decisions) and zero-activity branch choices are absent. So future branching work should not target best-activity tie handling or zero-activity fallback first; if it is revisited at all, it needs a read-only scan reduction or some other stronger invariance story than mutable active-set maintenance.
- The newest satisfied-skip profiler split adds a complementary propagation boundary: only about `19.4%..26.4%` of problem-ternary trigger events end in an immediate satisfied skip on the main hotspot cases. So future original-ternary work should not focus mainly on branch ordering around the satisfied-skip exit; the majority of that workload still runs through relocation, unit propagation, or conflict handling.
- The newest ternary-outcome family split tightens that again: once a problem ternary clause reaches the non-satisfied path, conflicts are still under `1%` on all four hotspot cases, while relocation and unit propagation split the bulk roughly `51%..61%` versus `38%..48%`. So future original-ternary work should favor ideas that simplify or shorten the shared relocation/unit path rather than branches aimed mainly at the rare conflict tail.
- The newest scratch reject sharpens that same warning at the list-access level: manually unpacking ternary clauses into locals and writing them back explicitly inside `propagate()` still regressed the hotspot slice in both orders while preserving identical conflict counts on every case. So future original-ternary work should not assume that trimming a handful of `lits[...]` reads is already a meaningful structural simplification.
- The newest startup-path reject adds the corresponding warning on preprocessing cleanup: even a same-search branch that removes the duplicated clause-normalization pass from the serial path still lost slightly on the real exact-CLI full suite. So future front-loaded helper cleanups need a stronger suite-level story than “do one less normalization pass.”
- The newest trail-append profiler split explains the remaining `append()` / `pop()` hotspot more directly: on the four main hotspot cases, propagation trail appends are about `3.6x..4.1x` larger than `analyze()` learnt-literal appends, are themselves `91.5%..95.9%` ternary-unit work, and are still smaller than raw watch relocations by about `1.31x..2.03x`. So the visible list churn is still mainly watched-clause relocation plus original-ternary unit growth, not branch decisions or learnt-literal construction.
- The newest watcher-pop split closes the loop on the `pop()` side too: watcher-list pops now account for `98.43%..98.92%` of the explicitly counted pop traffic on the four main hotspots, leaving decision-level stack pops as noise by comparison. So future list-churn work should attack watched-clause removal/relocation directly, not trail-limit maintenance.
- The newest watcher-removal reject tightens that boundary one step further: even after proving watcher-list churn dominates the pop hotspot, a pop-return swap-removal rewrite still lost slightly on the two-order five-case average while preserving exact conflict counts. So future watcher-churn work still needs a larger structural reduction than shaving one list read off the current swap-pop pattern.
- The newest watcher-pop cause split sharpens the target inside that remaining churn: deleted-watch cleanup is only about `1.7%..2.5%` of watcher pops on the hotspot cases, while original problem-ternary relocations alone account for `56.4%..73.9%` and learnt large-clause relocations account for another `21.4%..38.3%`. So future watcher-churn work should target original-ternary relocation first, with learnt-large relocation as the secondary bucket, rather than treating deleted-watch cleanup as a co-equal target.
- The newest ternary normalized-outcome split closes one more tempting door on that same path: only about `31.2%..33.7%` of problem-ternary relocations and `27.1%..29.8%` of problem-ternary units happen after watched-slot normalization. Even problem-ternary conflicts, which are more normalization-heavy at `47.5%..48.0%`, are still under `1%` of the non-satisfied original-ternary path. So future watch-order or swap-avoidance ideas would only touch a minority of the dominant relocation/unit workload.
- The newest watch-batch family-mix split adds an important nuance to that propagation picture: batches containing problem ternary clauses are mixed much more often than the global family totals alone suggest, mostly with learnt-large watchers. So a true physical watch-list split is not ruled out on “the lists are already homogeneous anyway” grounds, but it still needs to be materially different from the already-rejected branch-hoist and per-clause-side-state ideas.
- The newest physical split-list reject closes much of that remaining loophole too: simply moving original problem-ternary clauses into their own watch lists and traversing them separately changed the search path badly enough to lose hard on `large/test_6.cnf` and `large/test_8.cnf`, even while helping `special/hard.cnf`. So future split-list work would need a much stronger semantics-preservation story than “physically separate the lists because batches are mixed.”
- The newest alternate-file keep adds a useful exact-CLI counterexample on the preprocessing side: a lean wrapper that simply removes the root pure-literal presolve from the current solver core can beat the current same-day exact-CLI full-suite run by `3.12%` and land `27.3829s` repeat-aware, even though the hotspot serial slice is only near-tied. So root-pure policy is still one of the few remaining levers that can move real submission-path runtime without another deep propagation rewrite.
- The newest exact-CLI wrapper reject closes another easy-looking door on the submission path: removing the post-solve `model_satisfies(...)` self-check from `satsolver_fast.py` only removes about `0.0053s` total across the entire current SAT benchmark corpus, so it is not a meaningful speed lever and not worth weakening the wrapper's internal safety.
- The newest parser-gating reject narrows the root-pure story further on the alternate submission path: even when first-round pure counts are collected during parsing and used as a cheap gate, reintroducing iterative root-pure preprocessing into `satsolver_fast.py` still comes out as a root-hit near-tie and a mixed-slice near-tie. So future exact-CLI root-pure work needs something materially stronger than “run it only when first-round pures are already visible.”
- The newest alternate-file reject adds the complementary startup lesson: even though the wrapper version imports the full main solver module, replacing it with a standalone no-root-pure copy is worse on the exact-CLI root-hit SAT slice. So “avoid the wrapper import” is not a free win; script size and parse/load cost still matter on the submission path.

Workload note:
- `27,414 / 32,783` benchmark clauses are length 3 (`83.62%`), which justifies continued focus on ternary-specialized propagation/data layout.

Current bottlenecks:
- `large/test_6.cnf`: `11.8684s`
- `special/hard.cnf`: `7.7563s`
- `medium/test_4.cnf`: `1.6973s`
- `large/test_10.cnf`: `1.6261s`
- `medium/test_3.cnf`: `0.6503s`
