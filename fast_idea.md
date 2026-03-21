I’ll answer as a SAT-solver engineer who has spent too much time profiling CDCL in Python.

**TL;DR**: In pure Python, the fastest solver is usually not a fancy new algorithm. It is a *very tight* MiniSat/Glucose-style CDCL engine: two-watched literals, VSIDS-style branching, phase saving, restarts, 1-UIP clause learning, LBD-based learnt-clause management, and a propagation loop engineered to avoid Python overhead. In your current repo, the strongest submission path is exactly that shape, wrapped in a lean exact-CLI layer over a shared core.  

1. **Write one good *iterative* CDCL core first.**
   Do not start from recursive DPLL if you care about speed. Build an explicit solver state with flat arrays/lists for assignments, reasons, levels, activities, saved phases, the trail, trail limits, and watch lists. Modern practical solvers are CDCL-based, and Glucose explicitly builds on MiniSat’s internal architecture with VSIDS and the two-watched-literal scheme. 

2. **Assume `propagate()` is your real program. Optimize that first.**
   The durable wins in this repo came from precomputed per-literal lookup tables, a direct per-literal truth cache, inlined unit assignment for already-known-unassigned literals, a ternary-clause fast path, and an immutable cached `ternary` flag on clauses. That worked especially well because the local workload is heavily 3-SAT: `27,414 / 32,783` clauses, or `83.62%`, are length 3. If your instances look like that, specializing binary and ternary propagation is worth more than almost anything else.    

3. **Keep conflict analysis lean, not clever.**
   Use 1-UIP learning, compute LBD once when the learnt clause is formed, keep binary/ternary reason fast paths, use tokenized `seen` marks instead of clearing arrays every conflict, and backtrack by slicing the trail tail once instead of popping in a loop. In this repo, tokenized `seen` and slice-delete backtracking were both clear keeps on exact-CLI A/B runs. Glucose’s whole design is built around LBD as a learnt-clause quality measure, and that still maps well to Python as long as the implementation stays simple.   

4. **Use LBD + activity for clause database reduction, and be conservative with policy tweaks.**
   Keeping binaries and very low-LBD clauses longer is standard practice in modern solvers. But in Python, many “obvious” tweaks to reduction policy can be disastrous. In this repo, reducing sooner, reducing later, sorting shorter clauses earlier, normalizing activity by clause length, or removing clause-activity bumping all regressed badly on exact-CLI hotspot slices or full repeat-aware suites. That is a strong hint to avoid touching the classifier until the rest of the engine is already very good.   

5. **Treat parsing, presolve, and wrapper overhead as part of solver performance.**
   If the judge runs `python satsolver.py input.cnf output.txt`, the wrapper path matters. The current best-known config in the repo uses an exact-CLI wrapper over `satsolver_core.py`, an import-gated main wrapper, a byte-level DIMACS parse/write path, structural XOR/pigeonhole UNSAT checks, and a very narrow root-pure presolve gate only for low-density all-3-SAT formulas. Preprocessing is hugely important in SAT in general, but in pure Python heavy preprocessing often costs more than it saves unless it is very cheap and very carefully gated. ([fmv.jku.at][1])   

6. **Benchmark the exact command, not just the core.**
   This repo’s history shows a repeated pattern: a change looks great on one hotspot slice, then loses on the repeat-aware exact-CLI full suite. So validate output semantics, benchmark the real command line, and compare baseline vs candidate on the same day. The repo’s benchmark harness and checker exist for exactly that reason.  

A compact state layout that usually works well in CPython looks like this:

```python
values[var]        # -1 false, 0 unassigned, +1 true
level[var]         # decision level
reason[var]        # clause id or sentinel for decision
activity[var]      # VSIDS score
saved_phase[var]   # preferred polarity

trail              # assigned literals in order
trail_limits       # index where each decision level starts
qhead              # propagation queue head

lit_value[idx]     # cached truth value of literal
lit_var[idx]       # literal -> variable
lit_sign[idx]      # literal -> sign
binary_watches[idx]
watches[idx]       # watched non-binary clauses

seen[var]
seen_token
```

And your clause object should stay tiny. A manual slotted object with immutable shape metadata is the sweet spot: literals, learnt flag, LBD, activity, deleted flag, and maybe one immutable `ternary` bit. Much broader side metadata tended to lose in this repo. 

The biggest trap is chasing “cute” micro-optimizations instead of removing real work. In this repo, per-visit `len(lits)` caching, local `append/pop` aliasing, fixed-size watched-clause paths beyond ternary, schedule-only `reduce_database()` tweaks, and export-surface trimming all regressed. The pattern is simple: if the change adds mutable side state, perturbs traversal order, or only makes `cProfile` look prettier without reducing clause visits, it probably loses in CPython.     

So the shortest honest answer is:

* **Algorithm**: CDCL.
* **Hot path**: binary + ternary-specialized watched propagation.
* **Heuristics**: VSIDS, phase saving, Luby-style restarts, LBD.
* **Data layout**: flat lists, ints, tiny slotted clauses, cached literal truth.
* **Conflict path**: 1-UIP, cheap minimization, tokenized marks, slice backtrack.
* **Engineering**: lean CLI wrapper, exact-CLI benchmarking, checker-backed validation.
* **Last 5%**: only then try a *very narrow* `multiprocessing` portfolio. The current repo keeps one such density-limited portfolio, but broad portfolioing was often a loss because process overhead is real. 

The fastest way to get there is not “invent a new heuristic”. It is: build a compact CDCL core, make `propagate()` brutally cheap, and refuse to keep any optimization that does not win on the real command-line benchmark.

[1]: https://fmv.jku.at/papers/BiereJarvisaloKiesl-SAT-Handbook-2021-Preprocessing-Chapter-Manuscript.pdf "Preprocessing in SAT Solving"
