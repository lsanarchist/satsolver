# Autonomous Work Verdict

Purpose:
- Convert the current high-level solver verdict into actionable guidance for future autonomous cycles.
- Keep the agent focused on changes that are large enough to matter on the current benchmark family.

Status:
- Strategic guidance only.
- This is not itself a measured keep/reject experiment.
- All ideas here still need same-day benchmark validation before they are kept.

## Core Verdict

The next real gains probably will not come from more pure-Python hot-loop surgery.

Current evidence says:
- the main remaining cost is dense search-heavy UNSAT solving, not parser/output/import overhead,
- the dominant hot path is still original ternary clause traffic inside `propagate()`,
- once original ternary clauses leave the satisfied path, most of the work is relocation or unit propagation,
- conflict tails are comparatively small,
- clause-local and literal-local micro-tricks are weak because the hotspot traffic is diffuse rather than concentrated.

So the main optimization target is:
- reduce how often the solver has to do original-ternary relocation/unit work,
- not just make each visit a few percent cheaper in Python.

## Highest-Priority New Branches

### 1. Selective Clause Vivification

Why:
- This is the best direct way to cut original-clause traffic instead of merely polishing it.
- If vivification turns some original ternaries into binaries or units, or drops literals from heavily used clauses, it directly reduces the dominant workload.

Suggested narrow selector:
- original clauses of length `3..8` that were recently used as reasons or conflicts,
- learnt clauses with low LBD and recent activity/reuse,
- vivify at most once per simplification epoch unless clause quality improves again.

Budgeting rule:
- budget vivification by propagation-like work, watcher visits, or clause dereferences,
- not by wall clock and not by a naive fixed conflict interval.

Success criteria:
- same-day exact-CLI full-suite A/B must be positive,
- original ternary watch visits and/or reason traversals should materially fall on `large/test_6.cnf` and `special/hard.cnf`.

### 2. Real Inprocessing, Not More Root-Pure Tuning

Why:
- The remaining gap looks algorithmic, not cosmetic.
- Reducing clause count and strengthening the formula should help more than more threshold tuning on current lightweight presolve.

Suggested bundle:
- bounded variable elimination,
- subsumption,
- self-subsuming resolution,
- blocked clause elimination,
- top-level propagation to a touched-set fixpoint.

Implementation constraints:
- use touched variables only,
- reject eliminations that grow the clause set too much,
- skip very high-occurrence variables,
- keep a reconstruction stack for SAT model rebuilding.

Success criteria:
- measured clause-count reduction,
- lower watched-clause traffic on the hard cases,
- same-day exact-CLI full-suite A/B must stay positive.

### 3. Branching Policy Changes Without New Branch Data Structures

Why:
- Heap/frontier experiments already failed badly.
- That does not mean branching is finished; it means Python bookkeeping-heavy branch frontiers are the wrong vehicle.

What to try:
- keep the current linear max scan in `pick_branch_literal()`,
- add alternative score-update policies such as LRB or CHB,
- do not add heaps, mutable active sets, or branch frontiers.

Success criteria:
- same-day exact-CLI full-suite A/B,
- lower conflicts and/or lower average LBD on `large/test_6.cnf` and `special/hard.cnf`,
- no regression from Python bookkeeping overhead.

## Second-Tier Branches

These are real lanes, but below the three priorities above.

### Dynamic Restart Regimes

Try only as a distinct policy change, not as another constant tweak.

Examples:
- Glucose-style dynamic restart criteria,
- focused/stable alternation,
- target phases,
- classifier-gated restart modes.

Important:
- simple restart-base and decay nudges are already heavily mined and mostly dead.

### Chronological Backtracking Plus Stronger On-the-Fly Reason Simplification

This is promising but invasive.

Priority:
- below vivification, inprocessing, and same-scan branching-score changes.

### Light Probing / Hyper-Binary Resolution

Potential fit:
- the workload is ternary-heavy, so generating useful binaries could matter.

Warning:
- likely expensive in Python,
- should stay below vivification and BVE/BCE in priority.

## What To Stop Spending Time On

Treat these as mostly exhausted unless a future branch changes something materially larger than the item itself:
- more `propagate()` branch-order micro-tuning,
- watcher payload reshaping,
- per-clause mutable blocker or scan-hint state,
- branch heaps or active frontiers,
- schedule-only clause-database tweaks,
- more root-pure threshold tuning,
- wrapper/import cleanup,
- tiny builtin/local-binding cleanup,
- container substitutions that keep the same search work,
- hotspot-only branch-shape rewrites without broad-suite proof.

## Acceptance Criteria For Future Autonomous Cycles

For any branch inspired by this verdict:

1. Require same-day exact-CLI full-suite A/B against the retained baseline.
2. Require a concrete explanation of whether the branch reduced:
   - original ternary watch visits,
   - original ternary relocation/unit work,
   - or reason traversals
   on `large/test_6.cnf` and `special/hard.cnf`.
3. Do not trust hotspot-only wins.
4. Do not keep changes that only move Python work around without reducing solver work.

## Practical Summary

If opening three autonomous branches next, prefer:

1. `vivify_selected_clauses`
2. `bve_bce_touched_root`
3. `lrb_scores_same_scan`

If a branch does not materially reduce original-ternary traffic on the hard cases, it is probably not the right next direction.
