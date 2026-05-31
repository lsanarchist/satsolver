# formulae_like_02

Synthetic DIMACS benchmark set shaped like the LPI assignment data set.

- `small/`: 10 formulas, 10-50 variables, 20-200 clauses
- `medium/`: 10 formulas, 50-200 variables, 200-1000 clauses
- `large/`: 10 formulas, 200-500 variables, 1000-2000 clauses
- `special/`: 5 structured formulas within the assignment hard limits

Variant index: `2`
Seed base: `20280601`
Generated with `python tools/generate_formulae_like_variants.py` using only the Python standard library.
Expected SAT/UNSAT labels are recorded in `MANIFEST.tsv` and as DIMACS comments.
