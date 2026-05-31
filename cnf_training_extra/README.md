# Extra CNF training pack for satsolver

This pack contains 158 additional plain DIMACS `.cnf` files in `extra_cnf/`.
They are intentionally stored in one flat directory because this repository's `benchmark_suite.py`
uses `Path(folder).glob("*.cnf")` and does not recurse into nested folders.

## How to use inside the SAT solver repo

Copy `extra_cnf/` into the repository root, then run:

```bash
python benchmark_suite.py satsolver /tmp/bench_extra.txt extra_cnf --bruteforce-var-limit 16 --cli-script satsolver.py
```

For a quick smoke subset:

```bash
python satsolver.py extra_cnf/horn_chain_len32_unsat.cnf /tmp/out.txt
python tools/checker.py extra_cnf/horn_chain_len32_unsat.cnf /tmp/out.txt --bruteforce-var-limit 16
```

## Categories included

- `planted_random_3sat`: known-SAT near-threshold random 3-SAT generated from hidden assignments.
- `exact_small_random_3sat`: n <= 16 random 3-SAT with status brute-force checked during generation.
- `pigeonhole_unsat`: classic pigeonhole UNSAT encodings.
- `graph_coloring`: planted 3-colorable graphs plus unsatisfiable complete-graph cases.
- `nqueens`: SAT and UNSAT N-queens encodings.
- `xor_parity_cnf`: XOR/parity systems translated to CNF, including contradictory systems.
- `horn_implication`: Horn/unit-propagation chains.
- `cardinality_exactly_one`: pairwise exactly-one constraints, SAT and deliberately UNSAT variants.
- `equivalence_chain`: binary implication/equivalence chains.

See `manifest.csv` for expected status, variable count, clause count, and notes per file.
