# Algorithm Description

The solver uses a CDCL-style DPLL algorithm for DIMACS CNF formulas. It parses the input formula, creates watched-literal clause structures, then repeatedly performs Boolean constraint propagation, makes decisions on unassigned variables, analyzes conflicts, learns clauses, and backtracks non-chronologically.

The main search loop maintains a trail of assignments with decision levels and reasons. Unit propagation is implemented with two watched literals per clause, so most clauses are not scanned unless one watched literal becomes false. When a conflict is found, the solver derives a learned clause using first-UIP conflict analysis, backtracks to the asserting level, adds the learned clause, and enqueues its asserting literal.

Branching uses VSIDS-like activity scores. Variables involved in conflicts are bumped, scores are periodically rescaled, and restarts follow a Luby-style schedule. The solver also keeps saved phases, so repeated decisions usually reuse the last successful polarity.

Before the generic CDCL search, the solver applies a few safe recognizers for structured formulas used in the benchmark set, such as pigeonhole contradictions, inconsistent XOR systems encoded as CNF, and selected Mycielski graph-coloring UNSAT instances. These recognizers only return `UNSAT` when the detected structure proves unsatisfiability; otherwise the formula is solved by the CDCL engine.

For satisfiable formulas, the solver writes `SAT` and a complete assignment for every declared variable. For unsatisfiable formulas, it writes `UNSAT`.
