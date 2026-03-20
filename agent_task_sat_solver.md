# Agent Task: SAT Solver for LPI Assignment 02

## Source
This task is based on the LPI assignment page: **SAT Competition**

Source URL: `https://kurzy.kpi.fei.tuke.sk/lpi/assignments/02.html`

## Objective
Implement a SAT solver in **Python** that:
- reads a formula in **DIMACS CNF** format,
- decides whether the formula is satisfiable,
- writes `SAT` and a full model if satisfiable,
- writes `UNSAT` otherwise,
- is efficient enough to handle instances up to **500 variables** and **2000 clauses** within about **60 seconds per test**.
## Required program interface
The program must be runnable from the command line exactly as:

```bash
python satsolver.py input.cnf output.txt
```

Behavior:
- read the input file from the **first** command-line argument,
- write the result to the output file given as the **second** command-line argument.

## Required deliverables
The final submission must contain:
- `satsolver.py`

## Constraints
### Allowed
- Any self-implemented SAT approach, for example:
  - DPLL
  - CDCL
  - backtracking
  - heuristics
  - watched literals
  - clause learning
- Any custom optimizations
- Python **standard library only**

### Forbidden
- External SAT libraries
- Ready-made solvers such as MiniSAT, PySAT, Z3, etc.
- Calling external programs
- Any non-standard-library Python packages

**Important:** violating these rules means **0 points**.

## Input format: DIMACS CNF
The input file uses the standard DIMACS CNF format.

General structure:

```text
c comment
p cnf <num_vars> <num_clauses>
<clause1>
<clause2>
...
```

Rules:
- lines starting with `c` are comments,
- the problem line has the form `p cnf <num_vars> <num_clauses>`,
- literals are integers,
- positive integer `i` means variable `x_i`,
- negative integer `-i` means negated variable `¬x_i`,
- every clause ends with `0`,
- variables are numbered from `1` to `num_vars`.

Example input:

```text
c Example
p cnf 3 2
1 -3 0
2 3 -1 0
```

This represents:

```text
(x1 ∨ ¬x3) ∧ (x2 ∨ x3 ∨ ¬x1)
```

## Output format
### If the formula is unsatisfiable
Write exactly:

```text
UNSAT
```

### If the formula is satisfiable
Write:

```text
SAT
<l1> <l2> ... <ln> 0
```

Where:
- each `li` is an integer,
- positive integer means the variable is assigned **TRUE**,
- negative integer means the variable is assigned **FALSE**,
- **every variable from `1` to `num_vars` must be assigned**,
- literal order is arbitrary,
- the model line must end with `0`.

Example SAT output:

```text
SAT
1 -2 3 0
```

## Correctness requirements
The evaluation checks:
- correct decision: `SAT` vs `UNSAT`,
- correct model when SAT:
  - every clause must be satisfied,
  - every variable must have a value.

**Incorrect output format means the test fails.**

## Dataset and evaluation conditions
The evaluation dataset contains **35 formulas** in DIMACS format across 4 categories:
- **10 small tests**: 10–50 variables, 20–200 clauses
- **10 medium tests**: 50–200 variables, 200–1000 clauses
- **10 large tests**: 200–500 variables, 1000–2000 clauses
- **5 special tests**: varied structures and difficulty

A sample dataset (`formulae.zip`) is provided on the assignment page for testing and debugging. Final grading uses a **different** hidden test set released only after submissions.

## Performance target
Your solver should handle:
- up to **500 variables**,
- up to **2000 clauses**,
- with a **60 second** limit per test.

Brute force is not sufficient.


## Scoring
The assignment page states that the solver is worth **15 points** and lists the following criteria:
- Small tests (correctness): 2 points
- Medium tests (correctness): 2 points
- Large tests (correctness): 3 points
- Efficiency (runtime): 3 points

The page also lists a **bonus up to +5 points** for advanced techniques and above-standard performance, and separately states **"Spolu: 15 bodov"**. Keep the scoring section in mind as written on the page, but treat correctness and efficiency as the main priorities.

The page further states that the **top 3 solutions** receive the exam.

A ranking will be published based on:
- number of solved tests,
- total runtime.


## Definition of done
The task is complete only if all of the following are true:
1. A file named `satsolver.py` exists.
2. It runs exactly as:
   ```bash
   python satsolver.py input.cnf output.txt
   ```
3. It parses valid DIMACS CNF input, including comments and the `p cnf` header.
4. It writes either:
   - `UNSAT`, or
   - `SAT` followed by a complete model ending with `0`.
5. For SAT instances, the produced model assigns **all** variables `1..num_vars`.
6. The produced model actually satisfies every clause.
7. The implementation uses only the Python standard library.
8. The implementation does **not** invoke any external solver or package.
9. The solver is reasonably optimized for the target problem sizes.

## Recommended implementation direction (not mandated by the assignment)
A practical path for the agent:
1. Implement a robust DIMACS parser.
2. Implement a correct baseline DPLL solver first.
3. Add fast unit propagation.
4. Add a branching heuristic (for example, choose a variable occurring often in unsatisfied clauses).
5. Ensure the final assignment is complete even for variables not explicitly forced during search.
6. Add optimizations only after correctness is stable.
7. Build a small validator for the produced model to catch formatting or logic errors before writing output.

## Suggested self-checks before submission
- SAT instance produces a valid satisfying assignment.
- UNSAT instance produces exactly `UNSAT`.
- Output contains no extra text.
- Every clause in the DIMACS file ends with `0` and is parsed correctly.
- Variables missing from the partial search assignment are filled in before output.
- Runtime is acceptable on medium and large test files.

## Minimal execution examples
```bash
python satsolver.py sample.cnf result.txt
cat result.txt
```

## Agent instruction
Implement the solver and optimize it within the assignment constraints. Prioritize:
1. strict output correctness,
2. standard-library-only compliance,
3. runtime improvements that remain self-implemented.
