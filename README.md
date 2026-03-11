# satsolver

A fast, olympiad-ready **CDCL SAT solver** written in pure Python — inspired by MiniSAT.

## Algorithm

| Feature | Description |
|---|---|
| **Core** | Conflict-Driven Clause Learning (CDCL) |
| **Propagation** | Two-watched-literal (2WL) Boolean Constraint Propagation |
| **Decisions** | VSIDS (Variable State Independent Decaying Sum) |
| **Backtracking** | Non-chronological (back-jumping) |
| **Restarts** | Luby-sequence restarts |
| **Clause management** | Periodic deletion of low-activity learnt clauses |
| **Minimization** | On-the-fly self-subsumption of learnt clauses |
| **Input** | DIMACS CNF format |

## Usage

### Python API

```python
from satsolver import Solver

s = Solver()
# Clauses are lists of DIMACS-style integers (1-based; negative = negated)
s.add_clause([1, -3, 4])
s.add_clause([-1, 2])
s.add_clause([-2, -4])

if s.solve():
    print("SAT", s.model())   # {var: bool, ...}
else:
    print("UNSAT")
```

### DIMACS CNF file (command-line)

```
python satsolver.py problem.cnf
```

Output follows the SAT competition standard:

```
s SATISFIABLE
v 1 -2 3 0
```

or

```
s UNSATISFIABLE
```

Exit codes: **10** = SAT, **20** = UNSAT, **1** = error.

### `solve_dimacs` helper

```python
from satsolver import solve_dimacs

sat, model = solve_dimacs(open("problem.cnf").read())
```

## Running the tests

```
pip install pytest
pytest test_satsolver.py -v
```

## Example — Pigeonhole PHP(3,2)

```python
from satsolver import Solver

# 3 pigeons, 2 holes — UNSAT
def var(pigeon, hole): return (pigeon - 1) * 2 + hole

s = Solver()
for i in range(1, 4):                        # each pigeon in some hole
    s.add_clause([var(i, 1), var(i, 2)])
for j in range(1, 3):                        # no two pigeons share a hole
    for i1 in range(1, 4):
        for i2 in range(i1 + 1, 4):
            s.add_clause([-var(i1, j), -var(i2, j)])

print(s.solve())   # False
```
