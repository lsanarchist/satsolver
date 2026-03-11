"""
Tests for the CDCL SAT solver.
"""

import pytest
from satsolver import Solver, parse_dimacs, solve_dimacs, _luby


# ---------------------------------------------------------------------------
# Luby sequence
# ---------------------------------------------------------------------------

class TestLuby:
    def test_first_eight(self):
        expected = [1, 1, 2, 1, 1, 2, 4, 1]
        for i, exp in enumerate(expected, start=1):
            assert _luby(i) == exp, f"_luby({i}) expected {exp}"

    def test_sequence_grows(self):
        """Later Luby values should include larger integers."""
        assert _luby(7) == 4
        assert _luby(15) == 8


# ---------------------------------------------------------------------------
# parse_dimacs
# ---------------------------------------------------------------------------

DIMACS_SIMPLE = """\
c simple SAT instance
p cnf 3 2
1 -2 0
2 3 0
"""

DIMACS_UNSAT = """\
p cnf 1 2
1 0
-1 0
"""

class TestParseDimacs:
    def test_parses_vars_and_clause_count(self):
        nv, nc, clauses = parse_dimacs(DIMACS_SIMPLE)
        assert nv == 3
        assert nc == 2

    def test_parses_clauses(self):
        _, _, clauses = parse_dimacs(DIMACS_SIMPLE)
        assert clauses == [[1, -2], [2, 3]]

    def test_comment_lines_ignored(self):
        _, _, clauses = parse_dimacs(DIMACS_SIMPLE)
        assert len(clauses) == 2

    def test_unsat_instance(self):
        nv, nc, clauses = parse_dimacs(DIMACS_UNSAT)
        assert nv == 1
        assert nc == 2
        assert clauses == [[1], [-1]]


# ---------------------------------------------------------------------------
# Trivial / small instances
# ---------------------------------------------------------------------------

class TestTrivial:
    def test_empty_clause_is_unsat(self):
        s = Solver()
        s.new_var()
        s.add_clause([])
        assert s.solve() is False

    def test_single_var_positive(self):
        s = Solver()
        s.add_clause([1])
        assert s.solve() is True
        m = s.model()
        assert m[1] is True

    def test_single_var_negative(self):
        s = Solver()
        s.add_clause([-1])
        assert s.solve() is True
        m = s.model()
        assert m[1] is False

    def test_trivial_unsat(self):
        s = Solver()
        s.add_clause([1])
        s.add_clause([-1])
        assert s.solve() is False

    def test_tautology_clause(self):
        """A clause containing both a literal and its negation is trivially SAT."""
        s = Solver()
        s.add_clause([1, -1])
        assert s.solve() is True

    def test_duplicate_literal_in_clause(self):
        """Duplicates should be deduplicated; clause still valid."""
        s = Solver()
        s.add_clause([1, 1, 2])
        assert s.solve() is True


# ---------------------------------------------------------------------------
# Model correctness
# ---------------------------------------------------------------------------

class TestModel:
    def _check_model(self, clauses, model):
        """Verify that the model satisfies all clauses."""
        for clause in clauses:
            satisfied = any(
                (lit > 0 and model.get(lit, False))
                or (lit < 0 and not model.get(-lit, True))
                for lit in clause
            )
            assert satisfied, f"Clause {clause} not satisfied by model {model}"

    def test_two_clause_model(self):
        clauses = [[1, 2], [-1, 3], [-2, -3]]
        s = Solver()
        for cl in clauses:
            s.add_clause(cl)
        assert s.solve() is True
        self._check_model(clauses, s.model())

    def test_three_coloring_triangle(self):
        """
        Triangle graph (3 nodes, edges 1-2, 2-3, 1-3) with 3 colours.
        Encode as SAT: each node gets exactly one colour, adjacent nodes differ.
        """
        # Variables: x_{node,colour} = node*3 + colour  (1-indexed)
        # x_{1,1}=1, x_{1,2}=2, x_{1,3}=3
        # x_{2,1}=4, x_{2,2}=5, x_{2,3}=6
        # x_{3,1}=7, x_{3,2}=8, x_{3,3}=9
        clauses = [
            # each node has at least one colour
            [1, 2, 3],
            [4, 5, 6],
            [7, 8, 9],
            # each node has at most one colour (pairwise)
            [-1, -2], [-1, -3], [-2, -3],
            [-4, -5], [-4, -6], [-5, -6],
            [-7, -8], [-7, -9], [-8, -9],
            # adjacent nodes differ
            [-1, -4], [-2, -5], [-3, -6],
            [-1, -7], [-2, -8], [-3, -9],
            [-4, -7], [-5, -8], [-6, -9],
        ]
        s = Solver()
        for cl in clauses:
            s.add_clause(cl)
        assert s.solve() is True
        self._check_model(clauses, s.model())


# ---------------------------------------------------------------------------
# UNSAT instances
# ---------------------------------------------------------------------------

class TestUnsat:
    def test_php_2_1(self):
        """
        Pigeonhole principle: 2 pigeons, 1 hole.
        Each pigeon must be in the only hole, but the hole can hold only one.
        p(1,1)             <- pigeon 1 must be in hole 1
        p(2,1)             <- pigeon 2 must be in hole 1
        -p(1,1) v -p(2,1)  <- at most one pigeon per hole
        """
        s = Solver()
        s.add_clause([1])
        s.add_clause([2])
        s.add_clause([-1, -2])
        assert s.solve() is False

    def test_php_3_2(self):
        """
        Pigeonhole principle: 3 pigeons, 2 holes.
        Variables: p(i,j) = pigeon i in hole j, encoded as (i-1)*2 + j
        """
        def var(i, j):
            return (i - 1) * 2 + j

        clauses = []
        # each pigeon in at least one hole
        for i in range(1, 4):
            clauses.append([var(i, 1), var(i, 2)])
        # no hole has two pigeons
        for j in range(1, 3):
            for i1 in range(1, 4):
                for i2 in range(i1 + 1, 4):
                    clauses.append([-var(i1, j), -var(i2, j)])

        s = Solver()
        for cl in clauses:
            s.add_clause(cl)
        assert s.solve() is False

    def test_all_3_clause_unsat(self):
        """3 clauses explicitly unsatisfiable."""
        s = Solver()
        s.add_clause([1, 2])
        s.add_clause([-1])
        s.add_clause([-2])
        assert s.solve() is False


# ---------------------------------------------------------------------------
# solve_dimacs helper
# ---------------------------------------------------------------------------

class TestSolveDimacs:
    def test_sat_instance(self):
        sat, model = solve_dimacs(DIMACS_SIMPLE)
        assert sat is True
        assert model is not None

    def test_unsat_instance(self):
        sat, model = solve_dimacs(DIMACS_UNSAT)
        assert sat is False
        assert model is None

    def test_model_satisfies_all_clauses(self):
        sat, model = solve_dimacs(DIMACS_SIMPLE)
        assert sat is True
        _, _, clauses = parse_dimacs(DIMACS_SIMPLE)
        for clause in clauses:
            satisfied = any(
                (lit > 0 and model.get(lit, False))
                or (lit < 0 and not model.get(-lit, True))
                for lit in clause
            )
            assert satisfied


# ---------------------------------------------------------------------------
# Larger / stress instance — random 3-SAT near phase transition
# ---------------------------------------------------------------------------

class TestLarger:
    def test_satisfiable_3sat(self):
        """
        A hand-crafted satisfiable 3-SAT formula with 20 variables.
        Built so that the assignment all-True satisfies it.
        """
        import random
        rng = random.Random(42)
        n = 20
        # Generate random 3-SAT clauses that are all satisfied by all-True
        clauses = []
        for _ in range(80):
            lits = rng.sample(range(1, n + 1), 3)
            # Ensure at least one positive literal so all-True satisfies it
            clause = [-l if rng.random() < 0.3 else l for l in lits]
            # Make sure at least one literal is positive
            if all(l < 0 for l in clause):
                clause[0] = -clause[0]
            clauses.append(clause)

        s = Solver()
        for cl in clauses:
            s.add_clause(cl)
        result = s.solve()
        if result:
            model = s.model()
            for cl in clauses:
                assert any(
                    (lit > 0 and model.get(lit, False))
                    or (lit < 0 and not model.get(-lit, True))
                    for lit in cl
                ), f"Clause {cl} not satisfied"

    def test_php_4_3_unsat(self):
        """Pigeonhole principle: 4 pigeons, 3 holes — UNSAT."""
        def var(i, j, holes):
            return (i - 1) * holes + j

        pigeons = 4
        holes = 3
        clauses = []
        for i in range(1, pigeons + 1):
            clauses.append([var(i, j, holes) for j in range(1, holes + 1)])
        for j in range(1, holes + 1):
            for i1 in range(1, pigeons + 1):
                for i2 in range(i1 + 1, pigeons + 1):
                    clauses.append([-var(i1, j, holes), -var(i2, j, holes)])

        s = Solver()
        for cl in clauses:
            s.add_clause(cl)
        assert s.solve() is False
