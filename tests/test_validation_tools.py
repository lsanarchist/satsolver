from __future__ import annotations

import unittest

import satsolver
from tools import checker


class ParseDimacsRegressionTests(unittest.TestCase):
    def test_parse_dimacs_ignores_comments_and_percent_terminator(self) -> None:
        num_vars, clauses = satsolver.parse_dimacs("c note\np cnf 2 2\n1 -2 0\n0\n% rest ignored\n1 0\n")
        self.assertEqual((num_vars, clauses), (2, [[1, -2], []]))

    def test_rejects_clause_before_problem_line(self) -> None:
        with self.assertRaisesRegex(ValueError, "problem line"):
            satsolver.parse_dimacs("1 -2 0\np cnf 2 1\n")

    def test_rejects_literal_outside_declared_range(self) -> None:
        with self.assertRaisesRegex(ValueError, "exceeds declared variable range"):
            satsolver.parse_dimacs("p cnf 3 1\n4 0\n")

    def test_rejects_multiple_problem_lines(self) -> None:
        with self.assertRaisesRegex(ValueError, "Multiple DIMACS problem lines"):
            satsolver.parse_dimacs("p cnf 1 1\np cnf 1 1\n1 0\n")

    def test_empty_clause_parses_and_solves_unsat(self) -> None:
        num_vars, clauses = satsolver.parse_dimacs("p cnf 1 1\n0\n")
        self.assertEqual((num_vars, clauses), (1, [[]]))
        self.assertIsNone(satsolver.solve_cnf(num_vars, clauses))


class CheckerRegressionTests(unittest.TestCase):
    def test_valid_sat_assignment_passes(self) -> None:
        num_vars, clauses = 3, [[1, -2], [2, 3]]
        result = checker.validate_output_text(num_vars, clauses, "SAT\n1 2 -3 0\n")
        self.assertEqual(result, "valid SAT")

    def test_sat_assignment_missing_variable_fails(self) -> None:
        num_vars, clauses = 3, [[1, -2], [2, 3]]
        with self.assertRaisesRegex(checker.ValidationError, "exactly 3 literals"):
            checker.validate_output_text(num_vars, clauses, "SAT\n1 2 0\n")

    def test_sat_assignment_that_does_not_satisfy_fails(self) -> None:
        num_vars, clauses = 2, [[1], [2]]
        with self.assertRaisesRegex(checker.ValidationError, "does not satisfy"):
            checker.validate_output_text(num_vars, clauses, "SAT\n1 -2 0\n")

    def test_valid_unsat_small_formula_is_bruteforce_checked(self) -> None:
        num_vars, clauses = 1, [[1], [-1]]
        result = checker.validate_output_text(num_vars, clauses, "UNSAT\n")
        self.assertEqual(result, "valid UNSAT (brute-force checked)")

    def test_unsat_claim_on_sat_formula_fails(self) -> None:
        num_vars, clauses = 2, [[1, 2]]
        with self.assertRaisesRegex(checker.ValidationError, "brute force found"):
            checker.validate_output_text(num_vars, clauses, "UNSAT\n")


if __name__ == "__main__":
    unittest.main()
