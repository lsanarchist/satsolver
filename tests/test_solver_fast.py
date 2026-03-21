import unittest

import satsolver
import satsolver_fast


class FastSolverTests(unittest.TestCase):
    def test_fast_parser_matches_base_parser_on_comments_and_percent_terminator(self) -> None:
        text = "c comment\np cnf 2 2\n1 -2 0\n0\n% ignore rest\n1 0\n"

        self.assertEqual(satsolver_fast.parse_dimacs(text), satsolver.parse_dimacs(text))

    def test_fast_parser_rejects_clause_before_problem_line(self) -> None:
        with self.assertRaisesRegex(ValueError, "problem line"):
            satsolver_fast.parse_dimacs("1 -2 0\np cnf 2 1\n")

    def test_fast_parser_rejects_literal_outside_declared_range(self) -> None:
        with self.assertRaisesRegex(ValueError, "exceeds declared variable range"):
            satsolver_fast.parse_dimacs("p cnf 3 1\n4 0\n")

    def test_fast_parser_rejects_multiple_problem_lines(self) -> None:
        with self.assertRaisesRegex(ValueError, "Multiple DIMACS problem lines"):
            satsolver_fast.parse_dimacs("p cnf 1 1\np cnf 1 1\n1 0\n")

    def test_fast_solver_matches_current_on_small_sat(self) -> None:
        num_vars, clauses = satsolver.parse_dimacs_file("small/test_1.cnf")

        baseline = satsolver.solve_cnf(num_vars, clauses)
        candidate = satsolver_fast.solve_cnf(num_vars, clauses)

        self.assertIsNotNone(baseline)
        self.assertIsNotNone(candidate)
        self.assertTrue(satsolver.model_satisfies(clauses, candidate))

    def test_fast_solver_matches_current_on_small_unsat(self) -> None:
        num_vars, clauses = satsolver.parse_dimacs_file("special/tseitin.cnf")

        baseline = satsolver.solve_cnf(num_vars, clauses)
        candidate = satsolver_fast.solve_cnf(num_vars, clauses)

        self.assertIsNone(baseline)
        self.assertIsNone(candidate)

    def test_fast_solver_handles_formula_without_root_pure_presolve(self) -> None:
        clauses = [
            [1, 2, 3],
            [1, -2, 3],
            [1, 2, -3],
        ]

        model = satsolver_fast.solve_cnf(3, clauses)

        self.assertIsNotNone(model)
        assert model is not None
        self.assertTrue(satsolver.model_satisfies(clauses, model))


if __name__ == "__main__":
    unittest.main()
