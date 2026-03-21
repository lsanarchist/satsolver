from __future__ import annotations

import itertools
import unittest
from unittest import mock

import satsolver


def xor_to_cnf(variables: tuple[int, ...], rhs: int) -> list[list[int]]:
    clauses: list[list[int]] = []
    for bits in itertools.product((0, 1), repeat=len(variables)):
        if sum(bits) % 2 == rhs:
            continue
        clause = [
            -variable if bit else variable
            for variable, bit in zip(variables, bits, strict=True)
        ]
        clauses.append(clause)
    return clauses


def brute_force_solve(num_vars: int, clauses: list[list[int]]) -> bool:
    for values in itertools.product((satsolver.FALSE, satsolver.TRUE), repeat=num_vars):
        model = [0, *values]
        if satsolver.model_satisfies(clauses, model):
            return True
    return False


class SolverRegressionTests(unittest.TestCase):
    def test_find_iterative_root_pure_literals_reaches_fixpoint(self) -> None:
        clauses = [
            [1, 2],
            [-2, 3],
            [-3, 4],
            [-4],
        ]

        self.assertEqual(
            satsolver.find_iterative_root_pure_literals(4, clauses),
            [1, -2, -3, -4],
        )

    def test_find_iterative_root_pure_literals_ignores_tautologies(self) -> None:
        clauses = [
            [1, -1, 2],
            [-2],
        ]

        self.assertEqual(satsolver.find_iterative_root_pure_literals(2, clauses), [-2])

    def test_serial_solver_gates_root_pure_presolve_by_assignment_count(self) -> None:
        original_enqueue = satsolver.Solver.enqueue

        with mock.patch("satsolver.find_iterative_root_pure_literals", return_value=[1]):
            with mock.patch.object(
                satsolver.Solver,
                "enqueue",
                autospec=True,
                wraps=original_enqueue,
            ) as enqueue:
                model = satsolver.solve_cnf_serial(1, [[1]])

        self.assertIsNotNone(model)
        self.assertEqual(enqueue.call_count, 1)

        with mock.patch("satsolver.find_iterative_root_pure_literals", return_value=[1, -2]):
            with mock.patch.object(
                satsolver.Solver,
                "enqueue",
                autospec=True,
                wraps=original_enqueue,
            ) as enqueue:
                model = satsolver.solve_cnf_serial(2, [])

        self.assertIsNotNone(model)
        self.assertEqual(enqueue.call_count, 2)

    def test_fast_serial_solver_skips_root_pure_presolve(self) -> None:
        with mock.patch(
            "satsolver.base.find_iterative_root_pure_literals",
            return_value=[1, 2],
        ) as find_root_pure:
            model = satsolver.solve_cnf_fast_serial(
                3,
                [
                    [1, 2, 3],
                    [-1, 2, 3],
                    [1, -2, 3],
                ],
            )

        self.assertIsNotNone(model)
        find_root_pure.assert_not_called()

    def test_propagate_sets_reason_and_literal_cache_for_inlined_units(self) -> None:
        binary_solver = satsolver.Solver(2)
        self.assertTrue(binary_solver.add_problem_clause([1, 2]))
        self.assertTrue(binary_solver.add_problem_clause([-1]))
        self.assertEqual(binary_solver.values[2], satsolver.TRUE)
        self.assertEqual(binary_solver.level[2], 0)
        self.assertEqual(binary_solver.literal_value(2), satsolver.TRUE)
        self.assertEqual(binary_solver.literal_value(-2), satsolver.FALSE)
        self.assertEqual(binary_solver.reason[2], 0)

        ternary_solver = satsolver.Solver(3)
        self.assertTrue(ternary_solver.add_problem_clause([1, 2, 3]))
        self.assertTrue(ternary_solver.add_problem_clause([-1]))
        self.assertTrue(ternary_solver.add_problem_clause([-2]))
        self.assertEqual(ternary_solver.values[3], satsolver.TRUE)
        self.assertEqual(ternary_solver.level[3], 0)
        self.assertEqual(ternary_solver.literal_value(3), satsolver.TRUE)
        self.assertEqual(ternary_solver.literal_value(-3), satsolver.FALSE)
        self.assertEqual(ternary_solver.reason[3], 0)

    def test_literal_value_cache_tracks_enqueue_and_backtrack(self) -> None:
        solver = satsolver.Solver(3)

        self.assertEqual(solver.literal_value(1), satsolver.UNASSIGNED)
        self.assertEqual(solver.literal_value(-1), satsolver.UNASSIGNED)
        self.assertTrue(solver.enqueue(1, None))
        self.assertEqual(solver.literal_value(1), satsolver.TRUE)
        self.assertEqual(solver.literal_value(-1), satsolver.FALSE)

        solver.trail_limits.append(len(solver.trail))
        solver.decision_level = 1
        self.assertTrue(solver.enqueue(-2, None))
        self.assertEqual(solver.literal_value(2), satsolver.FALSE)
        self.assertEqual(solver.literal_value(-2), satsolver.TRUE)

        solver.backtrack(0)

        self.assertEqual(solver.literal_value(1), satsolver.TRUE)
        self.assertEqual(solver.literal_value(-1), satsolver.FALSE)
        self.assertEqual(solver.literal_value(2), satsolver.UNASSIGNED)
        self.assertEqual(solver.literal_value(-2), satsolver.UNASSIGNED)

    def test_backtrack_trims_trail_and_resets_reasons_and_qhead(self) -> None:
        solver = satsolver.Solver(3)
        self.assertTrue(solver.enqueue(1, None))

        solver.trail_limits.append(len(solver.trail))
        solver.decision_level = 1
        self.assertTrue(solver.enqueue(-2, 17))

        solver.trail_limits.append(len(solver.trail))
        solver.decision_level = 2
        self.assertTrue(solver.enqueue(3, 18))
        solver.qhead = 1

        solver.backtrack(0)

        self.assertEqual(solver.decision_level, 0)
        self.assertEqual(solver.trail, [1])
        self.assertEqual(solver.trail_limits, [])
        self.assertEqual(solver.qhead, 1)
        self.assertEqual(solver.reason[2], None)
        self.assertEqual(solver.reason[3], None)
        self.assertEqual(solver.literal_value(2), satsolver.UNASSIGNED)
        self.assertEqual(solver.literal_value(-2), satsolver.UNASSIGNED)
        self.assertEqual(solver.literal_value(3), satsolver.UNASSIGNED)
        self.assertEqual(solver.literal_value(-3), satsolver.UNASSIGNED)

    def test_reduce_database_keeps_binary_learnt_clauses(self) -> None:
        solver = satsolver.Solver(3)
        binary_id = solver.add_learnt_clause([1, -2], lbd=5)
        solver.add_learnt_clause([1, 2, 3], lbd=5)
        solver.add_learnt_clause([-1, 2, 3], lbd=6)
        solver.next_reduce = 1

        solver.reduce_database()

        self.assertIn(binary_id, solver.learnt_ids)
        self.assertFalse(solver.clauses[binary_id].deleted)

    def test_reduce_database_never_deletes_problem_clauses(self) -> None:
        solver = satsolver.Solver(3)
        self.assertTrue(solver.add_problem_clause([1, 2, 3]))
        self.assertTrue(solver.add_problem_clause([-1, 2, 3]))
        solver.add_learnt_clause([1, -2], lbd=5)
        solver.add_learnt_clause([-1, -2, 3], lbd=6)
        solver.next_reduce = 1

        solver.reduce_database()

        self.assertFalse(solver.clauses[0].deleted)
        self.assertFalse(solver.clauses[1].deleted)

    def test_clause_ternary_flag_matches_clause_length(self) -> None:
        self.assertTrue(satsolver.Clause([1, 2, 3]).ternary)
        self.assertFalse(satsolver.Clause([1, 2]).ternary)
        self.assertFalse(satsolver.Clause([1, 2, 3, 4]).ternary)

    def test_minimize_learnt_handles_binary_and_ternary_reasons(self) -> None:
        solver = satsolver.Solver(4)
        self.assertTrue(solver.add_problem_clause([-2, 1]))
        self.assertTrue(solver.add_problem_clause([-4, 1, 3]))

        token = 1
        solver.level[1] = 1
        solver.level[2] = 1
        solver.level[3] = 1
        solver.level[4] = 1
        solver.reason[2] = 0
        solver.reason[4] = 1
        solver.seen[1] = token

        self.assertEqual(solver.minimize_learnt([1, 2, 4], token), [1, 4])

        solver.seen[3] = token
        self.assertEqual(solver.minimize_learnt([1, 4, 3], token), [1, 3])

    def test_analyze_rescales_var_activity_when_needed(self) -> None:
        solver = satsolver.Solver(2)
        solver.clauses.append(satsolver.Clause([-1, 2], learnt=False))
        solver.trail = [1, -2]
        solver.decision_level = 1
        solver.level[1] = 1
        solver.level[2] = 1
        solver.activity[1] = 1e100
        solver.var_inc = 1e100

        learnt, backtrack_level, lbd = solver.analyze(0)

        self.assertEqual(learnt, [2])
        self.assertEqual(backtrack_level, 0)
        self.assertEqual(lbd, 1)
        self.assertEqual(solver.var_inc, 1.0)
        self.assertLess(solver.activity[1], 10.0)
        self.assertLess(solver.activity[2], 10.0)

    def test_analyze_ignores_stale_seen_tokens(self) -> None:
        solver = satsolver.Solver(2)
        solver.clauses.append(satsolver.Clause([-1, 2], learnt=False))
        solver.trail = [1, -2]
        solver.decision_level = 1
        solver.level[1] = 1
        solver.level[2] = 1
        solver.seen_token = 41
        solver.seen[1] = 41
        solver.seen[2] = 41

        learnt, backtrack_level, lbd = solver.analyze(0)

        self.assertEqual(learnt, [2])
        self.assertEqual(backtrack_level, 0)
        self.assertEqual(lbd, 1)

    def test_serial_solver_handles_small_pure_ternary_formulas(self) -> None:
        sat_clauses = [
            [1, 2, 3],
            [-1, 2, 3],
            [1, -2, 3],
            [1, 2, -3],
        ]
        sat_model = satsolver.solve_cnf_serial(3, sat_clauses)
        self.assertIsNotNone(sat_model)
        self.assertTrue(satsolver.model_satisfies(sat_clauses, sat_model))

        unsat_clauses = [
            [1, 2, 3],
            [1, 2, -3],
            [1, -2, 3],
            [1, -2, -3],
            [-1, 2, 3],
            [-1, 2, -3],
            [-1, -2, 3],
            [-1, -2, -3],
        ]
        self.assertIsNone(satsolver.solve_cnf_serial(3, unsat_clauses))

    def test_parallel_portfolio_gate_is_narrow_and_disableable(self) -> None:
        large_ternary = [[1, 2, 3] for _ in range(satsolver.PORTFOLIO_MIN_CLAUSES)]
        dense_ternary = [[1, 2, 3] for _ in range(int(satsolver.PORTFOLIO_MIN_VARS * 5))]

        with mock.patch.dict("os.environ", {}, clear=True):
            with mock.patch("satsolver.os.cpu_count", return_value=4):
                self.assertTrue(
                    satsolver.should_use_parallel_portfolio(
                        satsolver.PORTFOLIO_MIN_VARS,
                        large_ternary,
                    )
                )
                self.assertFalse(
                    satsolver.should_use_parallel_portfolio(
                        satsolver.PORTFOLIO_MIN_VARS - 1,
                        large_ternary,
                    )
                )
                self.assertFalse(
                    satsolver.should_use_parallel_portfolio(
                        satsolver.PORTFOLIO_MIN_VARS,
                        large_ternary[:-1],
                    )
                )
                self.assertFalse(
                    satsolver.should_use_parallel_portfolio(
                        satsolver.PORTFOLIO_MIN_VARS,
                        [[1, 2]] + large_ternary[1:],
                    )
                )
                self.assertFalse(
                    satsolver.should_use_parallel_portfolio(
                        satsolver.PORTFOLIO_MIN_VARS,
                        dense_ternary,
                    )
                )

        with mock.patch.dict("os.environ", {satsolver.PORTFOLIO_DISABLE_ENV: "1"}, clear=True):
            with mock.patch("satsolver.os.cpu_count", return_value=4):
                self.assertFalse(
                    satsolver.should_use_parallel_portfolio(
                        satsolver.PORTFOLIO_MIN_VARS,
                        large_ternary,
                    )
                )

    def test_xor_unsat_detector_finds_inconsistent_system(self) -> None:
        clauses = []
        clauses.extend(xor_to_cnf((1, 2, 3), 0))
        clauses.extend(xor_to_cnf((1, 4, 5), 0))
        clauses.extend(xor_to_cnf((2, 4, 6), 0))
        clauses.extend(xor_to_cnf((3, 5, 6), 1))

        self.assertFalse(brute_force_solve(6, clauses))
        self.assertTrue(satsolver.xor_system_unsat(6, clauses))
        self.assertIsNone(satsolver.solve_cnf(6, clauses))

    def test_xor_unsat_detector_skips_consistent_system(self) -> None:
        clauses = []
        clauses.extend(xor_to_cnf((1, 2, 3), 0))
        clauses.extend(xor_to_cnf((1, 4, 5), 0))
        clauses.extend(xor_to_cnf((2, 4, 6), 0))
        clauses.extend(xor_to_cnf((3, 5, 6), 0))

        self.assertTrue(brute_force_solve(6, clauses))
        self.assertFalse(satsolver.xor_system_unsat(6, clauses))
        model = satsolver.solve_cnf(6, clauses)
        self.assertIsNotNone(model)
        self.assertTrue(satsolver.model_satisfies(clauses, model))


if __name__ == "__main__":
    unittest.main()
