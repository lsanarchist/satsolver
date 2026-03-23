from __future__ import annotations

import tempfile
import unittest
from pathlib import Path

from tools import profile_solver


class ProfileSolverTests(unittest.TestCase):
    def test_reason_size_bucket_boundaries(self) -> None:
        self.assertEqual(profile_solver.reason_size_bucket(2), 0)
        self.assertEqual(profile_solver.reason_size_bucket(3), 1)
        self.assertEqual(profile_solver.reason_size_bucket(4), 2)
        self.assertEqual(profile_solver.reason_size_bucket(9), 2)
        self.assertEqual(profile_solver.reason_size_bucket(10), 3)

    def test_large_watch_size_bucket_boundaries(self) -> None:
        self.assertEqual(profile_solver.large_watch_size_bucket(4), 0)
        self.assertEqual(profile_solver.large_watch_size_bucket(5), 1)
        self.assertEqual(profile_solver.large_watch_size_bucket(9), 1)
        self.assertEqual(profile_solver.large_watch_size_bucket(10), 2)

    def test_large_probe_success_bucket_boundaries(self) -> None:
        self.assertEqual(profile_solver.large_probe_success_bucket(1), 0)
        self.assertEqual(profile_solver.large_probe_success_bucket(2), 1)
        self.assertEqual(profile_solver.large_probe_success_bucket(3), 2)
        self.assertEqual(profile_solver.large_probe_success_bucket(4), 2)
        self.assertEqual(profile_solver.large_probe_success_bucket(5), 3)

    def test_learnt_large_success_bucket_boundaries(self) -> None:
        self.assertEqual(profile_solver.learnt_large_success_bucket(10, 1), 0)
        self.assertEqual(profile_solver.learnt_large_success_bucket(10, 2), 0)
        self.assertEqual(profile_solver.learnt_large_success_bucket(10, 3), 1)
        self.assertEqual(profile_solver.learnt_large_success_bucket(9, 1), 2)
        self.assertEqual(profile_solver.learnt_large_success_bucket(9, 2), 2)
        self.assertEqual(profile_solver.learnt_large_success_bucket(9, 3), 3)

    def test_profile_solver_collects_ternary_watch_and_minimization_stats(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            case_path = Path(temp_dir) / "cube_unsat.cnf"
            case_path.write_text(
                (
                    "p cnf 3 8\n"
                    "1 2 3 0\n"
                    "1 2 -3 0\n"
                    "1 -2 3 0\n"
                    "1 -2 -3 0\n"
                    "-1 2 3 0\n"
                    "-1 2 -3 0\n"
                    "-1 -2 3 0\n"
                    "-1 -2 -3 0\n"
                ),
                encoding="utf-8",
            )

            stats = profile_solver.solve_with_profile(
                str(case_path),
                restart_base=64,
                next_reduce=256,
                var_decay=0.95,
                clause_decay=0.999,
            )

            self.assertFalse(stats.sat)
            self.assertTrue(stats.ok)
            self.assertGreater(stats.conflicts, 0)
            self.assertEqual(stats.decision_trail_appends, stats.decisions)
            self.assertEqual(stats.trail_limit_pushes, stats.decisions)
            self.assertLessEqual(stats.trail_limit_pops, stats.trail_limit_pushes)
            self.assertEqual(
                stats.propagation_trail_appends,
                stats.binary_units
                + stats.problem_ternary_units
                + stats.learnt_ternary_units
                + stats.problem_large_units
                + stats.learnt_large_units,
            )
            self.assertGreater(stats.watch_clause_visits, 0)
            self.assertEqual(
                stats.watch_clause_visits,
                stats.deleted_watch_skips
                + stats.satisfied_watch_skips
                + stats.ternary_watch_visits
                + stats.large_watch_visits,
            )
            self.assertEqual(stats.watcher_list_appends, stats.watch_relocations)
            self.assertEqual(
                stats.watcher_list_pops,
                stats.watch_relocations + stats.deleted_watch_skips,
            )
            self.assertEqual(
                stats.deleted_watch_skips,
                stats.deleted_ternary_watch_pops + stats.deleted_large_watch_pops,
            )
            self.assertEqual(
                stats.watcher_list_pops,
                stats.deleted_ternary_watch_pops
                + stats.deleted_large_watch_pops
                + stats.problem_ternary_relocation_pops
                + stats.learnt_ternary_relocation_pops
                + stats.problem_large_relocation_pops
                + stats.learnt_large_relocation_pops,
            )
            self.assertEqual(
                stats.satisfied_watch_skips,
                stats.problem_ternary_satisfied_skips
                + stats.learnt_ternary_satisfied_skips
                + stats.problem_large_satisfied_skips
                + stats.learnt_large_satisfied_skips,
            )
            self.assertEqual(
                stats.watch_slot_normalizations,
                stats.ternary_slot_normalizations + stats.large_slot_normalizations,
            )
            self.assertLessEqual(stats.normalized_satisfied_skips, stats.satisfied_watch_skips)
            self.assertGreater(stats.ternary_watch_visits, 0)
            self.assertEqual(stats.large_watch_visits, 0)
            self.assertEqual(
                stats.ternary_watch_visits,
                stats.problem_ternary_watch_visits + stats.learnt_ternary_watch_visits,
            )
            self.assertEqual(
                stats.ternary_relocations,
                stats.problem_ternary_true_relocations
                + stats.problem_ternary_unassigned_relocations
                + stats.learnt_ternary_true_relocations
                + stats.learnt_ternary_unassigned_relocations,
            )
            self.assertEqual(
                stats.ternary_relocations,
                stats.problem_ternary_relocation_pops + stats.learnt_ternary_relocation_pops,
            )
            self.assertLessEqual(
                stats.problem_ternary_normalized_relocations,
                stats.problem_ternary_true_relocations + stats.problem_ternary_unassigned_relocations,
            )
            self.assertLessEqual(
                stats.learnt_ternary_normalized_relocations,
                stats.learnt_ternary_true_relocations + stats.learnt_ternary_unassigned_relocations,
            )
            self.assertEqual(
                stats.ternary_units,
                stats.problem_ternary_units + stats.learnt_ternary_units,
            )
            self.assertLessEqual(
                stats.problem_ternary_normalized_units,
                stats.problem_ternary_units,
            )
            self.assertLessEqual(
                stats.learnt_ternary_normalized_units,
                stats.learnt_ternary_units,
            )
            self.assertEqual(
                stats.ternary_conflicts,
                stats.problem_ternary_conflicts + stats.learnt_ternary_conflicts,
            )
            self.assertLessEqual(
                stats.problem_ternary_normalized_conflicts,
                stats.problem_ternary_conflicts,
            )
            self.assertLessEqual(
                stats.learnt_ternary_normalized_conflicts,
                stats.learnt_ternary_conflicts,
            )
            self.assertLessEqual(
                stats.problem_ternary_normalized_relocations
                + stats.learnt_ternary_normalized_relocations
                + stats.problem_ternary_normalized_units
                + stats.learnt_ternary_normalized_units
                + stats.problem_ternary_normalized_conflicts
                + stats.learnt_ternary_normalized_conflicts,
                stats.ternary_slot_normalizations,
            )
            self.assertEqual(
                stats.ternary_relocations,
                stats.problem_ternary_false_other_relocations
                + stats.problem_ternary_unassigned_other_relocations
                + stats.learnt_ternary_false_other_relocations
                + stats.learnt_ternary_unassigned_other_relocations,
            )
            self.assertEqual(stats.problem_ternary_clause_count, 8)
            self.assertGreater(stats.problem_ternary_distinct_clauses_visited, 0)
            self.assertLessEqual(
                stats.problem_ternary_distinct_clauses_visited,
                stats.problem_ternary_clause_count,
            )
            self.assertGreater(stats.max_problem_ternary_clause_visits, 0)
            self.assertEqual(stats.problem_ternary_literal_count, 6)
            self.assertGreater(stats.problem_ternary_distinct_trigger_literals, 0)
            self.assertLessEqual(
                stats.problem_ternary_distinct_trigger_literals,
                stats.problem_ternary_literal_count,
            )
            self.assertGreater(stats.max_problem_ternary_trigger_literal_visits, 0)
            self.assertGreater(stats.problem_ternary_watch_batches, 0)
            self.assertLessEqual(
                stats.problem_ternary_mixed_watch_batches,
                stats.problem_ternary_watch_batches,
            )
            self.assertGreaterEqual(
                stats.problem_ternary_batch_total_watchers,
                stats.problem_ternary_watch_batches,
            )
            self.assertGreaterEqual(
                stats.problem_ternary_batch_problem_ternary_watchers,
                stats.problem_ternary_watch_batches,
            )
            self.assertEqual(
                stats.problem_ternary_batch_total_watchers,
                stats.problem_ternary_batch_problem_ternary_watchers
                + stats.problem_ternary_batch_learnt_ternary_watchers
                + stats.problem_ternary_batch_problem_large_watchers
                + stats.problem_ternary_batch_learnt_large_watchers
                + stats.problem_ternary_batch_deleted_watchers,
            )
            self.assertGreater(stats.analyze_problem_reason_distinct_clauses, 0)
            self.assertLessEqual(
                stats.analyze_problem_reason_distinct_clauses,
                stats.problem_ternary_clause_count,
            )
            self.assertGreater(stats.max_analyze_problem_reason_clause_traversals, 0)
            self.assertEqual(
                stats.large_watch_visits,
                stats.problem_large_watch_visits + stats.learnt_large_watch_visits,
            )
            self.assertEqual(stats.large_slot_normalizations, 0)
            self.assertEqual(stats.watch_relocations, stats.ternary_relocations + stats.large_relocations)
            self.assertEqual(
                stats.large_relocations,
                stats.problem_large_relocations + stats.learnt_large_relocations,
            )
            self.assertEqual(
                stats.large_relocations,
                stats.problem_large_relocation_pops + stats.learnt_large_relocation_pops,
            )
            self.assertEqual(stats.watch_units, stats.ternary_units + stats.large_units)
            self.assertEqual(
                stats.large_units,
                stats.problem_large_units + stats.learnt_large_units,
            )
            self.assertEqual(stats.watch_conflicts, stats.ternary_conflicts + stats.large_conflicts)
            self.assertEqual(
                stats.large_conflicts,
                stats.problem_large_conflicts + stats.learnt_large_conflicts,
            )
            self.assertEqual(stats.large_probe_steps, 0)
            self.assertEqual(stats.max_large_probe, 0)
            self.assertEqual(stats.analyze_reason_traversals, sum(stats.analyze_reason_buckets))
            self.assertEqual(
                stats.analyze_reason_traversals,
                stats.analyze_problem_reason_traversals + stats.analyze_learnt_reason_traversals,
            )
            self.assertEqual(
                stats.minimize_reason_checks,
                sum(stats.minimize_reason_kept_buckets) + sum(stats.minimize_reason_removed_buckets),
            )
            self.assertEqual(
                stats.minimize_reason_checks,
                stats.minimize_problem_reason_checks + stats.minimize_learnt_reason_checks,
            )
            self.assertEqual(
                stats.analyze_learnt_literal_appends,
                stats.learnt_literals_before_min - stats.learnts_added,
            )
            self.assertGreater(stats.analyze_reason_traversals, 0)
            self.assertGreaterEqual(stats.learnt_literals_before_min, stats.learnt_literals_after_min)
            self.assertEqual(
                stats.minimize_removed_literals,
                stats.learnt_literals_before_min - stats.learnt_literals_after_min,
            )
            self.assertGreater(stats.lbd_sum, 0)
            self.assertLessEqual(stats.branch_multiway_best_ties, stats.decisions)
            self.assertLessEqual(stats.branch_zero_activity_choices, stats.decisions)
            self.assertLessEqual(stats.max_branch_best_tie, stats.max_branch_unassigned)

    def test_profile_solver_collects_branch_frontier_stats(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            case_path = Path(temp_dir) / "empty.cnf"
            case_path.write_text("p cnf 3 0\n", encoding="utf-8")

            stats = profile_solver.solve_with_profile(
                str(case_path),
                restart_base=64,
                next_reduce=256,
                var_decay=0.95,
                clause_decay=0.999,
            )

            self.assertTrue(stats.sat)
            self.assertTrue(stats.ok)
            self.assertEqual(stats.decisions, 3)
            self.assertEqual(stats.decision_trail_appends, 3)
            self.assertEqual(stats.propagation_trail_appends, 0)
            self.assertEqual(stats.trail_limit_pushes, 3)
            self.assertEqual(stats.trail_limit_pops, 0)
            self.assertEqual(stats.branch_unassigned_sum, 6)
            self.assertEqual(stats.branch_zero_activity_unassigned_sum, 6)
            self.assertEqual(stats.branch_best_tie_sum, 6)
            self.assertEqual(stats.branch_multiway_best_ties, 2)
            self.assertEqual(stats.branch_zero_activity_choices, 3)
            self.assertEqual(stats.max_branch_unassigned, 3)
            self.assertEqual(stats.max_branch_best_tie, 3)

    def test_profile_solver_zero_activity_branch_uses_saved_phase(self) -> None:
        solver = profile_solver.ProfiledSolver(
            1,
            restart_base=64,
            next_reduce=256,
            var_decay=0.95,
            clause_decay=0.999,
        )
        solver.saved_phase[1] = False
        solver.phase_bias[1] = 10

        literal = solver.pick_branch_literal()

        self.assertEqual(literal, -1)
        self.assertEqual(solver.decisions, 1)
        self.assertEqual(solver.branch_zero_activity_choices, 1)
        self.assertEqual(solver.branch_unassigned_sum, 1)
        self.assertEqual(solver.branch_zero_activity_unassigned_sum, 1)
        self.assertEqual(solver.branch_best_tie_sum, 1)

    def test_profile_solver_collects_restart_stats(self) -> None:
        case_path = Path(__file__).resolve().parents[1] / "small" / "test_4.cnf"

        stats = profile_solver.solve_with_profile(
            str(case_path),
            restart_base=1,
            next_reduce=256,
            var_decay=0.95,
            clause_decay=0.999,
        )

        self.assertFalse(stats.sat)
        self.assertTrue(stats.ok)
        self.assertGreater(stats.restarts, 0)
        self.assertGreaterEqual(stats.restart_conflict_sum, stats.restarts)
        self.assertGreaterEqual(stats.max_restart_conflicts, 1)
        self.assertGreaterEqual(stats.restart_decision_level_sum, stats.restarts)
        self.assertGreaterEqual(stats.max_restart_decision_level, 1)
        self.assertGreaterEqual(stats.restart_trail_sum, stats.restarts)
        self.assertGreaterEqual(stats.max_restart_trail, 1)

    def test_profile_solver_collects_reduction_stats(self) -> None:
        solver = profile_solver.ProfiledSolver(
            8,
            restart_base=64,
            next_reduce=1,
            var_decay=0.95,
            clause_decay=0.999,
        )
        locked_clause_id = solver.add_learnt_clause([1, 2, 3], 3)
        binary_clause_id = solver.add_learnt_clause([4, 5], 2)
        low_lbd_clause_id = solver.add_learnt_clause([6, 7, 8], 2)
        kept_candidate_clause_id = solver.add_learnt_clause([1, -4, 6, 7], 4)
        deleted_candidate_clause_id = solver.add_learnt_clause([-1, -5, -6, 8], 5)
        solver.reason[1] = locked_clause_id

        solver.reduce_database()

        self.assertEqual(solver.reductions, 1)
        self.assertEqual(solver.reduction_live_learnts_sum, 5)
        self.assertEqual(solver.reduction_locked_clause_sum, 1)
        self.assertEqual(solver.reduction_candidate_clause_sum, 2)
        self.assertEqual(solver.reduction_deleted_clause_sum, 1)
        self.assertEqual(solver.max_reduction_live_learnts, 5)
        self.assertEqual(solver.max_reduction_locked_clause_count, 1)
        self.assertEqual(solver.max_reduction_candidate_clause_count, 2)
        self.assertEqual(solver.max_reduction_deleted_clause_count, 1)
        self.assertFalse(solver.clauses[locked_clause_id].deleted)
        self.assertFalse(solver.clauses[binary_clause_id].deleted)
        self.assertFalse(solver.clauses[low_lbd_clause_id].deleted)
        self.assertFalse(solver.clauses[kept_candidate_clause_id].deleted)
        self.assertTrue(solver.clauses[deleted_candidate_clause_id].deleted)
        self.assertEqual(
            solver.learnt_ids,
            [
                locked_clause_id,
                binary_clause_id,
                low_lbd_clause_id,
                kept_candidate_clause_id,
            ],
        )

    def test_profile_solver_splits_satisfied_watch_skips_by_clause_family(self) -> None:
        solver = profile_solver.ProfiledSolver(
            3,
            restart_base=64,
            next_reduce=256,
            var_decay=0.95,
            clause_decay=0.999,
        )

        for clause in ([1, 2, 3], [2], [-1]):
            self.assertTrue(solver.add_problem_clause(clause))

        model = solver.solve()

        self.assertIsNotNone(model)
        self.assertGreater(solver.problem_ternary_satisfied_skips, 0)
        self.assertEqual(solver.learnt_ternary_satisfied_skips, 0)
        self.assertEqual(solver.problem_large_satisfied_skips, 0)
        self.assertEqual(solver.learnt_large_satisfied_skips, 0)
        self.assertEqual(
            solver.satisfied_watch_skips,
            solver.problem_ternary_satisfied_skips
            + solver.learnt_ternary_satisfied_skips
            + solver.problem_large_satisfied_skips
            + solver.learnt_large_satisfied_skips,
        )
        self.assertEqual(
            solver.ternary_units,
            solver.problem_ternary_units + solver.learnt_ternary_units,
        )
        self.assertEqual(
            solver.ternary_conflicts,
            solver.problem_ternary_conflicts + solver.learnt_ternary_conflicts,
        )

    def test_profile_solver_splits_ternary_relocations_by_candidate_value(self) -> None:
        solver = profile_solver.ProfiledSolver(
            7,
            restart_base=64,
            next_reduce=256,
            var_decay=0.95,
            clause_decay=0.999,
        )
        clauses = [
            [1, 2, 3],
            [5, 6, 7],
            [3],
            [-4, -1],
            [-4, -2],
            [-4, -5],
            [4],
        ]

        for clause in clauses:
            self.assertTrue(solver.add_problem_clause(clause))

        model = solver.solve()

        self.assertIsNotNone(model)
        self.assertGreater(solver.problem_ternary_true_relocations, 0)
        self.assertGreater(solver.problem_ternary_unassigned_relocations, 0)
        self.assertGreater(solver.problem_ternary_false_other_relocations, 0)
        self.assertGreater(solver.problem_ternary_unassigned_other_relocations, 0)
        self.assertEqual(solver.learnt_ternary_true_relocations, 0)
        self.assertEqual(solver.learnt_ternary_unassigned_relocations, 0)
        self.assertEqual(solver.learnt_ternary_false_other_relocations, 0)
        self.assertEqual(solver.learnt_ternary_unassigned_other_relocations, 0)
        self.assertEqual(
            solver.ternary_relocations,
            solver.problem_ternary_true_relocations
            + solver.problem_ternary_unassigned_relocations
            + solver.learnt_ternary_true_relocations
            + solver.learnt_ternary_unassigned_relocations,
        )
        self.assertLessEqual(
            solver.problem_ternary_normalized_relocations,
            solver.problem_ternary_true_relocations + solver.problem_ternary_unassigned_relocations,
        )
        self.assertLessEqual(
            solver.problem_ternary_normalized_units,
            solver.problem_ternary_units,
        )
        self.assertLessEqual(
            solver.problem_ternary_normalized_conflicts,
            solver.problem_ternary_conflicts,
        )
        self.assertEqual(
            solver.ternary_relocations,
            solver.problem_ternary_false_other_relocations
            + solver.problem_ternary_unassigned_other_relocations
            + solver.learnt_ternary_false_other_relocations
            + solver.learnt_ternary_unassigned_other_relocations,
        )

    def test_profile_solver_collects_large_clause_probe_stats(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            case_path = Path(temp_dir) / "large_watch_unsat.cnf"
            case_path.write_text(
                (
                    "p cnf 4 5\n"
                    "1 2 3 4 0\n"
                    "-1 0\n"
                    "-2 0\n"
                    "-3 0\n"
                    "-4 0\n"
                ),
                encoding="utf-8",
            )

            stats = profile_solver.solve_with_profile(
                str(case_path),
                restart_base=64,
                next_reduce=256,
                var_decay=0.95,
                clause_decay=0.999,
            )

            self.assertFalse(stats.sat)
            self.assertTrue(stats.ok)
            self.assertGreater(stats.watch_clause_visits, 0)
            self.assertGreater(stats.large_watch_visits, 0)
            self.assertEqual(stats.watcher_list_appends, stats.watch_relocations)
            self.assertEqual(
                stats.watcher_list_pops,
                stats.watch_relocations + stats.deleted_watch_skips,
            )
            self.assertEqual(
                stats.deleted_watch_skips,
                stats.deleted_ternary_watch_pops + stats.deleted_large_watch_pops,
            )
            self.assertEqual(
                stats.watcher_list_pops,
                stats.deleted_ternary_watch_pops
                + stats.deleted_large_watch_pops
                + stats.problem_ternary_relocation_pops
                + stats.learnt_ternary_relocation_pops
                + stats.problem_large_relocation_pops
                + stats.learnt_large_relocation_pops,
            )
            self.assertEqual(stats.problem_ternary_clause_count, 0)
            self.assertEqual(stats.problem_ternary_distinct_clauses_visited, 0)
            self.assertEqual(stats.max_problem_ternary_clause_visits, 0)
            self.assertEqual(stats.problem_ternary_literal_count, 0)
            self.assertEqual(stats.problem_ternary_distinct_trigger_literals, 0)
            self.assertEqual(stats.max_problem_ternary_trigger_literal_visits, 0)
            self.assertEqual(stats.problem_ternary_watch_batches, 0)
            self.assertEqual(stats.problem_ternary_mixed_watch_batches, 0)
            self.assertEqual(stats.problem_ternary_batch_total_watchers, 0)
            self.assertEqual(stats.problem_ternary_batch_problem_ternary_watchers, 0)
            self.assertEqual(stats.problem_ternary_batch_learnt_ternary_watchers, 0)
            self.assertEqual(stats.problem_ternary_batch_problem_large_watchers, 0)
            self.assertEqual(stats.problem_ternary_batch_learnt_large_watchers, 0)
            self.assertEqual(stats.problem_ternary_batch_deleted_watchers, 0)
            self.assertEqual(
                stats.watch_slot_normalizations,
                stats.ternary_slot_normalizations + stats.large_slot_normalizations,
            )
            self.assertLessEqual(stats.normalized_satisfied_skips, stats.satisfied_watch_skips)
            self.assertEqual(stats.ternary_slot_normalizations, 0)
            self.assertEqual(
                stats.ternary_watch_visits,
                stats.problem_ternary_watch_visits + stats.learnt_ternary_watch_visits,
            )
            self.assertEqual(
                stats.ternary_relocations,
                stats.problem_ternary_true_relocations
                + stats.problem_ternary_unassigned_relocations
                + stats.learnt_ternary_true_relocations
                + stats.learnt_ternary_unassigned_relocations,
            )
            self.assertEqual(
                stats.ternary_relocations,
                stats.problem_ternary_false_other_relocations
                + stats.problem_ternary_unassigned_other_relocations
                + stats.learnt_ternary_false_other_relocations
                + stats.learnt_ternary_unassigned_other_relocations,
            )
            self.assertEqual(
                stats.large_watch_visits,
                stats.problem_large_watch_visits + stats.learnt_large_watch_visits,
            )
            self.assertEqual(
                stats.large_relocations,
                stats.problem_large_relocations + stats.learnt_large_relocations,
            )
            self.assertEqual(
                stats.large_relocations,
                stats.problem_large_relocation_pops + stats.learnt_large_relocation_pops,
            )
            self.assertEqual(stats.problem_ternary_normalized_relocations, 0)
            self.assertEqual(stats.learnt_ternary_normalized_relocations, 0)
            self.assertEqual(stats.problem_ternary_normalized_units, 0)
            self.assertEqual(stats.learnt_ternary_normalized_units, 0)
            self.assertEqual(stats.problem_ternary_normalized_conflicts, 0)
            self.assertEqual(stats.learnt_ternary_normalized_conflicts, 0)
            self.assertEqual(
                stats.large_units,
                stats.problem_large_units + stats.learnt_large_units,
            )
            self.assertEqual(
                stats.large_conflicts,
                stats.problem_large_conflicts + stats.learnt_large_conflicts,
            )
            self.assertEqual(
                stats.large_watch_visits,
                stats.large_watch_len4_visits
                + stats.large_watch_len5_9_visits
                + stats.large_watch_len10_plus_visits,
            )
            self.assertGreater(stats.large_probe_steps, 0)
            self.assertGreater(stats.max_large_probe, 0)
            self.assertGreater(stats.large_watch_len4_visits, 0)
            self.assertEqual(stats.large_watch_len5_9_visits, 0)
            self.assertEqual(stats.large_watch_len10_plus_visits, 0)
            self.assertEqual(
                stats.large_probe_steps,
                stats.large_probe_success_steps + stats.large_probe_failure_steps,
            )
            self.assertEqual(
                stats.large_relocations,
                stats.large_probe_success_step1
                + stats.large_probe_success_step2
                + stats.large_probe_success_step3_4
                + stats.large_probe_success_step5_plus,
            )
            self.assertEqual(
                stats.learnt_large_relocations,
                stats.learnt_large_success_len10_plus_step1_2
                + stats.learnt_large_success_len10_plus_step3_plus
                + stats.learnt_large_success_sub10_step1_2
                + stats.learnt_large_success_sub10_step3_plus,
            )
            self.assertEqual(
                stats.learnt_large_success_sub10_step3_plus,
                stats.learnt_large_success_sub10_step3_4
                + stats.learnt_large_success_sub10_step5_plus,
            )
            self.assertEqual(
                stats.learnt_large_success_sub10_step3_4,
                stats.learnt_large_success_sub10_step3
                + stats.learnt_large_success_sub10_step4,
            )
            self.assertEqual(
                stats.learnt_large_success_sub10_step3,
                stats.learnt_large_success_sub10_step3_source_pop_last_slot
                + stats.learnt_large_success_sub10_step3_source_pop_overwrite,
            )
            self.assertEqual(
                stats.learnt_large_success_sub10_step3_source_pop_overwrite,
                stats.learnt_large_success_sub10_step3_source_pop_overwrite_shallow
                + stats.learnt_large_success_sub10_step3_source_pop_overwrite_deep,
            )
            self.assertEqual(
                stats.learnt_large_success_sub10_step3_source_pop_overwrite_deep,
                stats.learnt_large_success_sub10_step3_source_pop_overwrite_deep_index2
                + stats.learnt_large_success_sub10_step3_source_pop_overwrite_deep_index3_plus,
            )
            self.assertGreater(stats.large_relocations + stats.large_units + stats.large_conflicts, 0)
            self.assertEqual(stats.watch_relocations, stats.ternary_relocations + stats.large_relocations)
            self.assertEqual(stats.watch_units, stats.ternary_units + stats.large_units)
            self.assertEqual(stats.watch_conflicts, stats.ternary_conflicts + stats.large_conflicts)
            self.assertEqual(
                stats.analyze_reason_traversals,
                stats.analyze_problem_reason_traversals + stats.analyze_learnt_reason_traversals,
            )
            self.assertEqual(
                stats.minimize_reason_checks,
                stats.minimize_problem_reason_checks + stats.minimize_learnt_reason_checks,
            )

    def test_profile_solver_splits_large_watch_visits_by_clause_size(self) -> None:
        solver = profile_solver.ProfiledSolver(
            19,
            restart_base=64,
            next_reduce=256,
            var_decay=0.95,
            clause_decay=0.999,
        )
        clauses = [
            [1, 2, 3, 4],
            [-1],
            [-2],
            [-3],
            [4],
            [5, 6, 7, 8, 9],
            [-5],
            [-6],
            [-7],
            [-8],
            [9],
            [10, 11, 12, 13, 14, 15, 16, 17, 18, 19],
            [-10],
            [-11],
            [-12],
            [-13],
            [-14],
            [-15],
            [-16],
            [-17],
            [-18],
            [19],
        ]

        for clause in clauses:
            self.assertTrue(solver.add_problem_clause(clause))

        model = solver.solve()

        self.assertIsNotNone(model)
        self.assertGreater(solver.large_watch_len4_visits, 0)
        self.assertGreater(solver.large_watch_len5_9_visits, 0)
        self.assertGreater(solver.large_watch_len10_plus_visits, 0)
        self.assertEqual(
            solver.large_watch_visits,
            solver.large_watch_len4_visits
            + solver.large_watch_len5_9_visits
            + solver.large_watch_len10_plus_visits,
        )

    def test_profile_solver_splits_large_relocation_probe_depths(self) -> None:
        solver = profile_solver.ProfiledSolver(
            20,
            restart_base=64,
            next_reduce=256,
            var_decay=0.95,
            clause_decay=0.999,
        )
        clauses = [
            [1, 2, 3, 4],
            [-1],
            [5, 6, -7, 8],
            [-5],
            [7],
            [9, 10, -11, -12, 13],
            [-9],
            [11],
            [12],
            [14, 15, -16, -17, -18, -19, 20],
            [-14],
            [16],
            [17],
            [18],
            [19],
        ]

        for clause in clauses:
            self.assertTrue(solver.add_problem_clause(clause))

        model = solver.solve()

        self.assertIsNotNone(model)
        self.assertGreater(solver.large_probe_success_step1, 0)
        self.assertGreater(solver.large_probe_success_step2, 0)
        self.assertGreater(solver.large_probe_success_step3_4, 0)
        self.assertGreater(solver.large_probe_success_step5_plus, 0)
        self.assertEqual(
            solver.large_relocations,
            solver.large_probe_success_step1
            + solver.large_probe_success_step2
            + solver.large_probe_success_step3_4
            + solver.large_probe_success_step5_plus,
        )

    def test_profile_solver_splits_learnt_large_success_buckets(self) -> None:
        solver = profile_solver.ProfiledSolver(
            28,
            restart_base=64,
            next_reduce=256,
            var_decay=0.95,
            clause_decay=0.999,
        )

        solver.add_learnt_clause([1, 2, 3, 4, 5, 6, 7, 8, 9, 10], lbd=2)
        solver.add_learnt_clause([11, 12, 13, 14, 15], lbd=2)
        solver.add_learnt_clause([16, 17, 18, 19, 20, 21], lbd=2)
        solver.add_learnt_clause([22, 23, 24, 25, 26, 27, 28], lbd=2)

        self.assertTrue(solver.enqueue(-1, None))
        self.assertTrue(solver.enqueue(-11, None))
        self.assertTrue(solver.enqueue(-13, None))
        self.assertTrue(solver.enqueue(-14, None))
        self.assertTrue(solver.enqueue(-16, None))
        self.assertTrue(solver.enqueue(-18, None))
        self.assertTrue(solver.enqueue(-19, None))
        self.assertTrue(solver.enqueue(-20, None))
        self.assertTrue(solver.enqueue(-22, None))
        self.assertTrue(solver.enqueue(-24, None))
        self.assertTrue(solver.enqueue(-25, None))
        self.assertTrue(solver.enqueue(-26, None))
        self.assertTrue(solver.enqueue(-27, None))

        self.assertIsNone(solver.propagate())
        self.assertEqual(solver.learnt_large_relocations, 4)
        self.assertEqual(solver.learnt_large_success_len10_plus_step1_2, 1)
        self.assertEqual(solver.learnt_large_success_len10_plus_step3_plus, 0)
        self.assertEqual(solver.learnt_large_success_sub10_step1_2, 0)
        self.assertEqual(solver.learnt_large_success_sub10_step3_plus, 3)
        self.assertEqual(solver.learnt_large_success_sub10_step3_4, 2)
        self.assertEqual(solver.learnt_large_success_sub10_step3, 1)
        self.assertEqual(solver.learnt_large_success_sub10_step3_source_pop_last_slot, 1)
        self.assertEqual(solver.learnt_large_success_sub10_step3_source_pop_overwrite, 0)
        self.assertEqual(solver.learnt_large_success_sub10_step4, 1)
        self.assertEqual(solver.learnt_large_success_sub10_step5_plus, 1)

    def test_profile_solver_splits_exact_step3_tail_positions(self) -> None:
        solver = profile_solver.ProfiledSolver(
            9,
            restart_base=64,
            next_reduce=256,
            var_decay=0.95,
            clause_decay=0.999,
        )

        solver.add_learnt_clause([1, 2, 3, 4, 5], lbd=2)
        solver.add_learnt_clause([1, 6, 7, 8, 9], lbd=2)

        self.assertTrue(solver.enqueue(-1, None))
        self.assertTrue(solver.enqueue(-3, None))
        self.assertTrue(solver.enqueue(-4, None))
        self.assertTrue(solver.enqueue(-7, None))
        self.assertTrue(solver.enqueue(-8, None))

        self.assertIsNone(solver.propagate())
        self.assertEqual(solver.learnt_large_relocations, 2)
        self.assertEqual(solver.learnt_large_success_sub10_step3, 2)
        self.assertEqual(solver.learnt_large_success_sub10_step3_4, 2)
        self.assertEqual(solver.learnt_large_success_sub10_step3_source_pop_last_slot, 1)
        self.assertEqual(solver.learnt_large_success_sub10_step3_source_pop_overwrite, 1)
        self.assertEqual(solver.learnt_large_success_sub10_step3_source_pop_overwrite_shallow, 1)
        self.assertEqual(solver.learnt_large_success_sub10_step3_source_pop_overwrite_deep, 0)

    def test_profile_solver_splits_exact_step3_overwrite_depths(self) -> None:
        solver = profile_solver.ProfiledSolver(
            31,
            restart_base=64,
            next_reduce=256,
            var_decay=0.95,
            clause_decay=0.999,
        )

        solver.add_learnt_clause([1, 20, 21, 22, 23], lbd=2)
        solver.add_learnt_clause([1, 2, 3, 4, 5], lbd=2)
        solver.add_learnt_clause([1, 6, 7, 8, 9], lbd=2)
        solver.add_learnt_clause([1, 24, 25, 26, 27], lbd=2)
        solver.add_learnt_clause([1, 28, 29, 30, 31], lbd=2)

        self.assertTrue(solver.enqueue(-1, None))
        self.assertTrue(solver.enqueue(20, None))
        self.assertTrue(solver.enqueue(-3, None))
        self.assertTrue(solver.enqueue(-4, None))
        self.assertTrue(solver.enqueue(-7, None))
        self.assertTrue(solver.enqueue(-8, None))
        self.assertTrue(solver.enqueue(24, None))
        self.assertTrue(solver.enqueue(28, None))

        self.assertIsNone(solver.propagate())
        self.assertEqual(solver.learnt_large_relocations, 2)
        self.assertEqual(solver.learnt_large_success_sub10_step3, 2)
        self.assertEqual(solver.learnt_large_success_sub10_step3_source_pop_last_slot, 0)
        self.assertEqual(solver.learnt_large_success_sub10_step3_source_pop_overwrite, 2)
        self.assertEqual(solver.learnt_large_success_sub10_step3_source_pop_overwrite_shallow, 1)
        self.assertEqual(solver.learnt_large_success_sub10_step3_source_pop_overwrite_deep, 1)
        self.assertEqual(solver.learnt_large_success_sub10_step3_source_pop_overwrite_deep_index2, 1)
        self.assertEqual(solver.learnt_large_success_sub10_step3_source_pop_overwrite_deep_index3_plus, 0)

    def test_profile_solver_splits_exact_step3_deep_overwrite_source_indices(self) -> None:
        solver = profile_solver.ProfiledSolver(
            63,
            restart_base=64,
            next_reduce=256,
            var_decay=0.95,
            clause_decay=0.999,
        )

        solver.add_learnt_clause([1, 20, 21, 22, 23], lbd=2)
        solver.add_learnt_clause([1, 24, 25, 26, 27], lbd=2)
        solver.add_learnt_clause([1, 2, 3, 4, 5], lbd=2)
        solver.add_learnt_clause([1, 28, 29, 30, 31], lbd=2)

        solver.add_learnt_clause([11, 40, 41, 42, 43], lbd=2)
        solver.add_learnt_clause([11, 44, 45, 46, 47], lbd=2)
        solver.add_learnt_clause([11, 48, 49, 50, 51], lbd=2)
        solver.add_learnt_clause([11, 12, 13, 14, 15], lbd=2)
        solver.add_learnt_clause([11, 52, 53, 54, 55], lbd=2)

        self.assertTrue(solver.enqueue(-1, None))
        self.assertTrue(solver.enqueue(20, None))
        self.assertTrue(solver.enqueue(24, None))
        self.assertTrue(solver.enqueue(-3, None))
        self.assertTrue(solver.enqueue(-4, None))
        self.assertTrue(solver.enqueue(28, None))

        self.assertTrue(solver.enqueue(-11, None))
        self.assertTrue(solver.enqueue(40, None))
        self.assertTrue(solver.enqueue(44, None))
        self.assertTrue(solver.enqueue(48, None))
        self.assertTrue(solver.enqueue(-13, None))
        self.assertTrue(solver.enqueue(-14, None))
        self.assertTrue(solver.enqueue(52, None))

        self.assertIsNone(solver.propagate())
        self.assertEqual(solver.learnt_large_relocations, 2)
        self.assertEqual(solver.learnt_large_success_sub10_step3, 2)
        self.assertEqual(solver.learnt_large_success_sub10_step3_source_pop_last_slot, 0)
        self.assertEqual(solver.learnt_large_success_sub10_step3_source_pop_overwrite, 2)
        self.assertEqual(solver.learnt_large_success_sub10_step3_source_pop_overwrite_shallow, 0)
        self.assertEqual(solver.learnt_large_success_sub10_step3_source_pop_overwrite_deep, 2)
        self.assertEqual(solver.learnt_large_success_sub10_step3_source_pop_overwrite_deep_index2, 1)
        self.assertEqual(solver.learnt_large_success_sub10_step3_source_pop_overwrite_deep_index3_plus, 1)


if __name__ == "__main__":
    unittest.main()
