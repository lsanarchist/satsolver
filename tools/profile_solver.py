from __future__ import annotations

import argparse
import sys
from dataclasses import dataclass
from pathlib import Path
from time import perf_counter
from typing import Optional

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

import satsolver


@dataclass(slots=True)
class RunStats:
    path: str
    sat: bool
    ok: bool
    elapsed_s: float
    decisions: int
    decision_trail_appends: int
    propagation_trail_appends: int
    branch_unassigned_sum: int
    branch_zero_activity_unassigned_sum: int
    branch_best_tie_sum: int
    branch_multiway_best_ties: int
    branch_zero_activity_choices: int
    max_branch_unassigned: int
    max_branch_best_tie: int
    conflicts: int
    processed_literals: int
    propagations: int
    restarts: int
    restart_conflict_sum: int
    max_restart_conflicts: int
    restart_decision_level_sum: int
    max_restart_decision_level: int
    restart_trail_sum: int
    max_restart_trail: int
    reductions: int
    reduction_live_learnts_sum: int
    reduction_locked_clause_sum: int
    reduction_candidate_clause_sum: int
    reduction_deleted_clause_sum: int
    max_reduction_live_learnts: int
    max_reduction_locked_clause_count: int
    max_reduction_candidate_clause_count: int
    max_reduction_deleted_clause_count: int
    learnts_added: int
    live_learnts: int
    max_live_learnts: int
    max_trail: int
    restart_base: int
    next_reduce: int
    var_decay: float
    clause_decay: float
    trail_limit_pushes: int
    trail_limit_pops: int
    binary_clause_checks: int
    binary_units: int
    binary_conflicts: int
    watch_clause_visits: int
    deleted_watch_skips: int
    ternary_watch_visits: int
    large_watch_visits: int
    large_watch_len4_visits: int
    large_watch_len5_9_visits: int
    large_watch_len10_plus_visits: int
    problem_ternary_watch_visits: int
    learnt_ternary_watch_visits: int
    problem_large_watch_visits: int
    learnt_large_watch_visits: int
    problem_ternary_watch_batches: int
    problem_ternary_mixed_watch_batches: int
    problem_ternary_batch_total_watchers: int
    problem_ternary_batch_problem_ternary_watchers: int
    problem_ternary_batch_learnt_ternary_watchers: int
    problem_ternary_batch_problem_large_watchers: int
    problem_ternary_batch_learnt_large_watchers: int
    problem_ternary_batch_deleted_watchers: int
    problem_ternary_satisfied_skips: int
    learnt_ternary_satisfied_skips: int
    problem_large_satisfied_skips: int
    learnt_large_satisfied_skips: int
    problem_ternary_normalized_relocations: int
    learnt_ternary_normalized_relocations: int
    problem_ternary_normalized_units: int
    learnt_ternary_normalized_units: int
    problem_ternary_normalized_conflicts: int
    learnt_ternary_normalized_conflicts: int
    problem_ternary_true_relocations: int
    problem_ternary_unassigned_relocations: int
    learnt_ternary_true_relocations: int
    learnt_ternary_unassigned_relocations: int
    problem_ternary_units: int
    learnt_ternary_units: int
    problem_ternary_conflicts: int
    learnt_ternary_conflicts: int
    problem_ternary_false_other_relocations: int
    problem_ternary_unassigned_other_relocations: int
    learnt_ternary_false_other_relocations: int
    learnt_ternary_unassigned_other_relocations: int
    problem_ternary_clause_count: int
    problem_ternary_distinct_clauses_visited: int
    max_problem_ternary_clause_visits: int
    problem_ternary_literal_count: int
    problem_ternary_distinct_trigger_literals: int
    max_problem_ternary_trigger_literal_visits: int
    satisfied_watch_skips: int
    watch_slot_normalizations: int
    ternary_slot_normalizations: int
    large_slot_normalizations: int
    normalized_satisfied_skips: int
    watcher_list_appends: int
    watcher_list_pops: int
    deleted_ternary_watch_pops: int
    deleted_large_watch_pops: int
    problem_ternary_relocation_pops: int
    learnt_ternary_relocation_pops: int
    problem_large_relocation_pops: int
    learnt_large_relocation_pops: int
    watch_relocations: int
    watch_units: int
    watch_conflicts: int
    ternary_relocations: int
    ternary_units: int
    ternary_conflicts: int
    large_relocations: int
    problem_large_relocations: int
    learnt_large_relocations: int
    large_units: int
    problem_large_units: int
    learnt_large_units: int
    large_conflicts: int
    problem_large_conflicts: int
    learnt_large_conflicts: int
    large_probe_steps: int
    large_probe_success_steps: int
    large_probe_failure_steps: int
    large_probe_success_step1: int
    large_probe_success_step2: int
    large_probe_success_step3_4: int
    large_probe_success_step5_plus: int
    learnt_large_success_len10_plus_step1_2: int
    learnt_large_success_len10_plus_step3_plus: int
    learnt_large_success_sub10_step1_2: int
    learnt_large_success_sub10_step3_plus: int
    learnt_large_success_sub10_step3_4: int
    learnt_large_success_sub10_step3: int
    learnt_large_success_sub10_step3_source_pop_last_slot: int
    learnt_large_success_sub10_step3_source_pop_overwrite: int
    learnt_large_success_sub10_step3_source_pop_overwrite_shallow: int
    learnt_large_success_sub10_step3_source_pop_overwrite_deep: int
    learnt_large_success_sub10_step3_source_pop_overwrite_deep_index2: int
    learnt_large_success_sub10_step3_source_pop_overwrite_deep_index3_plus: int
    learnt_large_success_sub10_step3_source_pop_overwrite_deep_index3: int
    learnt_large_success_sub10_step3_source_pop_overwrite_deep_index4_plus: int
    learnt_large_success_sub10_step3_source_pop_overwrite_deep_index4: int
    learnt_large_success_sub10_step3_source_pop_overwrite_deep_index5_plus: int
    learnt_large_success_sub10_step4: int
    learnt_large_success_sub10_step5_plus: int
    max_large_probe: int
    analyze_reason_traversals: int
    analyze_problem_reason_traversals: int
    analyze_learnt_reason_traversals: int
    analyze_problem_reason_distinct_clauses: int
    max_analyze_problem_reason_clause_traversals: int
    analyze_reason_buckets: tuple[int, int, int, int]
    minimize_reason_checks: int
    minimize_problem_reason_checks: int
    minimize_learnt_reason_checks: int
    minimize_reason_kept_buckets: tuple[int, int, int, int]
    minimize_reason_removed_buckets: tuple[int, int, int, int]
    analyze_learnt_literal_appends: int
    learnt_literals_before_min: int
    learnt_literals_after_min: int
    minimize_removed_literals: int
    max_learnt_before: int
    max_learnt_after: int
    lbd_sum: int


def reason_size_bucket(size: int) -> int:
    if size <= 2:
        return 0
    if size == 3:
        return 1
    if size <= 9:
        return 2
    return 3


def large_watch_size_bucket(size: int) -> int:
    if size == 4:
        return 0
    if size <= 9:
        return 1
    return 2


def large_probe_success_bucket(probe_steps: int) -> int:
    if probe_steps <= 1:
        return 0
    if probe_steps == 2:
        return 1
    if probe_steps <= 4:
        return 2
    return 3


def learnt_large_success_bucket(clause_size: int, probe_steps: int) -> int:
    if clause_size >= 10:
        if probe_steps <= 2:
            return 0
        return 1
    if probe_steps <= 2:
        return 2
    return 3


class ProfiledSolver(satsolver.Solver):
    def __init__(
        self,
        num_vars: int,
        *,
        restart_base: int = 64,
        next_reduce: int = 256,
        var_decay: float = 0.95,
        clause_decay: float = 0.999,
    ) -> None:
        super().__init__(num_vars)
        self.restart_base = restart_base
        self.next_reduce = next_reduce
        self.var_decay = var_decay
        self.clause_decay = clause_decay

        self.decisions = 0
        self.trail_limit_pushes = 0
        self.trail_limit_pops = 0
        self.decision_trail_appends = 0
        self.propagation_trail_appends = 0
        self.branch_unassigned_sum = 0
        self.branch_zero_activity_unassigned_sum = 0
        self.branch_best_tie_sum = 0
        self.branch_multiway_best_ties = 0
        self.branch_zero_activity_choices = 0
        self.max_branch_unassigned = 0
        self.max_branch_best_tie = 0
        self.propagations = 0
        self.processed_literals = 0
        self.restarts = 0
        self.restart_conflict_sum = 0
        self.max_restart_conflicts = 0
        self.restart_decision_level_sum = 0
        self.max_restart_decision_level = 0
        self.restart_trail_sum = 0
        self.max_restart_trail = 0
        self.reductions = 0
        self.reduction_live_learnts_sum = 0
        self.reduction_locked_clause_sum = 0
        self.reduction_candidate_clause_sum = 0
        self.reduction_deleted_clause_sum = 0
        self.max_reduction_live_learnts = 0
        self.max_reduction_locked_clause_count = 0
        self.max_reduction_candidate_clause_count = 0
        self.max_reduction_deleted_clause_count = 0
        self.learnts_added = 0
        self.max_live_learnts = 0
        self.max_trail = 0
        self.binary_clause_checks = 0
        self.binary_units = 0
        self.binary_conflicts = 0
        self.watch_clause_visits = 0
        self.deleted_watch_skips = 0
        self.ternary_watch_visits = 0
        self.large_watch_visits = 0
        self.large_watch_len4_visits = 0
        self.large_watch_len5_9_visits = 0
        self.large_watch_len10_plus_visits = 0
        self.problem_ternary_watch_visits = 0
        self.learnt_ternary_watch_visits = 0
        self.problem_large_watch_visits = 0
        self.learnt_large_watch_visits = 0
        self.problem_ternary_watch_batches = 0
        self.problem_ternary_mixed_watch_batches = 0
        self.problem_ternary_batch_total_watchers = 0
        self.problem_ternary_batch_problem_ternary_watchers = 0
        self.problem_ternary_batch_learnt_ternary_watchers = 0
        self.problem_ternary_batch_problem_large_watchers = 0
        self.problem_ternary_batch_learnt_large_watchers = 0
        self.problem_ternary_batch_deleted_watchers = 0
        self.problem_ternary_satisfied_skips = 0
        self.learnt_ternary_satisfied_skips = 0
        self.problem_large_satisfied_skips = 0
        self.learnt_large_satisfied_skips = 0
        self.problem_ternary_normalized_relocations = 0
        self.learnt_ternary_normalized_relocations = 0
        self.problem_ternary_normalized_units = 0
        self.learnt_ternary_normalized_units = 0
        self.problem_ternary_normalized_conflicts = 0
        self.learnt_ternary_normalized_conflicts = 0
        self.problem_ternary_true_relocations = 0
        self.problem_ternary_unassigned_relocations = 0
        self.learnt_ternary_true_relocations = 0
        self.learnt_ternary_unassigned_relocations = 0
        self.problem_ternary_units = 0
        self.learnt_ternary_units = 0
        self.problem_ternary_conflicts = 0
        self.learnt_ternary_conflicts = 0
        self.problem_ternary_false_other_relocations = 0
        self.problem_ternary_unassigned_other_relocations = 0
        self.learnt_ternary_false_other_relocations = 0
        self.learnt_ternary_unassigned_other_relocations = 0
        self.problem_ternary_clause_visit_counts: dict[int, int] = {}
        self.problem_ternary_trigger_literal_counts: dict[int, int] = {}
        self.problem_reason_clause_traversal_counts: dict[int, int] = {}
        self.satisfied_watch_skips = 0
        self.watch_slot_normalizations = 0
        self.ternary_slot_normalizations = 0
        self.large_slot_normalizations = 0
        self.normalized_satisfied_skips = 0
        self.watcher_list_appends = 0
        self.watcher_list_pops = 0
        self.deleted_ternary_watch_pops = 0
        self.deleted_large_watch_pops = 0
        self.problem_ternary_relocation_pops = 0
        self.learnt_ternary_relocation_pops = 0
        self.problem_large_relocation_pops = 0
        self.learnt_large_relocation_pops = 0
        self.watch_relocations = 0
        self.watch_units = 0
        self.watch_conflicts = 0
        self.ternary_relocations = 0
        self.ternary_units = 0
        self.ternary_conflicts = 0
        self.large_relocations = 0
        self.problem_large_relocations = 0
        self.learnt_large_relocations = 0
        self.large_units = 0
        self.problem_large_units = 0
        self.learnt_large_units = 0
        self.large_conflicts = 0
        self.problem_large_conflicts = 0
        self.learnt_large_conflicts = 0
        self.large_probe_steps = 0
        self.large_probe_success_steps = 0
        self.large_probe_failure_steps = 0
        self.large_probe_success_step1 = 0
        self.large_probe_success_step2 = 0
        self.large_probe_success_step3_4 = 0
        self.large_probe_success_step5_plus = 0
        self.learnt_large_success_len10_plus_step1_2 = 0
        self.learnt_large_success_len10_plus_step3_plus = 0
        self.learnt_large_success_sub10_step1_2 = 0
        self.learnt_large_success_sub10_step3_plus = 0
        self.learnt_large_success_sub10_step3_4 = 0
        self.learnt_large_success_sub10_step3 = 0
        self.learnt_large_success_sub10_step3_source_pop_last_slot = 0
        self.learnt_large_success_sub10_step3_source_pop_overwrite = 0
        self.learnt_large_success_sub10_step3_source_pop_overwrite_shallow = 0
        self.learnt_large_success_sub10_step3_source_pop_overwrite_deep = 0
        self.learnt_large_success_sub10_step3_source_pop_overwrite_deep_index2 = 0
        self.learnt_large_success_sub10_step3_source_pop_overwrite_deep_index3_plus = 0
        self.learnt_large_success_sub10_step3_source_pop_overwrite_deep_index3 = 0
        self.learnt_large_success_sub10_step3_source_pop_overwrite_deep_index4_plus = 0
        self.learnt_large_success_sub10_step3_source_pop_overwrite_deep_index4 = 0
        self.learnt_large_success_sub10_step3_source_pop_overwrite_deep_index5_plus = 0
        self.learnt_large_success_sub10_step4 = 0
        self.learnt_large_success_sub10_step5_plus = 0
        self.max_large_probe = 0
        self.analyze_reason_traversals = 0
        self.analyze_problem_reason_traversals = 0
        self.analyze_learnt_reason_traversals = 0
        self.analyze_reason_buckets = [0, 0, 0, 0]
        self.minimize_reason_checks = 0
        self.minimize_problem_reason_checks = 0
        self.minimize_learnt_reason_checks = 0
        self.minimize_reason_kept_buckets = [0, 0, 0, 0]
        self.minimize_reason_removed_buckets = [0, 0, 0, 0]
        self.analyze_learnt_literal_appends = 0
        self.learnt_literals_before_min = 0
        self.learnt_literals_after_min = 0
        self.minimize_removed_literals = 0
        self.max_learnt_before = 0
        self.max_learnt_after = 0
        self.lbd_sum = 0

    def enqueue(self, literal: int, reason: Optional[int]) -> bool:
        assigned = super().enqueue(literal, reason)
        if assigned:
            self.max_trail = max(self.max_trail, len(self.trail))
        return assigned

    def add_learnt_clause(self, literals: list[int], lbd: int) -> int:
        clause_id = super().add_learnt_clause(literals, lbd)
        self.learnts_added += 1
        live_learnts = sum(1 for learnt_id in self.learnt_ids if not self.clauses[learnt_id].deleted)
        self.max_live_learnts = max(self.max_live_learnts, live_learnts)
        return clause_id

    def backtrack(self, level: int) -> None:
        current_level = self.decision_level
        if current_level > level:
            self.trail_limit_pops += current_level - level
        super().backtrack(level)

    def propagate(self) -> Optional[int]:
        clauses = self.clauses
        literal_values = self.literal_values
        literal_var = self.literal_var
        literal_sign = self.literal_sign
        literal_watch_index = self.literal_watch_index
        negated_watch_index = self.negated_watch_index
        binary_implications = self.binary_implications
        all_watchers = self.watchers
        values = self.values
        levels = self.level
        reasons = self.reason
        saved_phase = self.saved_phase
        trail = self.trail
        decision_level = self.decision_level
        qhead = self.qhead
        trail_len = len(trail)
        start_qhead = qhead
        self.propagations += 1

        while qhead < trail_len:
            literal = trail[qhead]
            qhead += 1

            for implied_literal, clause_id in binary_implications[literal_watch_index[literal]]:
                self.binary_clause_checks += 1
                clause = clauses[clause_id]
                if clause.deleted:
                    continue

                implied_value = literal_values[implied_literal]
                if implied_value == satsolver.FALSE:
                    self.binary_conflicts += 1
                    self.qhead = qhead
                    self.processed_literals += qhead - start_qhead
                    return clause_id
                if implied_value == satsolver.UNASSIGNED:
                    variable = literal_var[implied_literal]
                    value = literal_sign[implied_literal]
                    values[variable] = value
                    literal_values[variable] = value
                    literal_values[-variable] = -value
                    levels[variable] = decision_level
                    reasons[variable] = clause_id
                    saved_phase[variable] = implied_literal > 0
                    trail.append(implied_literal)
                    self.propagation_trail_appends += 1
                    self.max_trail = max(self.max_trail, len(trail))
                    self.binary_units += 1
                    trail_len += 1

            false_literal = -literal
            watchers = all_watchers[negated_watch_index[literal]]
            index = 0
            watchers_len = len(watchers)

            if watchers_len:
                batch_problem_ternary = 0
                batch_learnt_ternary = 0
                batch_problem_large = 0
                batch_learnt_large = 0
                batch_deleted = 0

                for batch_clause_id in watchers:
                    batch_clause = clauses[batch_clause_id]
                    if batch_clause.learnt and batch_clause.deleted:
                        batch_deleted += 1
                        continue

                    if len(batch_clause.lits) == 3:
                        if batch_clause.learnt:
                            batch_learnt_ternary += 1
                        else:
                            batch_problem_ternary += 1
                    elif batch_clause.learnt:
                        batch_learnt_large += 1
                    else:
                        batch_problem_large += 1

                if batch_problem_ternary:
                    self.problem_ternary_watch_batches += 1
                    self.problem_ternary_batch_total_watchers += watchers_len
                    self.problem_ternary_batch_problem_ternary_watchers += batch_problem_ternary
                    self.problem_ternary_batch_learnt_ternary_watchers += batch_learnt_ternary
                    self.problem_ternary_batch_problem_large_watchers += batch_problem_large
                    self.problem_ternary_batch_learnt_large_watchers += batch_learnt_large
                    self.problem_ternary_batch_deleted_watchers += batch_deleted
                    if batch_learnt_ternary or batch_problem_large or batch_learnt_large or batch_deleted:
                        self.problem_ternary_mixed_watch_batches += 1

            while index < watchers_len:
                self.watch_clause_visits += 1
                clause_id = watchers[index]
                clause = clauses[clause_id]
                lits = clause.lits
                clause_size = len(lits)

                if clause.learnt and clause.deleted:
                    self.deleted_watch_skips += 1
                    if clause_size == 3:
                        self.deleted_ternary_watch_pops += 1
                    else:
                        self.deleted_large_watch_pops += 1
                    self.watcher_list_pops += 1
                    watchers_len -= 1
                    watchers[index] = watchers[watchers_len]
                    watchers.pop()
                    continue

                normalized = lits[0] == false_literal
                if normalized:
                    self.watch_slot_normalizations += 1
                    if clause_size == 3:
                        self.ternary_slot_normalizations += 1
                    else:
                        self.large_slot_normalizations += 1
                    lits[0], lits[1] = lits[1], lits[0]

                other_literal = lits[0]
                other_value = literal_values[other_literal]

                if other_value == satsolver.TRUE:
                    self.satisfied_watch_skips += 1
                    if clause_size == 3:
                        if clause.learnt:
                            self.learnt_ternary_satisfied_skips += 1
                        else:
                            self.problem_ternary_satisfied_skips += 1
                    elif clause.learnt:
                        self.learnt_large_satisfied_skips += 1
                    else:
                        self.problem_large_satisfied_skips += 1
                    if normalized:
                        self.normalized_satisfied_skips += 1
                    index += 1
                    continue

                if clause_size == 3:
                    self.ternary_watch_visits += 1
                    if clause.learnt:
                        self.learnt_ternary_watch_visits += 1
                    else:
                        self.problem_ternary_watch_visits += 1
                        self.problem_ternary_clause_visit_counts[clause_id] = (
                            self.problem_ternary_clause_visit_counts.get(clause_id, 0) + 1
                        )
                        self.problem_ternary_trigger_literal_counts[false_literal] = (
                            self.problem_ternary_trigger_literal_counts.get(false_literal, 0) + 1
                        )
                    candidate_literal = lits[2]
                    candidate_value = literal_values[candidate_literal]
                    if candidate_value != satsolver.FALSE:
                        self.watch_relocations += 1
                        self.ternary_relocations += 1
                        if clause.learnt:
                            if normalized:
                                self.learnt_ternary_normalized_relocations += 1
                            if candidate_value == satsolver.TRUE:
                                self.learnt_ternary_true_relocations += 1
                            else:
                                self.learnt_ternary_unassigned_relocations += 1
                            if other_value == satsolver.FALSE:
                                self.learnt_ternary_false_other_relocations += 1
                            else:
                                self.learnt_ternary_unassigned_other_relocations += 1
                        else:
                            if normalized:
                                self.problem_ternary_normalized_relocations += 1
                            if candidate_value == satsolver.TRUE:
                                self.problem_ternary_true_relocations += 1
                            else:
                                self.problem_ternary_unassigned_relocations += 1
                            if other_value == satsolver.FALSE:
                                self.problem_ternary_false_other_relocations += 1
                            else:
                                self.problem_ternary_unassigned_other_relocations += 1
                        false_watched_literal = lits[1]
                        lits[1] = candidate_literal
                        lits[2] = false_watched_literal
                        all_watchers[literal_watch_index[candidate_literal]].append(clause_id)
                        self.watcher_list_appends += 1
                        self.watcher_list_pops += 1
                        if clause.learnt:
                            self.learnt_ternary_relocation_pops += 1
                        else:
                            self.problem_ternary_relocation_pops += 1
                        watchers_len -= 1
                        watchers[index] = watchers[watchers_len]
                        watchers.pop()
                        continue

                    if other_value != satsolver.FALSE:
                        variable = literal_var[other_literal]
                        value = literal_sign[other_literal]
                        values[variable] = value
                        literal_values[variable] = value
                        literal_values[-variable] = -value
                        levels[variable] = decision_level
                        reasons[variable] = clause_id
                        saved_phase[variable] = other_literal > 0
                        trail.append(other_literal)
                        self.propagation_trail_appends += 1
                        self.max_trail = max(self.max_trail, len(trail))
                        self.watch_units += 1
                        self.ternary_units += 1
                        if clause.learnt:
                            if normalized:
                                self.learnt_ternary_normalized_units += 1
                            self.learnt_ternary_units += 1
                        else:
                            if normalized:
                                self.problem_ternary_normalized_units += 1
                            self.problem_ternary_units += 1
                        trail_len += 1
                        index += 1
                        continue
                    self.watch_conflicts += 1
                    self.ternary_conflicts += 1
                    if clause.learnt:
                        if normalized:
                            self.learnt_ternary_normalized_conflicts += 1
                        self.learnt_ternary_conflicts += 1
                    else:
                        if normalized:
                            self.problem_ternary_normalized_conflicts += 1
                        self.problem_ternary_conflicts += 1
                    self.qhead = qhead
                    self.processed_literals += qhead - start_qhead
                    return clause_id

                self.large_watch_visits += 1
                if clause_size == 4:
                    self.large_watch_len4_visits += 1
                elif clause_size <= 9:
                    self.large_watch_len5_9_visits += 1
                else:
                    self.large_watch_len10_plus_visits += 1
                if clause.learnt:
                    self.learnt_large_watch_visits += 1
                else:
                    self.problem_large_watch_visits += 1
                found_replacement = False
                probe_steps = 0
                for replacement in range(2, clause_size):
                    probe_steps += 1
                    candidate_literal = lits[replacement]
                    candidate_value = literal_values[candidate_literal]
                    if candidate_value != satsolver.FALSE:
                        self.watch_relocations += 1
                        self.large_relocations += 1
                        if clause.learnt:
                            self.learnt_large_relocations += 1
                            learnt_success_bucket = learnt_large_success_bucket(
                                clause_size,
                                probe_steps,
                            )
                            if learnt_success_bucket == 0:
                                self.learnt_large_success_len10_plus_step1_2 += 1
                            elif learnt_success_bucket == 1:
                                self.learnt_large_success_len10_plus_step3_plus += 1
                            elif learnt_success_bucket == 2:
                                self.learnt_large_success_sub10_step1_2 += 1
                            else:
                                self.learnt_large_success_sub10_step3_plus += 1
                                if probe_steps == 3:
                                    self.learnt_large_success_sub10_step3_4 += 1
                                    self.learnt_large_success_sub10_step3 += 1
                                    # Separate the exact step-3 tail self-assignment case from
                                    # removals that still overwrite the current slot from elsewhere.
                                    if index == watchers_len - 1:
                                        self.learnt_large_success_sub10_step3_source_pop_last_slot += 1
                                    else:
                                        self.learnt_large_success_sub10_step3_source_pop_overwrite += 1
                                        # Treat the first two watcher slots as the shallow lane and
                                        # everything beyond them as the deeper overwrite tail.
                                        if index <= 1:
                                            self.learnt_large_success_sub10_step3_source_pop_overwrite_shallow += 1
                                        else:
                                            self.learnt_large_success_sub10_step3_source_pop_overwrite_deep += 1
                                            if index == 2:
                                                self.learnt_large_success_sub10_step3_source_pop_overwrite_deep_index2 += 1
                                            else:
                                                self.learnt_large_success_sub10_step3_source_pop_overwrite_deep_index3_plus += 1
                                                if index == 3:
                                                    self.learnt_large_success_sub10_step3_source_pop_overwrite_deep_index3 += 1
                                                else:
                                                    self.learnt_large_success_sub10_step3_source_pop_overwrite_deep_index4_plus += 1
                                                    if index == 4:
                                                        self.learnt_large_success_sub10_step3_source_pop_overwrite_deep_index4 += 1
                                                    else:
                                                        self.learnt_large_success_sub10_step3_source_pop_overwrite_deep_index5_plus += 1
                                elif probe_steps == 4:
                                    self.learnt_large_success_sub10_step3_4 += 1
                                    self.learnt_large_success_sub10_step4 += 1
                                else:
                                    self.learnt_large_success_sub10_step5_plus += 1
                        else:
                            self.problem_large_relocations += 1
                        self.large_probe_steps += probe_steps
                        self.large_probe_success_steps += probe_steps
                        if probe_steps == 1:
                            self.large_probe_success_step1 += 1
                        elif probe_steps == 2:
                            self.large_probe_success_step2 += 1
                        elif probe_steps <= 4:
                            self.large_probe_success_step3_4 += 1
                        else:
                            self.large_probe_success_step5_plus += 1
                        self.max_large_probe = max(self.max_large_probe, probe_steps)
                        lits[1], lits[replacement] = lits[replacement], lits[1]
                        all_watchers[literal_watch_index[lits[1]]].append(clause_id)
                        self.watcher_list_appends += 1
                        self.watcher_list_pops += 1
                        if clause.learnt:
                            self.learnt_large_relocation_pops += 1
                        else:
                            self.problem_large_relocation_pops += 1
                        watchers_len -= 1
                        watchers[index] = watchers[watchers_len]
                        watchers.pop()
                        found_replacement = True
                        break

                if found_replacement:
                    continue

                self.large_probe_steps += probe_steps
                self.large_probe_failure_steps += probe_steps
                self.max_large_probe = max(self.max_large_probe, probe_steps)
                if other_value == satsolver.FALSE:
                    self.watch_conflicts += 1
                    self.large_conflicts += 1
                    if clause.learnt:
                        self.learnt_large_conflicts += 1
                    else:
                        self.problem_large_conflicts += 1
                    self.qhead = qhead
                    self.processed_literals += qhead - start_qhead
                    return clause_id
                if other_value == satsolver.UNASSIGNED:
                    variable = literal_var[other_literal]
                    value = literal_sign[other_literal]
                    values[variable] = value
                    literal_values[variable] = value
                    literal_values[-variable] = -value
                    levels[variable] = decision_level
                    reasons[variable] = clause_id
                    saved_phase[variable] = other_literal > 0
                    trail.append(other_literal)
                    self.propagation_trail_appends += 1
                    self.max_trail = max(self.max_trail, len(trail))
                    self.watch_units += 1
                    self.large_units += 1
                    if clause.learnt:
                        self.learnt_large_units += 1
                    else:
                        self.problem_large_units += 1
                    trail_len += 1
                index += 1

        self.qhead = qhead
        self.processed_literals += qhead - start_qhead
        return None

    def pick_branch_literal(self) -> int:
        best_variable = 0
        best_activity = -1.0
        best_tie_count = 0
        unassigned_count = 0
        zero_activity_unassigned_count = 0

        values = self.values
        activity = self.activity

        for variable in range(1, self.num_vars + 1):
            if values[variable] != satsolver.UNASSIGNED:
                continue

            unassigned_count += 1
            variable_activity = activity[variable]
            if variable_activity == 0.0:
                zero_activity_unassigned_count += 1

            if variable_activity > best_activity:
                best_activity = variable_activity
                best_variable = variable
                best_tie_count = 1
            elif variable_activity == best_activity:
                best_tie_count += 1

        if best_variable == 0:
            return 0

        self.decisions += 1
        self.branch_unassigned_sum += unassigned_count
        self.branch_zero_activity_unassigned_sum += zero_activity_unassigned_count
        self.branch_best_tie_sum += best_tie_count
        if best_tie_count > 1:
            self.branch_multiway_best_ties += 1
        self.max_branch_unassigned = max(self.max_branch_unassigned, unassigned_count)
        self.max_branch_best_tie = max(self.max_branch_best_tie, best_tie_count)

        positive = self.saved_phase[best_variable]
        if best_activity == 0.0:
            self.branch_zero_activity_choices += 1
        return best_variable if positive else -best_variable

    def reduce_database(self) -> None:
        if len(self.learnt_ids) < self.next_reduce:
            return

        self.reductions += 1

        live_learnts = sum(
            1 for learnt_id in self.learnt_ids if not self.clauses[learnt_id].deleted
        )
        locked = {clause_id for clause_id in self.reason[1:] if clause_id is not None}
        keep: list[int] = []
        candidates: list[int] = []

        for clause_id in self.learnt_ids:
            clause = self.clauses[clause_id]
            if clause.deleted:
                continue
            if clause_id in locked or len(clause.lits) <= 2 or clause.lbd <= 2:
                keep.append(clause_id)
            else:
                candidates.append(clause_id)

        candidates.sort(
            key=lambda clause_id: (
                self.clauses[clause_id].lbd,
                -self.clauses[clause_id].activity,
                len(self.clauses[clause_id].lits),
            )
        )
        midpoint = len(candidates) // 2
        deleted_count = len(candidates) - midpoint

        self.reduction_live_learnts_sum += live_learnts
        self.reduction_locked_clause_sum += len(locked)
        self.reduction_candidate_clause_sum += len(candidates)
        self.reduction_deleted_clause_sum += deleted_count
        self.max_reduction_live_learnts = max(self.max_reduction_live_learnts, live_learnts)
        self.max_reduction_locked_clause_count = max(
            self.max_reduction_locked_clause_count,
            len(locked),
        )
        self.max_reduction_candidate_clause_count = max(
            self.max_reduction_candidate_clause_count,
            len(candidates),
        )
        self.max_reduction_deleted_clause_count = max(
            self.max_reduction_deleted_clause_count,
            deleted_count,
        )

        keep.extend(candidates[:midpoint])
        for clause_id in candidates[midpoint:]:
            self.clauses[clause_id].deleted = True

        self.learnt_ids = keep
        self.next_reduce = max(256, int(len(self.learnt_ids) * 1.5) + 64)

    def _minimize_learnt_and_prepare(
        self,
        learnt: list[int],
        token: int,
    ) -> tuple[list[int], int, int]:
        if len(learnt) == 1:
            return learnt, 0, 1

        levels = self.level
        reasons = self.reason
        seen = self.seen
        clauses = self.clauses
        kept_buckets = self.minimize_reason_kept_buckets
        removed_buckets = self.minimize_reason_removed_buckets
        self.lbd_token += 1
        lbd_token = self.lbd_token
        lbd_marks = self.lbd_marks
        write_index = 1
        first_level = levels[abs(learnt[0])]
        lbd_marks[first_level] = lbd_token
        lbd = 1
        best_index = 1
        best_level = 0

        for read_index in range(1, len(learnt)):
            literal = learnt[read_index]
            reason_clause_id = reasons[abs(literal)]
            keep_literal = False
            if reason_clause_id is None:
                keep_literal = True
            else:
                reason_clause = clauses[reason_clause_id]
                reason_lits = reason_clause.lits
                bucket = reason_size_bucket(len(reason_lits))
                neg_literal = -literal
                self.minimize_reason_checks += 1
                if reason_clause.learnt:
                    self.minimize_learnt_reason_checks += 1
                else:
                    self.minimize_problem_reason_checks += 1

                if len(reason_lits) == 2:
                    first, second = reason_lits
                    other_variable = abs(second if first == neg_literal else first)
                    keep_literal = levels[other_variable] != 0 and seen[other_variable] != token
                elif len(reason_lits) == 3:
                    first, second, third = reason_lits
                    if first == neg_literal:
                        first_variable = abs(second)
                        second_variable = abs(third)
                    elif second == neg_literal:
                        first_variable = abs(first)
                        second_variable = abs(third)
                    else:
                        first_variable = abs(first)
                        second_variable = abs(second)

                    keep_literal = (
                        (levels[first_variable] != 0 and seen[first_variable] != token)
                        or (levels[second_variable] != 0 and seen[second_variable] != token)
                    )
                else:
                    keep_literal = False
                    for reason_literal in reason_lits:
                        if reason_literal == neg_literal:
                            continue
                        variable = abs(reason_literal)
                        if levels[variable] != 0 and seen[variable] != token:
                            keep_literal = True
                            break

                if keep_literal:
                    kept_buckets[bucket] += 1
                else:
                    removed_buckets[bucket] += 1

            if keep_literal:
                learnt[write_index] = literal
                decision_level = levels[abs(literal)]
                if lbd_marks[decision_level] != lbd_token:
                    lbd_marks[decision_level] = lbd_token
                    lbd += 1
                if decision_level > best_level:
                    best_level = decision_level
                    best_index = write_index
                write_index += 1

        del learnt[write_index:]
        if write_index == 1:
            return learnt, 0, 1
        learnt[1], learnt[best_index] = learnt[best_index], learnt[1]
        return learnt, best_level, lbd

    def minimize_learnt(self, learnt: list[int], token: int) -> list[int]:
        learnt, _, _ = self._minimize_learnt_and_prepare(learnt, token)
        return learnt

    def analyze(self, conflict_clause_id: int) -> tuple[list[int], int, int]:
        learnt = [0]
        self.seen_token += 1
        token = self.seen_token

        clauses = self.clauses
        levels = self.level
        reasons = self.reason
        seen = self.seen
        trail = self.trail
        current_level = self.decision_level
        activity = self.activity
        var_inc = self.var_inc
        num_vars = self.num_vars

        current_clause_id = conflict_clause_id
        path_count = 0
        pivot = 0
        trail_index = len(trail) - 1

        while True:
            clause = clauses[current_clause_id]
            if clause.learnt:
                self.bump_clause_activity(current_clause_id)

            for literal in clause.lits:
                if literal == pivot:
                    continue
                variable = abs(literal)
                if seen[variable] == token or levels[variable] == 0:
                    continue

                seen[variable] = token
                activity[variable] += var_inc
                if activity[variable] > 1e100:
                    for index in range(1, num_vars + 1):
                        activity[index] *= 1e-100
                    var_inc *= 1e-100

                if levels[variable] == current_level:
                    path_count += 1
                else:
                    learnt.append(literal)
                    self.analyze_learnt_literal_appends += 1

            while True:
                pivot = trail[trail_index]
                trail_index -= 1
                pivot_variable = abs(pivot)
                if seen[pivot_variable] == token:
                    break

            seen[pivot_variable] = 0
            path_count -= 1
            if path_count == 0:
                learnt[0] = -pivot
                break

            reason_clause_id = reasons[pivot_variable]
            if reason_clause_id is None:
                learnt[0] = -pivot
                break
            self.analyze_reason_traversals += 1
            reason_clause = clauses[reason_clause_id]
            if reason_clause.learnt:
                self.analyze_learnt_reason_traversals += 1
            else:
                self.analyze_problem_reason_traversals += 1
                self.problem_reason_clause_traversal_counts[reason_clause_id] = (
                    self.problem_reason_clause_traversal_counts.get(reason_clause_id, 0) + 1
                )
            self.analyze_reason_buckets[reason_size_bucket(len(reason_clause.lits))] += 1
            current_clause_id = reason_clause_id

        learnt_before = len(learnt)
        self.learnt_literals_before_min += learnt_before
        self.max_learnt_before = max(self.max_learnt_before, learnt_before)
        learnt, best_level, lbd = self._minimize_learnt_and_prepare(learnt, token)
        learnt_after = len(learnt)
        self.learnt_literals_after_min += learnt_after
        self.minimize_removed_literals += learnt_before - learnt_after
        self.max_learnt_after = max(self.max_learnt_after, learnt_after)
        self.var_inc = var_inc
        self.lbd_sum += lbd
        return learnt, best_level, lbd

    def solve(self) -> Optional[list[int]]:
        if not self.ok:
            return None

        root_conflict = self.propagate()
        if root_conflict is not None:
            self.ok = False
            return None

        restart_index = 1
        conflicts_since_restart = 0
        restart_limit = self.restart_base * satsolver.luby(restart_index)

        while True:
            conflict = self.propagate()
            if conflict is not None:
                self.conflicts += 1
                conflicts_since_restart += 1

                if self.current_level() == 0:
                    self.ok = False
                    return None

                learnt, backtrack_level, lbd = self.analyze(conflict)
                self.backtrack(backtrack_level)
                learnt_clause_id = self.add_learnt_clause(learnt, lbd)
                if not self.enqueue(learnt[0], learnt_clause_id):
                    self.ok = False
                    return None

                self.decay_var_activity()
                self.decay_clause_activity()

                if conflicts_since_restart >= restart_limit:
                    if self.current_level() > 0:
                        self.restarts += 1
                        self.restart_conflict_sum += conflicts_since_restart
                        self.max_restart_conflicts = max(
                            self.max_restart_conflicts,
                            conflicts_since_restart,
                        )
                        self.restart_decision_level_sum += self.current_level()
                        self.max_restart_decision_level = max(
                            self.max_restart_decision_level,
                            self.current_level(),
                        )
                        self.restart_trail_sum += len(self.trail)
                        self.max_restart_trail = max(
                            self.max_restart_trail,
                            len(self.trail),
                        )
                    self.backtrack(0)
                    conflicts_since_restart = 0
                    restart_index += 1
                    restart_limit = self.restart_base * satsolver.luby(restart_index)

                self.reduce_database()
                continue

            branch_literal = self.pick_branch_literal()
            if branch_literal == 0:
                return self.build_model()

            self.trail_limits.append(len(self.trail))
            self.trail_limit_pushes += 1
            self.decision_level += 1
            self.enqueue(branch_literal, None)
            self.decision_trail_appends += 1


def build_run_stats(
    path: str,
    solver: ProfiledSolver | None,
    *,
    sat: bool,
    ok: bool,
    elapsed_s: float,
    restart_base: int,
    next_reduce: int,
    var_decay: float,
    clause_decay: float,
) -> RunStats:
    if solver is None:
        return RunStats(
            path=path,
            sat=sat,
            ok=ok,
            elapsed_s=elapsed_s,
            decisions=0,
            decision_trail_appends=0,
            propagation_trail_appends=0,
            branch_unassigned_sum=0,
            branch_zero_activity_unassigned_sum=0,
            branch_best_tie_sum=0,
            branch_multiway_best_ties=0,
            branch_zero_activity_choices=0,
            max_branch_unassigned=0,
            max_branch_best_tie=0,
            conflicts=0,
            processed_literals=0,
            propagations=0,
            restarts=0,
            restart_conflict_sum=0,
            max_restart_conflicts=0,
            restart_decision_level_sum=0,
            max_restart_decision_level=0,
            restart_trail_sum=0,
            max_restart_trail=0,
            reductions=0,
            reduction_live_learnts_sum=0,
            reduction_locked_clause_sum=0,
            reduction_candidate_clause_sum=0,
            reduction_deleted_clause_sum=0,
            max_reduction_live_learnts=0,
            max_reduction_locked_clause_count=0,
            max_reduction_candidate_clause_count=0,
            max_reduction_deleted_clause_count=0,
            learnts_added=0,
            live_learnts=0,
            max_live_learnts=0,
            max_trail=0,
            restart_base=restart_base,
            next_reduce=next_reduce,
            var_decay=var_decay,
            clause_decay=clause_decay,
            trail_limit_pushes=0,
            trail_limit_pops=0,
            binary_clause_checks=0,
            binary_units=0,
            binary_conflicts=0,
            watch_clause_visits=0,
            deleted_watch_skips=0,
            ternary_watch_visits=0,
            large_watch_visits=0,
            large_watch_len4_visits=0,
            large_watch_len5_9_visits=0,
            large_watch_len10_plus_visits=0,
            problem_ternary_watch_visits=0,
            learnt_ternary_watch_visits=0,
            problem_large_watch_visits=0,
            learnt_large_watch_visits=0,
            problem_ternary_watch_batches=0,
            problem_ternary_mixed_watch_batches=0,
            problem_ternary_batch_total_watchers=0,
            problem_ternary_batch_problem_ternary_watchers=0,
            problem_ternary_batch_learnt_ternary_watchers=0,
            problem_ternary_batch_problem_large_watchers=0,
            problem_ternary_batch_learnt_large_watchers=0,
            problem_ternary_batch_deleted_watchers=0,
            problem_ternary_satisfied_skips=0,
            learnt_ternary_satisfied_skips=0,
            problem_large_satisfied_skips=0,
            learnt_large_satisfied_skips=0,
            problem_ternary_normalized_relocations=0,
            learnt_ternary_normalized_relocations=0,
            problem_ternary_normalized_units=0,
            learnt_ternary_normalized_units=0,
            problem_ternary_normalized_conflicts=0,
            learnt_ternary_normalized_conflicts=0,
            problem_ternary_true_relocations=0,
            problem_ternary_unassigned_relocations=0,
            learnt_ternary_true_relocations=0,
            learnt_ternary_unassigned_relocations=0,
            problem_ternary_units=0,
            learnt_ternary_units=0,
            problem_ternary_conflicts=0,
            learnt_ternary_conflicts=0,
            problem_ternary_false_other_relocations=0,
            problem_ternary_unassigned_other_relocations=0,
            learnt_ternary_false_other_relocations=0,
            learnt_ternary_unassigned_other_relocations=0,
            problem_ternary_clause_count=0,
            problem_ternary_distinct_clauses_visited=0,
            max_problem_ternary_clause_visits=0,
            problem_ternary_literal_count=0,
            problem_ternary_distinct_trigger_literals=0,
            max_problem_ternary_trigger_literal_visits=0,
            satisfied_watch_skips=0,
            watch_slot_normalizations=0,
            ternary_slot_normalizations=0,
            large_slot_normalizations=0,
            normalized_satisfied_skips=0,
            watcher_list_appends=0,
            watcher_list_pops=0,
            deleted_ternary_watch_pops=0,
            deleted_large_watch_pops=0,
            problem_ternary_relocation_pops=0,
            learnt_ternary_relocation_pops=0,
            problem_large_relocation_pops=0,
            learnt_large_relocation_pops=0,
            watch_relocations=0,
            watch_units=0,
            watch_conflicts=0,
            ternary_relocations=0,
            ternary_units=0,
            ternary_conflicts=0,
            large_relocations=0,
            problem_large_relocations=0,
            learnt_large_relocations=0,
            large_units=0,
            problem_large_units=0,
            learnt_large_units=0,
            large_conflicts=0,
            problem_large_conflicts=0,
            learnt_large_conflicts=0,
            large_probe_steps=0,
            large_probe_success_steps=0,
            large_probe_failure_steps=0,
            large_probe_success_step1=0,
            large_probe_success_step2=0,
            large_probe_success_step3_4=0,
            large_probe_success_step5_plus=0,
            learnt_large_success_len10_plus_step1_2=0,
            learnt_large_success_len10_plus_step3_plus=0,
            learnt_large_success_sub10_step1_2=0,
            learnt_large_success_sub10_step3_plus=0,
            learnt_large_success_sub10_step3_4=0,
            learnt_large_success_sub10_step3=0,
            learnt_large_success_sub10_step3_source_pop_last_slot=0,
            learnt_large_success_sub10_step3_source_pop_overwrite=0,
            learnt_large_success_sub10_step3_source_pop_overwrite_shallow=0,
            learnt_large_success_sub10_step3_source_pop_overwrite_deep=0,
            learnt_large_success_sub10_step3_source_pop_overwrite_deep_index2=0,
            learnt_large_success_sub10_step3_source_pop_overwrite_deep_index3_plus=0,
            learnt_large_success_sub10_step3_source_pop_overwrite_deep_index3=0,
            learnt_large_success_sub10_step3_source_pop_overwrite_deep_index4_plus=0,
            learnt_large_success_sub10_step3_source_pop_overwrite_deep_index4=0,
            learnt_large_success_sub10_step3_source_pop_overwrite_deep_index5_plus=0,
            learnt_large_success_sub10_step4=0,
            learnt_large_success_sub10_step5_plus=0,
            max_large_probe=0,
            analyze_reason_traversals=0,
            analyze_problem_reason_traversals=0,
            analyze_learnt_reason_traversals=0,
            analyze_problem_reason_distinct_clauses=0,
            max_analyze_problem_reason_clause_traversals=0,
            analyze_reason_buckets=(0, 0, 0, 0),
            minimize_reason_checks=0,
            minimize_problem_reason_checks=0,
            minimize_learnt_reason_checks=0,
            minimize_reason_kept_buckets=(0, 0, 0, 0),
            minimize_reason_removed_buckets=(0, 0, 0, 0),
            analyze_learnt_literal_appends=0,
            learnt_literals_before_min=0,
            learnt_literals_after_min=0,
            minimize_removed_literals=0,
            max_learnt_before=0,
            max_learnt_after=0,
            lbd_sum=0,
        )

    live_learnts = sum(1 for learnt_id in solver.learnt_ids if not solver.clauses[learnt_id].deleted)
    problem_ternary_clause_count = sum(
        1 for clause in solver.clauses if not clause.learnt and len(clause.lits) == 3
    )
    problem_ternary_literals: set[int] = set()
    for clause in solver.clauses:
        if clause.learnt or len(clause.lits) != 3:
            continue
        problem_ternary_literals.update(clause.lits)
    return RunStats(
        path=path,
        sat=sat,
        ok=ok,
        elapsed_s=elapsed_s,
        decisions=solver.decisions,
        decision_trail_appends=solver.decision_trail_appends,
        propagation_trail_appends=solver.propagation_trail_appends,
        branch_unassigned_sum=solver.branch_unassigned_sum,
        branch_zero_activity_unassigned_sum=solver.branch_zero_activity_unassigned_sum,
        branch_best_tie_sum=solver.branch_best_tie_sum,
        branch_multiway_best_ties=solver.branch_multiway_best_ties,
        branch_zero_activity_choices=solver.branch_zero_activity_choices,
        max_branch_unassigned=solver.max_branch_unassigned,
        max_branch_best_tie=solver.max_branch_best_tie,
        conflicts=solver.conflicts,
        processed_literals=solver.processed_literals,
        propagations=solver.propagations,
        restarts=solver.restarts,
        restart_conflict_sum=solver.restart_conflict_sum,
        max_restart_conflicts=solver.max_restart_conflicts,
        restart_decision_level_sum=solver.restart_decision_level_sum,
        max_restart_decision_level=solver.max_restart_decision_level,
        restart_trail_sum=solver.restart_trail_sum,
        max_restart_trail=solver.max_restart_trail,
        reductions=solver.reductions,
        reduction_live_learnts_sum=solver.reduction_live_learnts_sum,
        reduction_locked_clause_sum=solver.reduction_locked_clause_sum,
        reduction_candidate_clause_sum=solver.reduction_candidate_clause_sum,
        reduction_deleted_clause_sum=solver.reduction_deleted_clause_sum,
        max_reduction_live_learnts=solver.max_reduction_live_learnts,
        max_reduction_locked_clause_count=solver.max_reduction_locked_clause_count,
        max_reduction_candidate_clause_count=solver.max_reduction_candidate_clause_count,
        max_reduction_deleted_clause_count=solver.max_reduction_deleted_clause_count,
        learnts_added=solver.learnts_added,
        live_learnts=live_learnts,
        max_live_learnts=max(solver.max_live_learnts, live_learnts),
        max_trail=solver.max_trail,
        restart_base=restart_base,
        next_reduce=next_reduce,
        var_decay=var_decay,
        clause_decay=clause_decay,
        trail_limit_pushes=solver.trail_limit_pushes,
        trail_limit_pops=solver.trail_limit_pops,
        binary_clause_checks=solver.binary_clause_checks,
        binary_units=solver.binary_units,
        binary_conflicts=solver.binary_conflicts,
        watch_clause_visits=solver.watch_clause_visits,
        deleted_watch_skips=solver.deleted_watch_skips,
        ternary_watch_visits=solver.ternary_watch_visits,
        large_watch_visits=solver.large_watch_visits,
        large_watch_len4_visits=solver.large_watch_len4_visits,
        large_watch_len5_9_visits=solver.large_watch_len5_9_visits,
        large_watch_len10_plus_visits=solver.large_watch_len10_plus_visits,
        problem_ternary_watch_visits=solver.problem_ternary_watch_visits,
        learnt_ternary_watch_visits=solver.learnt_ternary_watch_visits,
        problem_large_watch_visits=solver.problem_large_watch_visits,
        learnt_large_watch_visits=solver.learnt_large_watch_visits,
        problem_ternary_watch_batches=solver.problem_ternary_watch_batches,
        problem_ternary_mixed_watch_batches=solver.problem_ternary_mixed_watch_batches,
        problem_ternary_batch_total_watchers=solver.problem_ternary_batch_total_watchers,
        problem_ternary_batch_problem_ternary_watchers=solver.problem_ternary_batch_problem_ternary_watchers,
        problem_ternary_batch_learnt_ternary_watchers=solver.problem_ternary_batch_learnt_ternary_watchers,
        problem_ternary_batch_problem_large_watchers=solver.problem_ternary_batch_problem_large_watchers,
        problem_ternary_batch_learnt_large_watchers=solver.problem_ternary_batch_learnt_large_watchers,
        problem_ternary_batch_deleted_watchers=solver.problem_ternary_batch_deleted_watchers,
        problem_ternary_satisfied_skips=solver.problem_ternary_satisfied_skips,
        learnt_ternary_satisfied_skips=solver.learnt_ternary_satisfied_skips,
        problem_large_satisfied_skips=solver.problem_large_satisfied_skips,
        learnt_large_satisfied_skips=solver.learnt_large_satisfied_skips,
        problem_ternary_normalized_relocations=solver.problem_ternary_normalized_relocations,
        learnt_ternary_normalized_relocations=solver.learnt_ternary_normalized_relocations,
        problem_ternary_normalized_units=solver.problem_ternary_normalized_units,
        learnt_ternary_normalized_units=solver.learnt_ternary_normalized_units,
        problem_ternary_normalized_conflicts=solver.problem_ternary_normalized_conflicts,
        learnt_ternary_normalized_conflicts=solver.learnt_ternary_normalized_conflicts,
        problem_ternary_true_relocations=solver.problem_ternary_true_relocations,
        problem_ternary_unassigned_relocations=solver.problem_ternary_unassigned_relocations,
        learnt_ternary_true_relocations=solver.learnt_ternary_true_relocations,
        learnt_ternary_unassigned_relocations=solver.learnt_ternary_unassigned_relocations,
        problem_ternary_units=solver.problem_ternary_units,
        learnt_ternary_units=solver.learnt_ternary_units,
        problem_ternary_conflicts=solver.problem_ternary_conflicts,
        learnt_ternary_conflicts=solver.learnt_ternary_conflicts,
        problem_ternary_false_other_relocations=solver.problem_ternary_false_other_relocations,
        problem_ternary_unassigned_other_relocations=solver.problem_ternary_unassigned_other_relocations,
        learnt_ternary_false_other_relocations=solver.learnt_ternary_false_other_relocations,
        learnt_ternary_unassigned_other_relocations=solver.learnt_ternary_unassigned_other_relocations,
        problem_ternary_clause_count=problem_ternary_clause_count,
        problem_ternary_distinct_clauses_visited=len(solver.problem_ternary_clause_visit_counts),
        max_problem_ternary_clause_visits=max(
            solver.problem_ternary_clause_visit_counts.values(),
            default=0,
        ),
        problem_ternary_literal_count=len(problem_ternary_literals),
        problem_ternary_distinct_trigger_literals=len(solver.problem_ternary_trigger_literal_counts),
        max_problem_ternary_trigger_literal_visits=max(
            solver.problem_ternary_trigger_literal_counts.values(),
            default=0,
        ),
        satisfied_watch_skips=solver.satisfied_watch_skips,
        watch_slot_normalizations=solver.watch_slot_normalizations,
        ternary_slot_normalizations=solver.ternary_slot_normalizations,
        large_slot_normalizations=solver.large_slot_normalizations,
        normalized_satisfied_skips=solver.normalized_satisfied_skips,
        watcher_list_appends=solver.watcher_list_appends,
        watcher_list_pops=solver.watcher_list_pops,
        deleted_ternary_watch_pops=solver.deleted_ternary_watch_pops,
        deleted_large_watch_pops=solver.deleted_large_watch_pops,
        problem_ternary_relocation_pops=solver.problem_ternary_relocation_pops,
        learnt_ternary_relocation_pops=solver.learnt_ternary_relocation_pops,
        problem_large_relocation_pops=solver.problem_large_relocation_pops,
        learnt_large_relocation_pops=solver.learnt_large_relocation_pops,
        watch_relocations=solver.watch_relocations,
        watch_units=solver.watch_units,
        watch_conflicts=solver.watch_conflicts,
        ternary_relocations=solver.ternary_relocations,
        ternary_units=solver.ternary_units,
        ternary_conflicts=solver.ternary_conflicts,
        large_relocations=solver.large_relocations,
        problem_large_relocations=solver.problem_large_relocations,
        learnt_large_relocations=solver.learnt_large_relocations,
        large_units=solver.large_units,
        problem_large_units=solver.problem_large_units,
        learnt_large_units=solver.learnt_large_units,
        large_conflicts=solver.large_conflicts,
        problem_large_conflicts=solver.problem_large_conflicts,
        learnt_large_conflicts=solver.learnt_large_conflicts,
        large_probe_steps=solver.large_probe_steps,
        large_probe_success_steps=solver.large_probe_success_steps,
        large_probe_failure_steps=solver.large_probe_failure_steps,
        large_probe_success_step1=solver.large_probe_success_step1,
        large_probe_success_step2=solver.large_probe_success_step2,
        large_probe_success_step3_4=solver.large_probe_success_step3_4,
        large_probe_success_step5_plus=solver.large_probe_success_step5_plus,
        learnt_large_success_len10_plus_step1_2=solver.learnt_large_success_len10_plus_step1_2,
        learnt_large_success_len10_plus_step3_plus=solver.learnt_large_success_len10_plus_step3_plus,
        learnt_large_success_sub10_step1_2=solver.learnt_large_success_sub10_step1_2,
        learnt_large_success_sub10_step3_plus=solver.learnt_large_success_sub10_step3_plus,
        learnt_large_success_sub10_step3_4=solver.learnt_large_success_sub10_step3_4,
        learnt_large_success_sub10_step3=solver.learnt_large_success_sub10_step3,
        learnt_large_success_sub10_step3_source_pop_last_slot=(
            solver.learnt_large_success_sub10_step3_source_pop_last_slot
        ),
        learnt_large_success_sub10_step3_source_pop_overwrite=(
            solver.learnt_large_success_sub10_step3_source_pop_overwrite
        ),
        learnt_large_success_sub10_step3_source_pop_overwrite_shallow=(
            solver.learnt_large_success_sub10_step3_source_pop_overwrite_shallow
        ),
        learnt_large_success_sub10_step3_source_pop_overwrite_deep=(
            solver.learnt_large_success_sub10_step3_source_pop_overwrite_deep
        ),
        learnt_large_success_sub10_step3_source_pop_overwrite_deep_index2=(
            solver.learnt_large_success_sub10_step3_source_pop_overwrite_deep_index2
        ),
        learnt_large_success_sub10_step3_source_pop_overwrite_deep_index3_plus=(
            solver.learnt_large_success_sub10_step3_source_pop_overwrite_deep_index3_plus
        ),
        learnt_large_success_sub10_step3_source_pop_overwrite_deep_index3=(
            solver.learnt_large_success_sub10_step3_source_pop_overwrite_deep_index3
        ),
        learnt_large_success_sub10_step3_source_pop_overwrite_deep_index4_plus=(
            solver.learnt_large_success_sub10_step3_source_pop_overwrite_deep_index4_plus
        ),
        learnt_large_success_sub10_step3_source_pop_overwrite_deep_index4=(
            solver.learnt_large_success_sub10_step3_source_pop_overwrite_deep_index4
        ),
        learnt_large_success_sub10_step3_source_pop_overwrite_deep_index5_plus=(
            solver.learnt_large_success_sub10_step3_source_pop_overwrite_deep_index5_plus
        ),
        learnt_large_success_sub10_step4=solver.learnt_large_success_sub10_step4,
        learnt_large_success_sub10_step5_plus=solver.learnt_large_success_sub10_step5_plus,
        max_large_probe=solver.max_large_probe,
        analyze_reason_traversals=solver.analyze_reason_traversals,
        analyze_problem_reason_traversals=solver.analyze_problem_reason_traversals,
        analyze_learnt_reason_traversals=solver.analyze_learnt_reason_traversals,
        analyze_problem_reason_distinct_clauses=len(solver.problem_reason_clause_traversal_counts),
        max_analyze_problem_reason_clause_traversals=max(
            solver.problem_reason_clause_traversal_counts.values(),
            default=0,
        ),
        analyze_reason_buckets=tuple(solver.analyze_reason_buckets),
        minimize_reason_checks=solver.minimize_reason_checks,
        minimize_problem_reason_checks=solver.minimize_problem_reason_checks,
        minimize_learnt_reason_checks=solver.minimize_learnt_reason_checks,
        minimize_reason_kept_buckets=tuple(solver.minimize_reason_kept_buckets),
        minimize_reason_removed_buckets=tuple(solver.minimize_reason_removed_buckets),
        analyze_learnt_literal_appends=solver.analyze_learnt_literal_appends,
        learnt_literals_before_min=solver.learnt_literals_before_min,
        learnt_literals_after_min=solver.learnt_literals_after_min,
        minimize_removed_literals=solver.minimize_removed_literals,
        max_learnt_before=solver.max_learnt_before,
        max_learnt_after=solver.max_learnt_after,
        lbd_sum=solver.lbd_sum,
    )


def solve_with_profile(
    path: str,
    *,
    restart_base: int,
    next_reduce: int,
    var_decay: float,
    clause_decay: float,
) -> RunStats:
    num_vars, clauses = satsolver.parse_dimacs_file(path)

    if satsolver.has_pigeonhole_core(clauses):
        return build_run_stats(
            path,
            None,
            sat=False,
            ok=True,
            elapsed_s=0.0,
            restart_base=restart_base,
            next_reduce=next_reduce,
            var_decay=var_decay,
            clause_decay=clause_decay,
        )

    if satsolver.xor_system_unsat(num_vars, clauses):
        return build_run_stats(
            path,
            None,
            sat=False,
            ok=True,
            elapsed_s=0.0,
            restart_base=restart_base,
            next_reduce=next_reduce,
            var_decay=var_decay,
            clause_decay=clause_decay,
        )

    solver = ProfiledSolver(
        num_vars,
        restart_base=restart_base,
        next_reduce=next_reduce,
        var_decay=var_decay,
        clause_decay=clause_decay,
    )
    root_pure_literals = satsolver.find_iterative_root_pure_literals(num_vars, clauses)
    if len(root_pure_literals) >= satsolver.ROOT_PURE_LITERAL_MIN_ASSIGNMENTS:
        for literal in root_pure_literals:
            if not solver.enqueue(literal, None):
                return build_run_stats(
                    path,
                    solver,
                    sat=False,
                    ok=True,
                    elapsed_s=0.0,
                    restart_base=restart_base,
                    next_reduce=next_reduce,
                    var_decay=var_decay,
                    clause_decay=clause_decay,
                )
    for clause in clauses:
        if not solver.add_problem_clause(clause):
            return build_run_stats(
                path,
                solver,
                sat=False,
                ok=True,
                elapsed_s=0.0,
                restart_base=restart_base,
                next_reduce=next_reduce,
                var_decay=var_decay,
                clause_decay=clause_decay,
            )

    start = perf_counter()
    model = solver.solve()
    elapsed = perf_counter() - start
    ok = (model is None) or satsolver.model_satisfies(clauses, model)
    return build_run_stats(
        path,
        solver,
        sat=model is not None,
        ok=ok,
        elapsed_s=elapsed,
        restart_base=restart_base,
        next_reduce=next_reduce,
        var_decay=var_decay,
        clause_decay=clause_decay,
    )


def main() -> int:
    parser = argparse.ArgumentParser(description="Profile satsolver.py on selected CNF files.")
    parser.add_argument("paths", nargs="+", help="DIMACS CNF files to solve")
    parser.add_argument("--restart-base", type=int, default=64)
    parser.add_argument("--next-reduce", type=int, default=256)
    parser.add_argument("--var-decay", type=float, default=0.95)
    parser.add_argument("--clause-decay", type=float, default=0.999)
    args = parser.parse_args()

    for path in args.paths:
        stats = solve_with_profile(
            path,
            restart_base=args.restart_base,
            next_reduce=args.next_reduce,
            var_decay=args.var_decay,
            clause_decay=args.clause_decay,
        )
        status = "SAT" if stats.sat else "UNSAT"
        avg_learnt_before = (
            stats.learnt_literals_before_min / stats.conflicts if stats.conflicts else 0.0
        )
        avg_learnt_after = (
            stats.learnt_literals_after_min / stats.conflicts if stats.conflicts else 0.0
        )
        avg_branch_unassigned = (
            stats.branch_unassigned_sum / stats.decisions if stats.decisions else 0.0
        )
        avg_branch_zero_activity_unassigned = (
            stats.branch_zero_activity_unassigned_sum / stats.decisions if stats.decisions else 0.0
        )
        avg_branch_best_tie = (
            stats.branch_best_tie_sum / stats.decisions if stats.decisions else 0.0
        )
        avg_propagation_trail_appends = (
            stats.propagation_trail_appends / stats.propagations if stats.propagations else 0.0
        )
        avg_analyze_learnt_literal_appends = (
            stats.analyze_learnt_literal_appends / stats.conflicts if stats.conflicts else 0.0
        )
        watch_pop_share = (
            stats.watcher_list_pops / (stats.watcher_list_pops + stats.trail_limit_pops)
            if (stats.watcher_list_pops + stats.trail_limit_pops)
            else 0.0
        )
        deleted_watch_pop_share = (
            (stats.deleted_ternary_watch_pops + stats.deleted_large_watch_pops) / stats.watcher_list_pops
            if stats.watcher_list_pops
            else 0.0
        )
        problem_ternary_relocation_pop_share = (
            stats.problem_ternary_relocation_pops / stats.watcher_list_pops
            if stats.watcher_list_pops
            else 0.0
        )
        learnt_ternary_relocation_pop_share = (
            stats.learnt_ternary_relocation_pops / stats.watcher_list_pops
            if stats.watcher_list_pops
            else 0.0
        )
        problem_large_relocation_pop_share = (
            stats.problem_large_relocation_pops / stats.watcher_list_pops
            if stats.watcher_list_pops
            else 0.0
        )
        learnt_large_relocation_pop_share = (
            stats.learnt_large_relocation_pops / stats.watcher_list_pops
            if stats.watcher_list_pops
            else 0.0
        )
        branch_multiway_best_tie_share = (
            stats.branch_multiway_best_ties / stats.decisions if stats.decisions else 0.0
        )
        branch_zero_activity_choice_share = (
            stats.branch_zero_activity_choices / stats.decisions if stats.decisions else 0.0
        )
        avg_lbd = stats.lbd_sum / stats.conflicts if stats.conflicts else 0.0
        avg_conflicts_per_restart = (
            stats.restart_conflict_sum / stats.restarts if stats.restarts else 0.0
        )
        avg_restart_decision_level = (
            stats.restart_decision_level_sum / stats.restarts if stats.restarts else 0.0
        )
        avg_restart_trail = (
            stats.restart_trail_sum / stats.restarts if stats.restarts else 0.0
        )
        avg_live_learnts_per_reduction = (
            stats.reduction_live_learnts_sum / stats.reductions if stats.reductions else 0.0
        )
        avg_locked_clauses_per_reduction = (
            stats.reduction_locked_clause_sum / stats.reductions if stats.reductions else 0.0
        )
        avg_candidate_clauses_per_reduction = (
            stats.reduction_candidate_clause_sum / stats.reductions if stats.reductions else 0.0
        )
        avg_deleted_clauses_per_reduction = (
            stats.reduction_deleted_clause_sum / stats.reductions if stats.reductions else 0.0
        )
        avg_large_probe = stats.large_probe_steps / stats.large_watch_visits if stats.large_watch_visits else 0.0
        avg_large_probe_success = (
            stats.large_probe_success_steps / stats.large_relocations if stats.large_relocations else 0.0
        )
        large_failures = stats.large_units + stats.large_conflicts
        avg_large_probe_failure = (
            stats.large_probe_failure_steps / large_failures if large_failures else 0.0
        )
        large_probe_success_step1_share = (
            stats.large_probe_success_step1 / stats.large_relocations if stats.large_relocations else 0.0
        )
        large_probe_success_step2_share = (
            stats.large_probe_success_step2 / stats.large_relocations if stats.large_relocations else 0.0
        )
        large_probe_success_step3_4_share = (
            stats.large_probe_success_step3_4 / stats.large_relocations if stats.large_relocations else 0.0
        )
        large_probe_success_step5_plus_share = (
            stats.large_probe_success_step5_plus / stats.large_relocations
            if stats.large_relocations
            else 0.0
        )
        learnt_large_success_len10_plus_step1_2_share = (
            stats.learnt_large_success_len10_plus_step1_2 / stats.learnt_large_relocations
            if stats.learnt_large_relocations
            else 0.0
        )
        learnt_large_success_len10_plus_step3_plus_share = (
            stats.learnt_large_success_len10_plus_step3_plus / stats.learnt_large_relocations
            if stats.learnt_large_relocations
            else 0.0
        )
        learnt_large_success_sub10_step1_2_share = (
            stats.learnt_large_success_sub10_step1_2 / stats.learnt_large_relocations
            if stats.learnt_large_relocations
            else 0.0
        )
        learnt_large_success_sub10_step3_plus_share = (
            stats.learnt_large_success_sub10_step3_plus / stats.learnt_large_relocations
            if stats.learnt_large_relocations
            else 0.0
        )
        learnt_large_success_sub10_step3_4_share = (
            stats.learnt_large_success_sub10_step3_4 / stats.learnt_large_success_sub10_step3_plus
            if stats.learnt_large_success_sub10_step3_plus
            else 0.0
        )
        learnt_large_success_sub10_step5_plus_share = (
            stats.learnt_large_success_sub10_step5_plus / stats.learnt_large_success_sub10_step3_plus
            if stats.learnt_large_success_sub10_step3_plus
            else 0.0
        )
        learnt_large_success_sub10_step3_share = (
            stats.learnt_large_success_sub10_step3 / stats.learnt_large_success_sub10_step3_4
            if stats.learnt_large_success_sub10_step3_4
            else 0.0
        )
        learnt_large_success_sub10_step3_source_pop_last_slot_share = (
            stats.learnt_large_success_sub10_step3_source_pop_last_slot
            / stats.learnt_large_success_sub10_step3
            if stats.learnt_large_success_sub10_step3
            else 0.0
        )
        learnt_large_success_sub10_step3_source_pop_overwrite_share = (
            stats.learnt_large_success_sub10_step3_source_pop_overwrite
            / stats.learnt_large_success_sub10_step3
            if stats.learnt_large_success_sub10_step3
            else 0.0
        )
        learnt_large_success_sub10_step3_source_pop_overwrite_shallow_share = (
            stats.learnt_large_success_sub10_step3_source_pop_overwrite_shallow
            / stats.learnt_large_success_sub10_step3_source_pop_overwrite
            if stats.learnt_large_success_sub10_step3_source_pop_overwrite
            else 0.0
        )
        learnt_large_success_sub10_step3_source_pop_overwrite_deep_share = (
            stats.learnt_large_success_sub10_step3_source_pop_overwrite_deep
            / stats.learnt_large_success_sub10_step3_source_pop_overwrite
            if stats.learnt_large_success_sub10_step3_source_pop_overwrite
            else 0.0
        )
        learnt_large_success_sub10_step3_source_pop_overwrite_deep_index2_share = (
            stats.learnt_large_success_sub10_step3_source_pop_overwrite_deep_index2
            / stats.learnt_large_success_sub10_step3_source_pop_overwrite_deep
            if stats.learnt_large_success_sub10_step3_source_pop_overwrite_deep
            else 0.0
        )
        learnt_large_success_sub10_step3_source_pop_overwrite_deep_index3_plus_share = (
            stats.learnt_large_success_sub10_step3_source_pop_overwrite_deep_index3_plus
            / stats.learnt_large_success_sub10_step3_source_pop_overwrite_deep
            if stats.learnt_large_success_sub10_step3_source_pop_overwrite_deep
            else 0.0
        )
        learnt_large_success_sub10_step3_source_pop_overwrite_deep_index3_share = (
            stats.learnt_large_success_sub10_step3_source_pop_overwrite_deep_index3
            / stats.learnt_large_success_sub10_step3_source_pop_overwrite_deep_index3_plus
            if stats.learnt_large_success_sub10_step3_source_pop_overwrite_deep_index3_plus
            else 0.0
        )
        learnt_large_success_sub10_step3_source_pop_overwrite_deep_index4_plus_share = (
            stats.learnt_large_success_sub10_step3_source_pop_overwrite_deep_index4_plus
            / stats.learnt_large_success_sub10_step3_source_pop_overwrite_deep_index3_plus
            if stats.learnt_large_success_sub10_step3_source_pop_overwrite_deep_index3_plus
            else 0.0
        )
        learnt_large_success_sub10_step3_source_pop_overwrite_deep_index4_share = (
            stats.learnt_large_success_sub10_step3_source_pop_overwrite_deep_index4
            / stats.learnt_large_success_sub10_step3_source_pop_overwrite_deep_index4_plus
            if stats.learnt_large_success_sub10_step3_source_pop_overwrite_deep_index4_plus
            else 0.0
        )
        learnt_large_success_sub10_step3_source_pop_overwrite_deep_index5_plus_share = (
            stats.learnt_large_success_sub10_step3_source_pop_overwrite_deep_index5_plus
            / stats.learnt_large_success_sub10_step3_source_pop_overwrite_deep_index4_plus
            if stats.learnt_large_success_sub10_step3_source_pop_overwrite_deep_index4_plus
            else 0.0
        )
        learnt_large_success_sub10_step4_share = (
            stats.learnt_large_success_sub10_step4 / stats.learnt_large_success_sub10_step3_4
            if stats.learnt_large_success_sub10_step3_4
            else 0.0
        )
        large_len4_share = (
            stats.large_watch_len4_visits / stats.large_watch_visits if stats.large_watch_visits else 0.0
        )
        large_len5_9_share = (
            stats.large_watch_len5_9_visits / stats.large_watch_visits if stats.large_watch_visits else 0.0
        )
        large_len10_plus_share = (
            stats.large_watch_len10_plus_visits / stats.large_watch_visits
            if stats.large_watch_visits
            else 0.0
        )
        problem_ternary_clause_coverage = (
            stats.problem_ternary_distinct_clauses_visited / stats.problem_ternary_clause_count
            if stats.problem_ternary_clause_count
            else 0.0
        )
        problem_ternary_trigger_total = (
            stats.problem_ternary_satisfied_skips + stats.problem_ternary_watch_visits
        )
        learnt_ternary_trigger_total = (
            stats.learnt_ternary_satisfied_skips + stats.learnt_ternary_watch_visits
        )
        problem_ternary_relocation_total = (
            stats.problem_ternary_true_relocations + stats.problem_ternary_unassigned_relocations
        )
        learnt_ternary_relocation_total = (
            stats.learnt_ternary_true_relocations + stats.learnt_ternary_unassigned_relocations
        )
        problem_ternary_satisfied_skip_share = (
            stats.problem_ternary_satisfied_skips / problem_ternary_trigger_total
            if problem_ternary_trigger_total
            else 0.0
        )
        learnt_ternary_satisfied_skip_share = (
            stats.learnt_ternary_satisfied_skips / learnt_ternary_trigger_total
            if learnt_ternary_trigger_total
            else 0.0
        )
        problem_ternary_relocation_share = (
            problem_ternary_relocation_total / stats.problem_ternary_watch_visits
            if stats.problem_ternary_watch_visits
            else 0.0
        )
        problem_ternary_unit_share = (
            stats.problem_ternary_units / stats.problem_ternary_watch_visits
            if stats.problem_ternary_watch_visits
            else 0.0
        )
        problem_ternary_conflict_share = (
            stats.problem_ternary_conflicts / stats.problem_ternary_watch_visits
            if stats.problem_ternary_watch_visits
            else 0.0
        )
        learnt_ternary_relocation_share = (
            learnt_ternary_relocation_total / stats.learnt_ternary_watch_visits
            if stats.learnt_ternary_watch_visits
            else 0.0
        )
        problem_ternary_normalized_relocation_share = (
            stats.problem_ternary_normalized_relocations / problem_ternary_relocation_total
            if problem_ternary_relocation_total
            else 0.0
        )
        learnt_ternary_unit_share = (
            stats.learnt_ternary_units / stats.learnt_ternary_watch_visits
            if stats.learnt_ternary_watch_visits
            else 0.0
        )
        problem_ternary_normalized_unit_share = (
            stats.problem_ternary_normalized_units / stats.problem_ternary_units
            if stats.problem_ternary_units
            else 0.0
        )
        learnt_ternary_conflict_share = (
            stats.learnt_ternary_conflicts / stats.learnt_ternary_watch_visits
            if stats.learnt_ternary_watch_visits
            else 0.0
        )
        problem_ternary_normalized_conflict_share = (
            stats.problem_ternary_normalized_conflicts / stats.problem_ternary_conflicts
            if stats.problem_ternary_conflicts
            else 0.0
        )
        learnt_ternary_normalized_relocation_share = (
            stats.learnt_ternary_normalized_relocations / learnt_ternary_relocation_total
            if learnt_ternary_relocation_total
            else 0.0
        )
        learnt_ternary_normalized_unit_share = (
            stats.learnt_ternary_normalized_units / stats.learnt_ternary_units
            if stats.learnt_ternary_units
            else 0.0
        )
        learnt_ternary_normalized_conflict_share = (
            stats.learnt_ternary_normalized_conflicts / stats.learnt_ternary_conflicts
            if stats.learnt_ternary_conflicts
            else 0.0
        )
        problem_ternary_hot_share = (
            stats.max_problem_ternary_clause_visits / stats.problem_ternary_watch_visits
            if stats.problem_ternary_watch_visits
            else 0.0
        )
        problem_ternary_literal_coverage = (
            stats.problem_ternary_distinct_trigger_literals / stats.problem_ternary_literal_count
            if stats.problem_ternary_literal_count
            else 0.0
        )
        problem_ternary_trigger_hot_share = (
            stats.max_problem_ternary_trigger_literal_visits / stats.problem_ternary_watch_visits
            if stats.problem_ternary_watch_visits
            else 0.0
        )
        problem_ternary_mixed_batch_share = (
            stats.problem_ternary_mixed_watch_batches / stats.problem_ternary_watch_batches
            if stats.problem_ternary_watch_batches
            else 0.0
        )
        avg_problem_ternary_batch_size = (
            stats.problem_ternary_batch_total_watchers / stats.problem_ternary_watch_batches
            if stats.problem_ternary_watch_batches
            else 0.0
        )
        avg_problem_ternary_batch_other_watchers = (
            (
                stats.problem_ternary_batch_total_watchers
                - stats.problem_ternary_batch_problem_ternary_watchers
            )
            / stats.problem_ternary_watch_batches
            if stats.problem_ternary_watch_batches
            else 0.0
        )
        problem_ternary_batch_learnt_large_share = (
            stats.problem_ternary_batch_learnt_large_watchers
            / stats.problem_ternary_batch_total_watchers
            if stats.problem_ternary_batch_total_watchers
            else 0.0
        )
        total_ternary_relocations = (
            stats.problem_ternary_true_relocations
            + stats.problem_ternary_unassigned_relocations
            + stats.learnt_ternary_true_relocations
            + stats.learnt_ternary_unassigned_relocations
        )
        ternary_true_relocation_share = (
            (stats.problem_ternary_true_relocations + stats.learnt_ternary_true_relocations)
            / total_ternary_relocations
            if total_ternary_relocations
            else 0.0
        )
        ternary_false_other_relocation_share = (
            (stats.problem_ternary_false_other_relocations + stats.learnt_ternary_false_other_relocations)
            / total_ternary_relocations
            if total_ternary_relocations
            else 0.0
        )
        analyze_problem_reason_hot_share = (
            stats.max_analyze_problem_reason_clause_traversals
            / stats.analyze_problem_reason_traversals
            if stats.analyze_problem_reason_traversals
            else 0.0
        )
        analyze_2, analyze_3, analyze_4_9, analyze_10_plus = stats.analyze_reason_buckets
        kept_2, kept_3, kept_4_9, kept_10_plus = stats.minimize_reason_kept_buckets
        removed_2, removed_3, removed_4_9, removed_10_plus = stats.minimize_reason_removed_buckets
        print(
            (
                f"{path}: {status} ok={stats.ok} time={stats.elapsed_s:.4f}s "
                f"decisions={stats.decisions} conflicts={stats.conflicts} "
                f"avg_branch_unassigned={avg_branch_unassigned:.2f} "
                f"avg_branch_zero_activity_unassigned={avg_branch_zero_activity_unassigned:.2f} "
                f"avg_branch_best_tie={avg_branch_best_tie:.2f} "
                f"decision_trail_appends={stats.decision_trail_appends} "
                f"propagation_trail_appends={stats.propagation_trail_appends} "
                f"avg_propagation_trail_appends={avg_propagation_trail_appends:.2f} "
                f"trail_limit_pushes={stats.trail_limit_pushes} trail_limit_pops={stats.trail_limit_pops} "
                f"branch_multiway_best_ties={stats.branch_multiway_best_ties} "
                f"branch_multiway_best_tie_share={branch_multiway_best_tie_share:.4f} "
                f"branch_zero_activity_choices={stats.branch_zero_activity_choices} "
                f"branch_zero_activity_choice_share={branch_zero_activity_choice_share:.4f} "
                f"max_branch_unassigned={stats.max_branch_unassigned} "
                f"max_branch_best_tie={stats.max_branch_best_tie} "
                f"processed_literals={stats.processed_literals} propagations={stats.propagations} "
                f"restarts={stats.restarts} avg_conflicts_per_restart={avg_conflicts_per_restart:.2f} "
                f"avg_restart_decision_level={avg_restart_decision_level:.2f} "
                f"avg_restart_trail={avg_restart_trail:.2f} "
                f"max_restart_conflicts={stats.max_restart_conflicts} "
                f"max_restart_decision_level={stats.max_restart_decision_level} "
                f"max_restart_trail={stats.max_restart_trail} "
                f"reductions={stats.reductions} "
                f"avg_live_learnts_per_reduction={avg_live_learnts_per_reduction:.2f} "
                f"avg_locked_clauses_per_reduction={avg_locked_clauses_per_reduction:.2f} "
                f"avg_candidate_clauses_per_reduction={avg_candidate_clauses_per_reduction:.2f} "
                f"avg_deleted_clauses_per_reduction={avg_deleted_clauses_per_reduction:.2f} "
                f"max_reduction_live_learnts={stats.max_reduction_live_learnts} "
                f"max_reduction_locked_clauses={stats.max_reduction_locked_clause_count} "
                f"max_reduction_candidates={stats.max_reduction_candidate_clause_count} "
                f"max_reduction_deleted={stats.max_reduction_deleted_clause_count} "
                f"learnts_added={stats.learnts_added} live_learnts={stats.live_learnts} "
                f"max_live_learnts={stats.max_live_learnts} max_trail={stats.max_trail} "
                f"binary_checks={stats.binary_clause_checks} binary_units={stats.binary_units} "
                f"binary_conflicts={stats.binary_conflicts} watch_visits={stats.watch_clause_visits} "
                f"ternary_visits={stats.ternary_watch_visits} large_visits={stats.large_watch_visits} "
                f"large_len4_visits={stats.large_watch_len4_visits} "
                f"large_len5_9_visits={stats.large_watch_len5_9_visits} "
                f"large_len10_plus_visits={stats.large_watch_len10_plus_visits} "
                f"large_len4_share={large_len4_share:.4f} "
                f"large_len5_9_share={large_len5_9_share:.4f} "
                f"large_len10_plus_share={large_len10_plus_share:.4f} "
                f"problem_ternary_visits={stats.problem_ternary_watch_visits} "
                f"learnt_ternary_visits={stats.learnt_ternary_watch_visits} "
                f"problem_large_visits={stats.problem_large_watch_visits} "
                f"learnt_large_visits={stats.learnt_large_watch_visits} "
                f"problem_ternary_satisfied_skips={stats.problem_ternary_satisfied_skips} "
                f"learnt_ternary_satisfied_skips={stats.learnt_ternary_satisfied_skips} "
                f"problem_large_satisfied_skips={stats.problem_large_satisfied_skips} "
                f"learnt_large_satisfied_skips={stats.learnt_large_satisfied_skips} "
                f"problem_ternary_satisfied_skip_share={problem_ternary_satisfied_skip_share:.4f} "
                f"learnt_ternary_satisfied_skip_share={learnt_ternary_satisfied_skip_share:.4f} "
                f"problem_ternary_true_relocations={stats.problem_ternary_true_relocations} "
                f"problem_ternary_unassigned_relocations={stats.problem_ternary_unassigned_relocations} "
                f"learnt_ternary_true_relocations={stats.learnt_ternary_true_relocations} "
                f"learnt_ternary_unassigned_relocations={stats.learnt_ternary_unassigned_relocations} "
                f"problem_ternary_normalized_relocations={stats.problem_ternary_normalized_relocations} "
                f"learnt_ternary_normalized_relocations={stats.learnt_ternary_normalized_relocations} "
                f"problem_ternary_units={stats.problem_ternary_units} "
                f"learnt_ternary_units={stats.learnt_ternary_units} "
                f"problem_ternary_normalized_units={stats.problem_ternary_normalized_units} "
                f"learnt_ternary_normalized_units={stats.learnt_ternary_normalized_units} "
                f"problem_ternary_conflicts={stats.problem_ternary_conflicts} "
                f"learnt_ternary_conflicts={stats.learnt_ternary_conflicts} "
                f"problem_ternary_normalized_conflicts={stats.problem_ternary_normalized_conflicts} "
                f"learnt_ternary_normalized_conflicts={stats.learnt_ternary_normalized_conflicts} "
                f"problem_ternary_relocation_share={problem_ternary_relocation_share:.4f} "
                f"problem_ternary_unit_share={problem_ternary_unit_share:.4f} "
                f"problem_ternary_conflict_share={problem_ternary_conflict_share:.4f} "
                f"problem_ternary_normalized_relocation_share={problem_ternary_normalized_relocation_share:.4f} "
                f"problem_ternary_normalized_unit_share={problem_ternary_normalized_unit_share:.4f} "
                f"problem_ternary_normalized_conflict_share={problem_ternary_normalized_conflict_share:.4f} "
                f"learnt_ternary_relocation_share={learnt_ternary_relocation_share:.4f} "
                f"learnt_ternary_unit_share={learnt_ternary_unit_share:.4f} "
                f"learnt_ternary_conflict_share={learnt_ternary_conflict_share:.4f} "
                f"learnt_ternary_normalized_relocation_share={learnt_ternary_normalized_relocation_share:.4f} "
                f"learnt_ternary_normalized_unit_share={learnt_ternary_normalized_unit_share:.4f} "
                f"learnt_ternary_normalized_conflict_share={learnt_ternary_normalized_conflict_share:.4f} "
                f"ternary_true_relocation_share={ternary_true_relocation_share:.4f} "
                f"problem_ternary_false_other_relocations={stats.problem_ternary_false_other_relocations} "
                f"problem_ternary_unassigned_other_relocations={stats.problem_ternary_unassigned_other_relocations} "
                f"learnt_ternary_false_other_relocations={stats.learnt_ternary_false_other_relocations} "
                f"learnt_ternary_unassigned_other_relocations={stats.learnt_ternary_unassigned_other_relocations} "
                f"ternary_false_other_relocation_share={ternary_false_other_relocation_share:.4f} "
                f"problem_ternary_clauses={stats.problem_ternary_clause_count} "
                f"problem_ternary_distinct={stats.problem_ternary_distinct_clauses_visited} "
                f"problem_ternary_clause_coverage={problem_ternary_clause_coverage:.3f} "
                f"max_problem_ternary_clause_visits={stats.max_problem_ternary_clause_visits} "
                f"problem_ternary_hot_share={problem_ternary_hot_share:.4f} "
                f"problem_ternary_literals={stats.problem_ternary_literal_count} "
                f"problem_ternary_trigger_literals={stats.problem_ternary_distinct_trigger_literals} "
                f"problem_ternary_literal_coverage={problem_ternary_literal_coverage:.3f} "
                f"max_problem_ternary_trigger_literal_visits={stats.max_problem_ternary_trigger_literal_visits} "
                f"problem_ternary_trigger_hot_share={problem_ternary_trigger_hot_share:.4f} "
                f"problem_ternary_watch_batches={stats.problem_ternary_watch_batches} "
                f"problem_ternary_mixed_watch_batches={stats.problem_ternary_mixed_watch_batches} "
                f"problem_ternary_mixed_batch_share={problem_ternary_mixed_batch_share:.4f} "
                f"avg_problem_ternary_batch_size={avg_problem_ternary_batch_size:.2f} "
                f"avg_problem_ternary_batch_other_watchers={avg_problem_ternary_batch_other_watchers:.2f} "
                f"problem_ternary_batch_problem_watchers={stats.problem_ternary_batch_problem_ternary_watchers} "
                f"problem_ternary_batch_learnt_ternary_watchers={stats.problem_ternary_batch_learnt_ternary_watchers} "
                f"problem_ternary_batch_problem_large_watchers={stats.problem_ternary_batch_problem_large_watchers} "
                f"problem_ternary_batch_learnt_large_watchers={stats.problem_ternary_batch_learnt_large_watchers} "
                f"problem_ternary_batch_deleted_watchers={stats.problem_ternary_batch_deleted_watchers} "
                f"problem_ternary_batch_learnt_large_share={problem_ternary_batch_learnt_large_share:.4f} "
                f"deleted_watch_skips={stats.deleted_watch_skips} satisfied_skips={stats.satisfied_watch_skips} "
                f"watch_normalizations={stats.watch_slot_normalizations} "
                f"ternary_normalizations={stats.ternary_slot_normalizations} "
                f"large_normalizations={stats.large_slot_normalizations} "
                f"normalized_satisfied_skips={stats.normalized_satisfied_skips} "
                f"watcher_list_appends={stats.watcher_list_appends} "
                f"watcher_list_pops={stats.watcher_list_pops} "
                f"deleted_ternary_watch_pops={stats.deleted_ternary_watch_pops} "
                f"deleted_large_watch_pops={stats.deleted_large_watch_pops} "
                f"problem_ternary_relocation_pops={stats.problem_ternary_relocation_pops} "
                f"learnt_ternary_relocation_pops={stats.learnt_ternary_relocation_pops} "
                f"problem_large_relocation_pops={stats.problem_large_relocation_pops} "
                f"learnt_large_relocation_pops={stats.learnt_large_relocation_pops} "
                f"watch_pop_share={watch_pop_share:.4f} "
                f"deleted_watch_pop_share={deleted_watch_pop_share:.4f} "
                f"problem_ternary_relocation_pop_share={problem_ternary_relocation_pop_share:.4f} "
                f"learnt_ternary_relocation_pop_share={learnt_ternary_relocation_pop_share:.4f} "
                f"problem_large_relocation_pop_share={problem_large_relocation_pop_share:.4f} "
                f"learnt_large_relocation_pop_share={learnt_large_relocation_pop_share:.4f} "
                f"watch_relocations={stats.watch_relocations} watch_units={stats.watch_units} "
                f"watch_conflicts={stats.watch_conflicts} ternary_relocations={stats.ternary_relocations} "
                f"ternary_units={stats.ternary_units} ternary_conflicts={stats.ternary_conflicts} "
                f"large_relocations={stats.large_relocations} "
                f"problem_large_relocations={stats.problem_large_relocations} "
                f"learnt_large_relocations={stats.learnt_large_relocations} "
                f"large_units={stats.large_units} problem_large_units={stats.problem_large_units} "
                f"learnt_large_units={stats.learnt_large_units} "
                f"large_conflicts={stats.large_conflicts} "
                f"problem_large_conflicts={stats.problem_large_conflicts} "
                f"learnt_large_conflicts={stats.learnt_large_conflicts} "
                f"avg_large_probe={avg_large_probe:.2f} "
                f"avg_large_probe_success={avg_large_probe_success:.2f} "
                f"avg_large_probe_failure={avg_large_probe_failure:.2f} "
                f"large_probe_success_step1={stats.large_probe_success_step1} "
                f"large_probe_success_step2={stats.large_probe_success_step2} "
                f"large_probe_success_step3_4={stats.large_probe_success_step3_4} "
                f"large_probe_success_step5_plus={stats.large_probe_success_step5_plus} "
                f"large_probe_success_step1_share={large_probe_success_step1_share:.4f} "
                f"large_probe_success_step2_share={large_probe_success_step2_share:.4f} "
                f"large_probe_success_step3_4_share={large_probe_success_step3_4_share:.4f} "
                f"large_probe_success_step5_plus_share={large_probe_success_step5_plus_share:.4f} "
                f"learnt_large_success_len10_plus_step1_2={stats.learnt_large_success_len10_plus_step1_2} "
                f"learnt_large_success_len10_plus_step3_plus={stats.learnt_large_success_len10_plus_step3_plus} "
                f"learnt_large_success_sub10_step1_2={stats.learnt_large_success_sub10_step1_2} "
                f"learnt_large_success_sub10_step3_plus={stats.learnt_large_success_sub10_step3_plus} "
                f"learnt_large_success_len10_plus_step1_2_share={learnt_large_success_len10_plus_step1_2_share:.4f} "
                f"learnt_large_success_len10_plus_step3_plus_share={learnt_large_success_len10_plus_step3_plus_share:.4f} "
                f"learnt_large_success_sub10_step1_2_share={learnt_large_success_sub10_step1_2_share:.4f} "
                f"learnt_large_success_sub10_step3_plus_share={learnt_large_success_sub10_step3_plus_share:.4f} "
                f"learnt_large_success_sub10_step3_4={stats.learnt_large_success_sub10_step3_4} "
                f"learnt_large_success_sub10_step3={stats.learnt_large_success_sub10_step3} "
                f"learnt_large_success_sub10_step3_source_pop_last_slot="
                f"{stats.learnt_large_success_sub10_step3_source_pop_last_slot} "
                f"learnt_large_success_sub10_step3_source_pop_overwrite="
                f"{stats.learnt_large_success_sub10_step3_source_pop_overwrite} "
                f"learnt_large_success_sub10_step3_source_pop_overwrite_shallow="
                f"{stats.learnt_large_success_sub10_step3_source_pop_overwrite_shallow} "
                f"learnt_large_success_sub10_step3_source_pop_overwrite_deep="
                f"{stats.learnt_large_success_sub10_step3_source_pop_overwrite_deep} "
                f"learnt_large_success_sub10_step3_source_pop_overwrite_deep_index2="
                f"{stats.learnt_large_success_sub10_step3_source_pop_overwrite_deep_index2} "
                f"learnt_large_success_sub10_step3_source_pop_overwrite_deep_index3_plus="
                f"{stats.learnt_large_success_sub10_step3_source_pop_overwrite_deep_index3_plus} "
                f"learnt_large_success_sub10_step3_source_pop_overwrite_deep_index3="
                f"{stats.learnt_large_success_sub10_step3_source_pop_overwrite_deep_index3} "
                f"learnt_large_success_sub10_step3_source_pop_overwrite_deep_index4_plus="
                f"{stats.learnt_large_success_sub10_step3_source_pop_overwrite_deep_index4_plus} "
                f"learnt_large_success_sub10_step3_source_pop_overwrite_deep_index4="
                f"{stats.learnt_large_success_sub10_step3_source_pop_overwrite_deep_index4} "
                f"learnt_large_success_sub10_step3_source_pop_overwrite_deep_index5_plus="
                f"{stats.learnt_large_success_sub10_step3_source_pop_overwrite_deep_index5_plus} "
                f"learnt_large_success_sub10_step4={stats.learnt_large_success_sub10_step4} "
                f"learnt_large_success_sub10_step5_plus={stats.learnt_large_success_sub10_step5_plus} "
                f"learnt_large_success_sub10_step3_4_share={learnt_large_success_sub10_step3_4_share:.4f} "
                f"learnt_large_success_sub10_step3_share={learnt_large_success_sub10_step3_share:.4f} "
                f"learnt_large_success_sub10_step3_source_pop_last_slot_share="
                f"{learnt_large_success_sub10_step3_source_pop_last_slot_share:.4f} "
                f"learnt_large_success_sub10_step3_source_pop_overwrite_share="
                f"{learnt_large_success_sub10_step3_source_pop_overwrite_share:.4f} "
                f"learnt_large_success_sub10_step3_source_pop_overwrite_shallow_share="
                f"{learnt_large_success_sub10_step3_source_pop_overwrite_shallow_share:.4f} "
                f"learnt_large_success_sub10_step3_source_pop_overwrite_deep_share="
                f"{learnt_large_success_sub10_step3_source_pop_overwrite_deep_share:.4f} "
                f"learnt_large_success_sub10_step3_source_pop_overwrite_deep_index2_share="
                f"{learnt_large_success_sub10_step3_source_pop_overwrite_deep_index2_share:.4f} "
                f"learnt_large_success_sub10_step3_source_pop_overwrite_deep_index3_plus_share="
                f"{learnt_large_success_sub10_step3_source_pop_overwrite_deep_index3_plus_share:.4f} "
                f"learnt_large_success_sub10_step3_source_pop_overwrite_deep_index3_share="
                f"{learnt_large_success_sub10_step3_source_pop_overwrite_deep_index3_share:.4f} "
                f"learnt_large_success_sub10_step3_source_pop_overwrite_deep_index4_plus_share="
                f"{learnt_large_success_sub10_step3_source_pop_overwrite_deep_index4_plus_share:.4f} "
                f"learnt_large_success_sub10_step3_source_pop_overwrite_deep_index4_share="
                f"{learnt_large_success_sub10_step3_source_pop_overwrite_deep_index4_share:.4f} "
                f"learnt_large_success_sub10_step3_source_pop_overwrite_deep_index5_plus_share="
                f"{learnt_large_success_sub10_step3_source_pop_overwrite_deep_index5_plus_share:.4f} "
                f"learnt_large_success_sub10_step4_share={learnt_large_success_sub10_step4_share:.4f} "
                f"learnt_large_success_sub10_step5_plus_share={learnt_large_success_sub10_step5_plus_share:.4f} "
                f"max_large_probe={stats.max_large_probe} avg_learnt_before={avg_learnt_before:.2f} "
                f"avg_learnt_after={avg_learnt_after:.2f} max_learnt_before={stats.max_learnt_before} "
                f"max_learnt_after={stats.max_learnt_after} removed_by_min={stats.minimize_removed_literals} "
                f"analyze_reason_traversals={stats.analyze_reason_traversals} "
                f"analyze_problem_reasons={stats.analyze_problem_reason_traversals} "
                f"analyze_learnt_reasons={stats.analyze_learnt_reason_traversals} "
                f"analyze_problem_reason_distinct={stats.analyze_problem_reason_distinct_clauses} "
                f"max_analyze_problem_reason_clause_traversals={stats.max_analyze_problem_reason_clause_traversals} "
                f"analyze_problem_reason_hot_share={analyze_problem_reason_hot_share:.4f} "
                f"analyze_reason_2={analyze_2} analyze_reason_3={analyze_3} "
                f"analyze_reason_4_9={analyze_4_9} "
                f"analyze_reason_10_plus={analyze_10_plus} minimize_reason_checks={stats.minimize_reason_checks} "
                f"analyze_learnt_literal_appends={stats.analyze_learnt_literal_appends} "
                f"avg_analyze_learnt_literal_appends={avg_analyze_learnt_literal_appends:.2f} "
                f"minimize_problem_reasons={stats.minimize_problem_reason_checks} "
                f"minimize_learnt_reasons={stats.minimize_learnt_reason_checks} "
                f"min_keep_2={kept_2} min_keep_3={kept_3} min_keep_4_9={kept_4_9} "
                f"min_keep_10_plus={kept_10_plus} min_drop_2={removed_2} min_drop_3={removed_3} "
                f"min_drop_4_9={removed_4_9} min_drop_10_plus={removed_10_plus} "
                f"avg_lbd={avg_lbd:.2f} "
                f"restart_base={stats.restart_base} next_reduce={stats.next_reduce} "
                f"var_decay={stats.var_decay:.3f} clause_decay={stats.clause_decay:.3f}"
            )
        )

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
