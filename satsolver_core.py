from __future__ import annotations

from collections.abc import Iterable
import os
import sys


TRUE = 1
FALSE = -1
UNASSIGNED = 0

PORTFOLIO_DISABLE_ENV = "SATSOLVER_DISABLE_PORTFOLIO"
PORTFOLIO_MIN_VARS = 250
PORTFOLIO_MIN_CLAUSES = 1000
PORTFOLIO_MAX_DENSITY = 4.2
ROOT_PURE_LITERAL_MIN_ASSIGNMENTS = 2


def luby(index: int) -> int:
    """Return the 1-indexed Luby sequence value."""
    if index < 1:
        raise ValueError("Luby sequence is 1-indexed")

    size = 1
    while size < index + 1:
        size = 2 * size + 1
    while size - 1 != index:
        size = (size - 1) // 2
        index %= size
    return (size + 1) // 2


def lit_index(literal: int) -> int:
    variable = abs(literal)
    return variable * 2 if literal > 0 else variable * 2 + 1


def normalize_clause_literals(literals: Iterable[int]) -> list[int] | None:
    clause: list[int] = []
    seen: set[int] = set()
    for literal in literals:
        if literal == 0:
            continue
        if -literal in seen:
            return None
        if literal not in seen:
            seen.add(literal)
            clause.append(literal)
    return clause


def find_iterative_root_pure_literals(
    num_vars: int,
    clauses: Iterable[Iterable[int]],
) -> list[int]:
    normalized_clauses: list[list[int]] = []
    for clause in clauses:
        normalized = normalize_clause_literals(clause)
        if normalized is not None:
            normalized_clauses.append(normalized)

    active = [True] * len(normalized_clauses)
    assignment = [UNASSIGNED] * (num_vars + 1)
    pure_literals: list[int] = []

    while True:
        polarity = [0] * (num_vars + 1)

        for clause_id, clause in enumerate(normalized_clauses):
            if not active[clause_id]:
                continue
            for literal in clause:
                variable = abs(literal)
                if assignment[variable] != UNASSIGNED:
                    continue
                polarity[variable] |= 1 if literal > 0 else 2

        round_pures: list[int] = []
        for variable in range(1, num_vars + 1):
            if assignment[variable] != UNASSIGNED:
                continue
            if polarity[variable] == 1:
                assignment[variable] = TRUE
                round_pures.append(variable)
            elif polarity[variable] == 2:
                assignment[variable] = FALSE
                round_pures.append(-variable)

        if not round_pures:
            return pure_literals

        pure_literals.extend(round_pures)

        for clause_id, clause in enumerate(normalized_clauses):
            if not active[clause_id]:
                continue
            for literal in clause:
                value = assignment[abs(literal)]
                if value != UNASSIGNED and value == (TRUE if literal > 0 else FALSE):
                    active[clause_id] = False
                    break


class Clause:
    __slots__ = ("lits", "learnt", "activity", "lbd", "deleted", "ternary")

    def __init__(
        self,
        lits: list[int],
        learnt: bool = False,
        activity: float = 0.0,
        lbd: int = 0,
        deleted: bool = False,
    ) -> None:
        self.lits = lits
        self.learnt = learnt
        self.activity = activity
        self.lbd = lbd
        self.deleted = deleted
        self.ternary = len(lits) == 3


class Solver:
    """A compact CDCL solver with watched literals, VSIDS-style activity, and restarts."""

    def __init__(self, num_vars: int) -> None:
        self.num_vars = num_vars
        self.clauses: list[Clause] = []
        self.learnt_ids: list[int] = []
        self.binary_implications: list[list[tuple[int, int]]] = [[] for _ in range(2 * num_vars + 2)]
        self.watchers: list[list[int]] = [[] for _ in range(2 * num_vars + 2)]
        self.literal_values = [UNASSIGNED] * (2 * num_vars + 1)
        self.literal_var = [0] * (2 * num_vars + 1)
        self.literal_sign = [0] * (2 * num_vars + 1)
        self.literal_watch_index = [0] * (2 * num_vars + 1)
        self.negated_watch_index = [0] * (2 * num_vars + 1)

        self.values = [UNASSIGNED] * (num_vars + 1)
        self.level = [0] * (num_vars + 1)
        self.reason: list[int | None] = [None] * (num_vars + 1)

        self.activity = [0.0] * (num_vars + 1)
        self.phase_bias = [0] * (num_vars + 1)
        self.saved_phase = [True] * (num_vars + 1)
        self.var_inc = 1.0
        self.var_decay = 0.95
        self.clause_inc = 1.0
        self.clause_decay = 0.999

        self.trail: list[int] = []
        self.trail_limits: list[int] = []
        self.decision_level = 0
        self.qhead = 0

        self.seen = [0] * (num_vars + 1)
        self.seen_token = 0
        self.lbd_marks = [0] * (num_vars + 1)
        self.lbd_token = 0

        self.conflicts = 0
        self.restart_base = 64
        self.next_reduce = 256

        self.ok = True

        literal_var = self.literal_var
        literal_sign = self.literal_sign
        literal_watch_index = self.literal_watch_index
        negated_watch_index = self.negated_watch_index
        for variable in range(1, num_vars + 1):
            positive_watch_index = variable * 2
            negative_watch_index = positive_watch_index + 1

            literal_var[variable] = variable
            literal_var[-variable] = variable
            literal_sign[variable] = TRUE
            literal_sign[-variable] = FALSE
            literal_watch_index[variable] = positive_watch_index
            literal_watch_index[-variable] = negative_watch_index
            negated_watch_index[variable] = negative_watch_index
            negated_watch_index[-variable] = positive_watch_index

    def current_level(self) -> int:
        return self.decision_level

    def literal_value(self, literal: int) -> int:
        return self.literal_values[literal]

    def enqueue(self, literal: int, reason: int | None) -> bool:
        variable = self.literal_var[literal]
        value = self.literal_sign[literal]
        current = self.values[variable]
        if current != UNASSIGNED:
            return current == value

        self.values[variable] = value
        self.literal_values[variable] = value
        self.literal_values[-variable] = -value
        self.level[variable] = self.decision_level
        self.reason[variable] = reason
        self.saved_phase[variable] = literal > 0
        self.trail.append(literal)
        return True

    def backtrack(self, level: int) -> None:
        trail = self.trail
        values = self.values
        literal_values = self.literal_values
        levels = self.level
        reasons = self.reason
        literal_var = self.literal_var
        trail_limits = self.trail_limits
        decision_level = self.decision_level

        while decision_level > level:
            start = trail_limits.pop()
            decision_level -= 1
            for index in range(len(trail) - 1, start - 1, -1):
                literal = trail[index]
                variable = literal_var[literal]
                values[variable] = UNASSIGNED
                literal_values[variable] = UNASSIGNED
                literal_values[-variable] = UNASSIGNED
                levels[variable] = 0
                reasons[variable] = None
            del trail[start:]

        self.decision_level = decision_level
        self.qhead = len(trail)

    def attach_clause(self, clause_id: int) -> None:
        clause = self.clauses[clause_id]
        if len(clause.lits) == 2:
            first, second = clause.lits
            self.binary_implications[self.negated_watch_index[first]].append((second, clause_id))
            self.binary_implications[self.negated_watch_index[second]].append((first, clause_id))
            return
        self.watchers[self.literal_watch_index[clause.lits[0]]].append(clause_id)
        self.watchers[self.literal_watch_index[clause.lits[1]]].append(clause_id)

    def bump_var_activity(self, variable: int) -> None:
        self.activity[variable] += self.var_inc
        if self.activity[variable] > 1e100:
            for index in range(1, self.num_vars + 1):
                self.activity[index] *= 1e-100
            self.var_inc *= 1e-100

    def decay_var_activity(self) -> None:
        self.var_inc /= self.var_decay

    def bump_clause_activity(self, clause_id: int) -> None:
        clause = self.clauses[clause_id]
        clause.activity += self.clause_inc
        if clause.activity > 1e20:
            for learnt_id in self.learnt_ids:
                learnt = self.clauses[learnt_id]
                if not learnt.deleted:
                    learnt.activity *= 1e-20
            self.clause_inc *= 1e-20

    def decay_clause_activity(self) -> None:
        self.clause_inc /= self.clause_decay

    def observe_clause(self, literals: Iterable[int]) -> None:
        for literal in literals:
            variable = abs(literal)
            self.activity[variable] += 1.0
            self.phase_bias[variable] += 1 if literal > 0 else -1

    def normalize_clause(self, literals: Iterable[int]) -> list[int] | None:
        return normalize_clause_literals(literals)

    def simplify_root_clause(self, literals: Iterable[int]) -> list[int] | None:
        reduced: list[int] = []
        for literal in literals:
            value = self.literal_value(literal)
            if value == TRUE:
                return None
            if value != FALSE:
                reduced.append(literal)
        return reduced

    def add_problem_clause(self, literals: Iterable[int]) -> bool:
        if not self.ok:
            return False

        normalized = self.normalize_clause(literals)
        if normalized is None:
            return True

        self.observe_clause(normalized)
        reduced = self.simplify_root_clause(normalized)
        if reduced is None:
            return True
        if not reduced:
            self.ok = False
            return False

        clause_id = len(self.clauses)
        clause = Clause(reduced, learnt=False, lbd=0)
        self.clauses.append(clause)

        if len(reduced) == 1:
            if not self.enqueue(reduced[0], clause_id):
                self.ok = False
                return False
            conflict = self.propagate()
            if conflict is not None:
                self.ok = False
                return False
            return True

        self.attach_clause(clause_id)
        return True

    def add_learnt_clause(self, literals: list[int], lbd: int) -> int:
        clause_id = len(self.clauses)
        clause = Clause(list(literals), learnt=True, activity=self.clause_inc, lbd=lbd)
        self.clauses.append(clause)
        self.learnt_ids.append(clause_id)
        if len(literals) > 1:
            self.attach_clause(clause_id)
        return clause_id

    def propagate(self) -> int | None:
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

        while qhead < trail_len:
            literal = trail[qhead]
            qhead += 1

            for implied_literal, clause_id in binary_implications[literal_watch_index[literal]]:
                clause = clauses[clause_id]
                if clause.deleted:
                    continue

                implied_value = literal_values[implied_literal]
                if implied_value == FALSE:
                    self.qhead = qhead
                    return clause_id
                if implied_value == UNASSIGNED:
                    variable = literal_var[implied_literal]
                    value = literal_sign[implied_literal]
                    values[variable] = value
                    literal_values[variable] = value
                    literal_values[-variable] = -value
                    levels[variable] = decision_level
                    reasons[variable] = clause_id
                    saved_phase[variable] = implied_literal > 0
                    trail.append(implied_literal)
                    trail_len += 1

            false_literal = -literal
            watchers = all_watchers[negated_watch_index[literal]]
            index = 0
            watchers_len = len(watchers)

            while index < watchers_len:
                clause_id = watchers[index]
                clause = clauses[clause_id]

                if clause.learnt and clause.deleted:
                    watchers_len -= 1
                    watchers[index] = watchers[watchers_len]
                    watchers.pop()
                    continue

                lits = clause.lits
                if lits[0] == false_literal:
                    lits[0], lits[1] = lits[1], lits[0]

                other_literal = lits[0]
                other_value = literal_values[other_literal]

                if other_value == TRUE:
                    index += 1
                    continue

                if clause.ternary:
                    candidate_literal = lits[2]
                    candidate_value = literal_values[candidate_literal]
                    if candidate_value != FALSE:
                        lits[1], lits[2] = lits[2], lits[1]
                        all_watchers[literal_watch_index[lits[1]]].append(clause_id)
                        watchers_len -= 1
                        watchers[index] = watchers[watchers_len]
                        watchers.pop()
                        continue

                    if other_value == FALSE:
                        self.qhead = qhead
                        return clause_id
                    if other_value == UNASSIGNED:
                        variable = literal_var[other_literal]
                        value = literal_sign[other_literal]
                        values[variable] = value
                        literal_values[variable] = value
                        literal_values[-variable] = -value
                        levels[variable] = decision_level
                        reasons[variable] = clause_id
                        saved_phase[variable] = other_literal > 0
                        trail.append(other_literal)
                        trail_len += 1
                    index += 1
                    continue

                found_replacement = False
                for replacement in range(2, len(lits)):
                    candidate_literal = lits[replacement]
                    candidate_value = literal_values[candidate_literal]
                    if candidate_value != FALSE:
                        lits[1], lits[replacement] = lits[replacement], lits[1]
                        all_watchers[literal_watch_index[lits[1]]].append(clause_id)
                        watchers_len -= 1
                        watchers[index] = watchers[watchers_len]
                        watchers.pop()
                        found_replacement = True
                        break

                if found_replacement:
                    continue

                if other_value == FALSE:
                    self.qhead = qhead
                    return clause_id
                if other_value == UNASSIGNED:
                    variable = literal_var[other_literal]
                    value = literal_sign[other_literal]
                    values[variable] = value
                    literal_values[variable] = value
                    literal_values[-variable] = -value
                    levels[variable] = decision_level
                    reasons[variable] = clause_id
                    saved_phase[variable] = other_literal > 0
                    trail.append(other_literal)
                    trail_len += 1
                index += 1

        self.qhead = qhead
        return None

    def minimize_learnt(self, learnt: list[int], token: int) -> list[int]:
        if len(learnt) <= 2:
            return learnt

        levels = self.level
        reasons = self.reason
        seen = self.seen
        clauses = self.clauses
        write_index = 1

        for read_index in range(1, len(learnt)):
            literal = learnt[read_index]
            reason_clause_id = reasons[abs(literal)]
            if reason_clause_id is None:
                learnt[write_index] = literal
                write_index += 1
                continue

            reason_lits = clauses[reason_clause_id].lits
            neg_literal = -literal
            reason_size = len(reason_lits)

            if reason_size == 2:
                first, second = reason_lits
                other_variable = abs(second if first == neg_literal else first)
                if levels[other_variable] != 0 and seen[other_variable] != token:
                    learnt[write_index] = literal
                    write_index += 1
                continue

            if reason_size == 3:
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

                if (
                    (levels[first_variable] != 0 and seen[first_variable] != token)
                    or (levels[second_variable] != 0 and seen[second_variable] != token)
                ):
                    learnt[write_index] = literal
                    write_index += 1
                continue

            redundant = True
            for reason_literal in reason_lits:
                if reason_literal == neg_literal:
                    continue
                variable = abs(reason_literal)
                if levels[variable] != 0 and seen[variable] != token:
                    redundant = False
                    break

            if not redundant:
                learnt[write_index] = literal
                write_index += 1

        del learnt[write_index:]
        return learnt

    def prepare_learnt_clause(self, learnt: list[int]) -> tuple[int, int]:
        self.lbd_token += 1
        token = self.lbd_token
        marks = self.lbd_marks
        levels = self.level
        best_index = 1
        best_level = levels[abs(learnt[1])]
        lbd = 0

        for index, literal in enumerate(learnt):
            decision_level = levels[abs(literal)]
            if marks[decision_level] != token:
                marks[decision_level] = token
                lbd += 1
            if index != 0 and decision_level > best_level:
                best_level = decision_level
                best_index = index

        learnt[1], learnt[best_index] = learnt[best_index], learnt[1]
        return best_level, lbd

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
            current_clause_id = reason_clause_id

        learnt = self.minimize_learnt(learnt, token)

        self.var_inc = var_inc
        if len(learnt) == 1:
            return learnt, 0, 1

        best_level, lbd = self.prepare_learnt_clause(learnt)
        return learnt, best_level, lbd

    def pick_branch_literal(self) -> int:
        best_variable = 0
        best_activity = -1.0
        for variable in range(1, self.num_vars + 1):
            if self.values[variable] == UNASSIGNED and self.activity[variable] > best_activity:
                best_activity = self.activity[variable]
                best_variable = variable

        if best_variable == 0:
            return 0

        positive = self.saved_phase[best_variable]
        if self.activity[best_variable] == 0.0:
            positive = self.phase_bias[best_variable] >= 0
        return best_variable if positive else -best_variable

    def reduce_database(self) -> None:
        if len(self.learnt_ids) < self.next_reduce:
            return

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
        keep.extend(candidates[:midpoint])
        for clause_id in candidates[midpoint:]:
            self.clauses[clause_id].deleted = True

        self.learnt_ids = keep
        self.next_reduce = max(256, int(len(self.learnt_ids) * 1.5) + 64)

    def build_model(self) -> list[int]:
        model = [FALSE] * (self.num_vars + 1)
        for variable in range(1, self.num_vars + 1):
            value = self.values[variable]
            if value == UNASSIGNED:
                value = TRUE if self.saved_phase[variable] else FALSE
            model[variable] = value
        return model

    def seed_saved_phases_from_bias(self) -> None:
        values = self.values
        saved_phase = self.saved_phase
        phase_bias = self.phase_bias

        for variable in range(1, self.num_vars + 1):
            if values[variable] == UNASSIGNED:
                saved_phase[variable] = phase_bias[variable] >= 0

    def solve(self) -> list[int] | None:
        if not self.ok:
            return None

        root_conflict = self.propagate()
        if root_conflict is not None:
            self.ok = False
            return None

        restart_index = 1
        conflicts_since_restart = 0
        restart_limit = self.restart_base * luby(restart_index)

        while True:
            conflict = self.propagate()
            if conflict is not None:
                self.conflicts += 1
                conflicts_since_restart += 1

                if self.decision_level == 0:
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
                    self.backtrack(0)
                    conflicts_since_restart = 0
                    restart_index += 1
                    restart_limit = self.restart_base * luby(restart_index)

                self.reduce_database()
                continue

            branch_literal = self.pick_branch_literal()
            if branch_literal == 0:
                return self.build_model()

            self.trail_limits.append(len(self.trail))
            self.decision_level += 1
            self.enqueue(branch_literal, None)


def parse_dimacs(text: str) -> tuple[int, list[list[int]]]:
    num_vars: int | None = None
    num_clauses: int | None = None
    clauses: list[list[int]] = []
    current: list[int] = []
    header_seen = False

    for raw_line in text.splitlines():
        line = raw_line.strip()
        if not line or line.startswith("c"):
            continue
        if line.startswith("%"):
            break
        if line.startswith("p"):
            if header_seen:
                raise ValueError("Multiple DIMACS problem lines are not allowed")
            parts = line.split()
            if len(parts) != 4 or parts[1] != "cnf":
                raise ValueError("Invalid DIMACS problem line")
            num_vars = int(parts[2])
            num_clauses = int(parts[3])
            header_seen = True
            continue
        if not header_seen:
            raise ValueError("DIMACS clauses must appear after the problem line")

        for token in line.split():
            literal = int(token)
            if literal == 0:
                clauses.append(current)
                current = []
            else:
                if abs(literal) > num_vars:
                    raise ValueError(
                        f"Literal {literal} exceeds declared variable range 1..{num_vars}"
                    )
                current.append(literal)

    if num_vars is None or num_clauses is None:
        raise ValueError("Missing DIMACS problem line")
    if current:
        raise ValueError("Last clause is missing its terminating 0")
    if len(clauses) != num_clauses:
        raise ValueError(
            f"Clause count mismatch: header says {num_clauses}, parsed {len(clauses)}"
        )

    return num_vars, clauses


def parse_dimacs_file(path: str) -> tuple[int, list[list[int]]]:
    with open(path, "r", encoding="utf-8") as handle:
        return parse_dimacs(handle.read())


def model_satisfies(clauses: Iterable[Iterable[int]], model: list[int]) -> bool:
    for clause in clauses:
        if not any(model[abs(literal)] == (TRUE if literal > 0 else FALSE) for literal in clause):
            return False
    return True


def has_pigeonhole_core(clauses: Iterable[Iterable[int]]) -> bool:
    negative_pairs: set[tuple[int, int]] = set()
    positive_rows_by_width: dict[int, list[tuple[int, ...]]] = {}

    for clause in clauses:
        lits = list(clause)
        if len(lits) == 2 and lits[0] < 0 and lits[1] < 0:
            first, second = sorted((-lits[0], -lits[1]))
            negative_pairs.add((first, second))
        elif len(lits) > 1 and all(literal > 0 for literal in lits):
            row = tuple(sorted(dict.fromkeys(lits)))
            if len(row) == len(lits):
                positive_rows_by_width.setdefault(len(row), []).append(row)

    for width, rows in positive_rows_by_width.items():
        if len(rows) <= width:
            continue

        rows = sorted(rows)
        selected: list[tuple[int, ...]] = []
        used: set[int] = set()

        for row in rows:
            if used.isdisjoint(row):
                selected.append(row)
                used.update(row)

        if len(selected) <= width:
            continue

        core_found = True
        for column in range(width):
            column_vars = [row[column] for row in selected]
            for first_index in range(len(column_vars)):
                for second_index in range(first_index + 1, len(column_vars)):
                    pair = tuple(sorted((column_vars[first_index], column_vars[second_index])))
                    if pair not in negative_pairs:
                        core_found = False
                        break
                if not core_found:
                    break
            if not core_found:
                break

        if core_found:
            return True

    return False


def xor_system_unsat(num_vars: int, clauses: Iterable[Iterable[int]]) -> bool:
    groups: dict[tuple[int, ...], set[int]] = {}

    for clause in clauses:
        literals = list(clause)
        if len(literals) < 3 or len(literals) > 6:
            continue

        signs: dict[int, int] = {}
        valid = True
        for literal in literals:
            variable = abs(literal)
            if variable in signs:
                valid = False
                break
            signs[variable] = 1 if literal < 0 else 0

        if not valid:
            continue

        variables = tuple(sorted(signs))
        pattern = 0
        for index, variable in enumerate(variables):
            pattern |= signs[variable] << index
        groups.setdefault(variables, set()).add(pattern)

    basis: dict[int, tuple[int, int]] = {}
    equations: list[tuple[int, int]] = []

    for variables, patterns in groups.items():
        width = len(variables)
        if len(patterns) != (1 << (width - 1)):
            continue

        parities = {pattern.bit_count() & 1 for pattern in patterns}
        if len(parities) != 1:
            continue

        forbidden_parity = next(iter(parities))
        rhs = forbidden_parity ^ 1
        mask = 0
        for variable in variables:
            if variable > num_vars:
                return False
            mask |= 1 << (variable - 1)
        equations.append((mask, rhs))

    for mask, rhs in equations:
        current_mask = mask
        current_rhs = rhs

        while current_mask:
            pivot = current_mask.bit_length() - 1
            row = basis.get(pivot)
            if row is None:
                basis[pivot] = (current_mask, current_rhs)
                break
            current_mask ^= row[0]
            current_rhs ^= row[1]
        else:
            if current_rhs:
                return True

    return False


def format_model(model: list[int]) -> str:
    literals = [str(variable if model[variable] == TRUE else -variable) for variable in range(1, len(model))]
    return " ".join(literals) + " 0"


def solve_cnf_serial(
    num_vars: int,
    clauses: list[list[int]],
    *,
    seed_phase_bias: bool = False,
) -> list[int] | None:
    solver = Solver(num_vars)
    root_pure_literals = find_iterative_root_pure_literals(num_vars, clauses)
    if len(root_pure_literals) >= ROOT_PURE_LITERAL_MIN_ASSIGNMENTS:
        for literal in root_pure_literals:
            if not solver.enqueue(literal, None):
                return None
    for clause in clauses:
        if not solver.add_problem_clause(clause):
            return None
    if seed_phase_bias:
        solver.seed_saved_phases_from_bias()
    return solver.solve()


def should_use_parallel_portfolio(num_vars: int, clauses: list[list[int]]) -> bool:
    if os.environ.get(PORTFOLIO_DISABLE_ENV):
        return False
    if os.name != "posix":
        return False
    cpu_count = os.cpu_count() or 1
    if cpu_count < 2:
        return False
    if num_vars < PORTFOLIO_MIN_VARS or len(clauses) < PORTFOLIO_MIN_CLAUSES:
        return False
    if not all(len(clause) == 3 for clause in clauses):
        return False
    return (len(clauses) / num_vars) <= PORTFOLIO_MAX_DENSITY


def solve_cnf_portfolio(num_vars: int, clauses: list[list[int]]) -> list[int] | None:
    import multiprocessing as mp

    def solve_portfolio_worker(seed_phase_bias: bool, result_queue) -> None:
        try:
            model = solve_cnf_serial(num_vars, clauses, seed_phase_bias=seed_phase_bias)
            result_queue.put((True, model))
        except BaseException as exc:
            result_queue.put((False, f"{type(exc).__name__}: {exc}"))

    context = mp.get_context("fork")
    result_queue = context.Queue()
    processes = [
        context.Process(target=solve_portfolio_worker, args=(False, result_queue)),
        context.Process(target=solve_portfolio_worker, args=(True, result_queue)),
    ]

    for process in processes:
        process.start()

    errors: list[str] = []

    try:
        remaining = len(processes)
        while remaining > 0:
            ok, payload = result_queue.get()
            remaining -= 1
            if ok:
                return payload
            errors.append(payload)
    finally:
        for process in processes:
            if process.is_alive():
                process.terminate()
        for process in processes:
            process.join()
        result_queue.close()
        result_queue.join_thread()

    raise RuntimeError(f"Parallel portfolio failed: {'; '.join(errors)}")


def solve_cnf(num_vars: int, clauses: list[list[int]]) -> list[int] | None:
    if has_pigeonhole_core(clauses):
        return None
    if xor_system_unsat(num_vars, clauses):
        return None
    if should_use_parallel_portfolio(num_vars, clauses):
        return solve_cnf_portfolio(num_vars, clauses)
    return solve_cnf_serial(num_vars, clauses)


def write_result(path: str, model: list[int] | None) -> None:
    with open(path, "w", encoding="utf-8") as handle:
        if model is None:
            handle.write("UNSAT\n")
        else:
            handle.write("SAT\n")
            handle.write(format_model(model))
            handle.write("\n")


def main(argv: list[str] | None = None) -> int:
    arguments = sys.argv[1:] if argv is None else argv
    if len(arguments) != 2:
        print("Usage: python satsolver.py input.cnf output.txt", file=sys.stderr)
        return 1

    input_path, output_path = arguments
    try:
        num_vars, clauses = parse_dimacs_file(input_path)
        model = solve_cnf(num_vars, clauses)
        if model is not None and not model_satisfies(clauses, model):
            raise RuntimeError("Internal error: produced model does not satisfy the input CNF")
        write_result(output_path, model)
    except Exception as exc:  # pragma: no cover - CLI safety path
        print(f"Error: {exc}", file=sys.stderr)
        return 1

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
