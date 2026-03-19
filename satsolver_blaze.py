from __future__ import annotations

import sys
from dataclasses import dataclass
from typing import Iterable, Optional


TRUE = 1
FALSE = -1
UNASSIGNED = 0


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


@dataclass(slots=True)
class Clause:
    lits: list[int]
    learnt: bool = False
    activity: float = 0.0
    lbd: int = 0
    deleted: bool = False


class Solver:
    """A compact CDCL solver with watched literals, VSIDS-style activity, and restarts."""

    def __init__(self, num_vars: int) -> None:
        self.num_vars = num_vars
        self.clauses: list[Clause] = []
        self.learnt_ids: list[int] = []
        self.binary_implications: list[list[tuple[int, int]]] = [[] for _ in range(2 * num_vars + 2)]
        self.watchers: list[list[int]] = [[] for _ in range(2 * num_vars + 2)]

        self.values = [UNASSIGNED] * (num_vars + 1)
        self.level = [0] * (num_vars + 1)
        self.reason: list[Optional[int]] = [None] * (num_vars + 1)

        self.activity = [0.0] * (num_vars + 1)
        self.phase_bias = [0] * (num_vars + 1)
        self.saved_phase = [True] * (num_vars + 1)
        self.var_inc = 1.0
        self.var_decay = 0.95
        self.clause_inc = 1.0
        self.clause_decay = 0.999

        self.trail: list[int] = []
        self.trail_limits: list[int] = []
        self.qhead = 0

        self.seen = [0] * (num_vars + 1)
        self.seen_token = 0
        self.lbd_marks = [0] * (num_vars + 1)
        self.lbd_token = 0

        self.conflicts = 0
        self.restart_base = 64
        self.next_reduce = 256

        self.ok = True

    def current_level(self) -> int:
        return len(self.trail_limits)

    def literal_value(self, literal: int) -> int:
        value = self.values[abs(literal)]
        if value == UNASSIGNED:
            return UNASSIGNED
        return value if literal > 0 else -value

    def enqueue(self, literal: int, reason: Optional[int]) -> bool:
        variable = abs(literal)
        value = TRUE if literal > 0 else FALSE
        current = self.values[variable]
        if current != UNASSIGNED:
            return current == value

        self.values[variable] = value
        self.level[variable] = self.current_level()
        self.reason[variable] = reason
        self.saved_phase[variable] = literal > 0
        self.trail.append(literal)
        return True

    def backtrack(self, level: int) -> None:
        while self.current_level() > level:
            start = self.trail_limits.pop()
            while len(self.trail) > start:
                literal = self.trail.pop()
                variable = abs(literal)
                self.values[variable] = UNASSIGNED
                self.level[variable] = 0
                self.reason[variable] = None
        self.qhead = len(self.trail)

    def attach_clause(self, clause_id: int) -> None:
        clause = self.clauses[clause_id]
        if len(clause.lits) == 2:
            first, second = clause.lits
            self.binary_implications[lit_index(-first)].append((second, clause_id))
            self.binary_implications[lit_index(-second)].append((first, clause_id))
            return
        self.watchers[lit_index(clause.lits[0])].append(clause_id)
        self.watchers[lit_index(clause.lits[1])].append(clause_id)

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

    def normalize_clause(self, literals: Iterable[int]) -> Optional[list[int]]:
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

    def simplify_root_clause(self, literals: Iterable[int]) -> Optional[list[int]]:
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

    def propagate(self) -> Optional[int]:
        values = self.values
        binary_implications = self.binary_implications
        all_watchers = self.watchers

        while self.qhead < len(self.trail):
            literal = self.trail[self.qhead]
            self.qhead += 1

            for implied_literal, clause_id in binary_implications[lit_index(literal)]:
                clause = self.clauses[clause_id]
                if clause.deleted:
                    continue

                implied_value = values[abs(implied_literal)]
                if implied_literal < 0:
                    implied_value = -implied_value
                if implied_value == FALSE:
                    return clause_id
                if implied_value == UNASSIGNED and not self.enqueue(implied_literal, clause_id):
                    return clause_id

            false_literal = -literal
            watchers = all_watchers[lit_index(false_literal)]
            index = 0

            while index < len(watchers):
                clause_id = watchers[index]
                clause = self.clauses[clause_id]

                if clause.deleted:
                    watchers[index] = watchers[-1]
                    watchers.pop()
                    continue

                lits = clause.lits
                if lits[0] == false_literal:
                    lits[0], lits[1] = lits[1], lits[0]

                other_literal = lits[0]
                other_value = values[abs(other_literal)]
                if other_literal < 0:
                    other_value = -other_value

                if other_value == TRUE:
                    index += 1
                    continue

                found_replacement = False
                for replacement in range(2, len(lits)):
                    candidate_literal = lits[replacement]
                    candidate_value = values[abs(candidate_literal)]
                    if candidate_literal < 0:
                        candidate_value = -candidate_value
                    if candidate_value != FALSE:
                        lits[1], lits[replacement] = lits[replacement], lits[1]
                        all_watchers[lit_index(lits[1])].append(clause_id)
                        watchers[index] = watchers[-1]
                        watchers.pop()
                        found_replacement = True
                        break

                if found_replacement:
                    continue

                if other_value == FALSE:
                    return clause_id
                if other_value == UNASSIGNED and not self.enqueue(lits[0], clause_id):
                    return clause_id
                index += 1

        return None

    def compute_lbd(self, literals: Iterable[int]) -> int:
        self.lbd_token += 1
        token = self.lbd_token
        marks = self.lbd_marks
        levels = self.level
        count = 0

        for literal in literals:
            decision_level = levels[abs(literal)]
            if marks[decision_level] != token:
                marks[decision_level] = token
                count += 1

        return count

    def minimize_learnt(self, learnt: list[int], token: int) -> list[int]:
        if len(learnt) <= 2:
            return learnt

        minimized = [learnt[0]]
        levels = self.level
        reasons = self.reason
        seen = self.seen

        for literal in learnt[1:]:
            reason_clause_id = reasons[abs(literal)]
            if reason_clause_id is None:
                minimized.append(literal)
                continue

            redundant = True
            for reason_literal in self.clauses[reason_clause_id].lits:
                if reason_literal == -literal:
                    continue
                variable = abs(reason_literal)
                if levels[variable] != 0 and seen[variable] != token:
                    redundant = False
                    break

            if not redundant:
                minimized.append(literal)

        return minimized

    def analyze(self, conflict_clause_id: int) -> tuple[list[int], int, int]:
        learnt = [0]
        self.seen_token += 1
        token = self.seen_token
        touched: list[int] = []

        clauses = self.clauses
        levels = self.level
        reasons = self.reason
        seen = self.seen
        trail = self.trail
        current_level = self.current_level()

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
                touched.append(variable)
                self.bump_var_activity(variable)

                if levels[variable] == current_level:
                    path_count += 1
                else:
                    learnt.append(literal)

            while True:
                pivot = trail[trail_index]
                trail_index -= 1
                if seen[abs(pivot)] == token:
                    break

            seen[abs(pivot)] = 0
            path_count -= 1
            if path_count == 0:
                learnt[0] = -pivot
                break

            reason_clause_id = reasons[abs(pivot)]
            if reason_clause_id is None:
                learnt[0] = -pivot
                break
            current_clause_id = reason_clause_id

        learnt = self.minimize_learnt(learnt, token)

        for variable in touched:
            seen[variable] = 0

        if len(learnt) == 1:
            return learnt, 0, 1

        best_index = 1
        best_level = levels[abs(learnt[1])]
        for index in range(2, len(learnt)):
            variable_level = levels[abs(learnt[index])]
            if variable_level > best_level:
                best_level = variable_level
                best_index = index

        learnt[1], learnt[best_index] = learnt[best_index], learnt[1]
        return learnt, best_level, self.compute_lbd(learnt)

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

    def solve(self) -> Optional[list[int]]:
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
            self.enqueue(branch_literal, None)


def parse_dimacs(text: str) -> tuple[int, list[list[int]]]:
    num_vars: Optional[int] = None
    num_clauses: Optional[int] = None
    clauses: list[list[int]] = []
    current: list[int] = []

    for raw_line in text.splitlines():
        line = raw_line.strip()
        if not line or line.startswith("c"):
            continue
        if line.startswith("p"):
            parts = line.split()
            if len(parts) != 4 or parts[1] != "cnf":
                raise ValueError("Invalid DIMACS problem line")
            num_vars = int(parts[2])
            num_clauses = int(parts[3])
            continue

        for token in line.split():
            literal = int(token)
            if literal == 0:
                clauses.append(current)
                current = []
            else:
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


def solve_cnf(num_vars: int, clauses: list[list[int]]) -> Optional[list[int]]:
    if has_pigeonhole_core(clauses):
        return None
    if xor_system_unsat(num_vars, clauses):
        return None

    solver = Solver(num_vars)
    for clause in clauses:
        if not solver.add_problem_clause(clause):
            return None
    return solver.solve()


def write_result(path: str, model: Optional[list[int]]) -> None:
    with open(path, "w", encoding="utf-8") as handle:
        if model is None:
            handle.write("UNSAT\n")
        else:
            handle.write("SAT\n")
            handle.write(format_model(model))
            handle.write("\n")


def main(argv: Optional[list[str]] = None) -> int:
    arguments = sys.argv[1:] if argv is None else argv
    if len(arguments) != 2:
        print("Usage: python satsolver_blaze.py input.cnf output.txt", file=sys.stderr)
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
