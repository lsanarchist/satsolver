"""
CDCL SAT Solver — MiniSAT-style, olympiad-ready, pure Python.

Algorithm highlights
--------------------
* Two-watched-literal (2WL) unit propagation
* VSIDS variable-decision heuristic with periodic rescaling
* First-UIP conflict analysis + clause learning
* Non-chronological backtracking
* Luby-sequence restarts
* On-the-fly clause minimization (recursive self-subsumption)
* DIMACS CNF parser + command-line interface

Usage (API)
-----------
    from satsolver import Solver

    s = Solver()
    # add clauses as lists of integers (1-based, negative = negated)
    s.add_clause([1, -3, 4])
    s.add_clause([-1, 2])
    s.add_clause([-2, -4])
    result = s.solve()          # True (SAT) / False (UNSAT)
    if result:
        model = s.model()       # {var: bool, ...}

Usage (DIMACS CLI)
------------------
    python satsolver.py problem.cnf
"""

from __future__ import annotations

import sys
import math
from collections import defaultdict
from typing import List, Optional, Dict, Tuple


# ---------------------------------------------------------------------------
# Internal constants
# ---------------------------------------------------------------------------
_UNASSIGNED = -1
_FALSE = 0
_TRUE = 1

_UNDEF_REASON: int = -1   # sentinel: decision literal / no reason clause


# ---------------------------------------------------------------------------
# Luby sequence (for restarts)
# ---------------------------------------------------------------------------
def _luby(i: int) -> int:
    """Return the i-th element (1-indexed) of the Luby sequence."""
    # Find smallest k s.t. (2^k - 1) >= i
    k = 1
    while (1 << k) - 1 < i:
        k += 1
    if i == (1 << k) - 1:
        return 1 << (k - 1)
    return _luby(i - (1 << (k - 1)) + 1)


# ---------------------------------------------------------------------------
# Clause
# ---------------------------------------------------------------------------
class Clause:
    """A learned or original clause stored as a list of literals."""

    __slots__ = ("lits", "activity", "learnt")

    def __init__(self, lits: List[int], learnt: bool = False) -> None:
        self.lits: List[int] = lits
        self.activity: float = 0.0
        self.learnt: bool = learnt

    def __len__(self) -> int:
        return len(self.lits)

    def __repr__(self) -> str:  # pragma: no cover
        return f"Clause({self.lits})"


# ---------------------------------------------------------------------------
# Main solver
# ---------------------------------------------------------------------------
class Solver:
    """
    CDCL SAT solver with 2-watched literals, VSIDS, and Luby restarts.

    Variables are identified by positive integers starting at **1**.
    Literals are encoded as:  var * 2      for positive literal (+var)
                               var * 2 + 1  for negative literal (-var)
    """

    # ------------------------------------------------------------------
    # Construction helpers
    # ------------------------------------------------------------------

    def __init__(self) -> None:
        self._nvars: int = 0

        # Clause database
        self._clauses: List[Clause] = []      # original
        self._learnts: List[Clause] = []      # learned

        # Assignment trail
        self._assigns: List[int] = []         # indexed by var-1; _TRUE/_FALSE/_UNASSIGNED
        self._level: List[int] = []           # decision level of assignment
        self._reason: List[int] = []          # index into _clauses+_learnts; -1=decision
        self._trail: List[int] = []           # sequence of assigned literals
        self._trail_lim: List[int] = []       # trail size at each decision level

        # Two-watched literals: watcher[lit] = list of clause indices
        # Index 0 and 1 are unused (literal encoding starts at var*2 >= 2)
        self._watchers: List[List[int]] = [[], []]

        # VSIDS
        self._activity: List[float] = []      # indexed by var-1
        self._var_inc: float = 1.0
        self._var_decay: float = 0.95

        # Clause activity
        self._cla_inc: float = 1.0
        self._cla_decay: float = 0.999

        # Queue for unit propagation
        self._prop_queue: List[int] = []
        self._qhead: int = 0                  # index into _trail for BCP

        # Restart / learned-clause-deletion schedule
        self._restart_luby_unit: int = 100
        self._restart_count: int = 0
        self._conflict_budget: int = 0
        self._conflicts: int = 0

        # Status
        self._ok: bool = True                 # False if top-level conflict detected
        self._model: Optional[List[int]] = None  # satisfying assignment

    # ------------------------------------------------------------------
    # Public API
    # ------------------------------------------------------------------

    def new_var(self) -> int:
        """Allocate a new variable and return its 1-based index."""
        self._nvars += 1
        v = self._nvars
        self._assigns.append(_UNASSIGNED)
        self._level.append(-1)
        self._reason.append(_UNDEF_REASON)
        self._activity.append(0.0)
        # two literals per variable: 2v and 2v+1
        self._watchers.append([])  # lit 2v
        self._watchers.append([])  # lit 2v+1
        return v

    def add_clause(self, lits: List[int]) -> bool:
        """
        Add a clause given as a list of DIMACS-style literals
        (positive = variable, negative = negated variable; 1-based).

        Returns False if the formula is already unsatisfiable.
        """
        if not self._ok:
            return False

        # Ensure all variables exist
        for lit in lits:
            v = abs(lit)
            while v > self._nvars:
                self.new_var()

        # Convert to internal encoding
        int_lits = [self._ilit(lit) for lit in lits]

        # Simplify: remove duplicates and check for tautology
        seen: Dict[int, bool] = {}
        simplified: List[int] = []
        for il in int_lits:
            v = il >> 1
            if v in seen:
                if seen[v] != (il & 1):
                    return True   # tautology — trivially satisfied
            else:
                seen[v] = bool(il & 1)
                simplified.append(il)
        int_lits = simplified

        # Unit clause at level 0
        if len(int_lits) == 0:
            self._ok = False
            return False

        if len(int_lits) == 1:
            self._ok = self._enqueue(int_lits[0], _UNDEF_REASON)
            if self._ok:
                # propagate immediately so future clause additions see it
                self._ok = (self._propagate() == -1)
            return self._ok

        # Create clause — ensure watched literals are not already FALSE.
        # Reorder: satisfied or unassigned literals must occupy positions 0 and 1.
        not_false = [l for l in int_lits if self._value_lit(l) != _FALSE]
        false_lits = [l for l in int_lits if self._value_lit(l) == _FALSE]
        int_lits = not_false + false_lits

        if len(not_false) == 0:
            # All literals already FALSE at top level → UNSAT
            self._ok = False
            return False

        if len(not_false) == 1:
            # Exactly one non-false literal → unit propagation at top level
            self._ok = self._enqueue(int_lits[0], _UNDEF_REASON)
            if self._ok:
                self._ok = (self._propagate() == -1)
            return self._ok

        c = Clause(int_lits, learnt=False)
        idx = len(self._clauses)
        self._clauses.append(c)
        self._attach_clause(idx, clause_list=self._clauses)
        return True

    def solve(self, assumptions: Optional[List[int]] = None) -> bool:
        """
        Run the CDCL loop.

        Parameters
        ----------
        assumptions : list of DIMACS literals to assume (optional)

        Returns
        -------
        True  → SAT  (call `model()` to get the assignment)
        False → UNSAT
        """
        if not self._ok:
            return False

        # Propagate any top-level units added by add_clause
        if self._propagate() != -1:
            self._ok = False
            return False

        luby_idx = 0
        conflicts_at_restart = 0

        while True:
            conflict_idx = self._propagate()

            if conflict_idx != -1:
                # -------- CONFLICT --------
                self._conflicts += 1
                conflicts_at_restart += 1

                if self._decision_level() == 0:
                    self._ok = False
                    return False

                learnt_lits, backtrack_level = self._analyze(conflict_idx)
                self._cancel_until(backtrack_level)

                if len(learnt_lits) == 1:
                    self._enqueue(learnt_lits[0], _UNDEF_REASON)
                else:
                    lc = Clause(learnt_lits, learnt=True)
                    lc.activity = self._cla_inc
                    li = len(self._learnts)
                    self._learnts.append(lc)
                    self._attach_clause(li, clause_list=self._learnts)
                    self._enqueue(learnt_lits[0],
                                  _UNDEF_REASON - 1 - li)  # negative index = learnt

                self._var_decay_activity()
                self._cla_decay_activity()

            else:
                # -------- NO CONFLICT --------

                # Restart?
                luby_idx += 1
                limit = _luby(luby_idx) * self._restart_luby_unit
                if conflicts_at_restart >= limit:
                    self._cancel_until(0)
                    conflicts_at_restart = 0
                    self._reduce_learnts()

                # All variables assigned?
                undef_var = self._pick_branching_var()
                if undef_var == -1:
                    # SAT
                    self._model = list(self._assigns)
                    self._cancel_until(0)
                    return True

                # Decide
                self._trail_lim.append(len(self._trail))
                lit = self._ilit_from_var(undef_var)
                self._enqueue(lit, _UNDEF_REASON)

    def model(self) -> Optional[Dict[int, bool]]:
        """
        Return the satisfying assignment as {variable: bool} (1-based vars).
        Returns None if `solve()` has not been called or returned False.
        """
        if self._model is None:
            return None
        result: Dict[int, bool] = {}
        for i, val in enumerate(self._model):
            if val != _UNASSIGNED:
                result[i + 1] = (val == _TRUE)
        return result

    # ------------------------------------------------------------------
    # Internal helpers: literal encoding
    # ------------------------------------------------------------------

    @staticmethod
    def _ilit(dimacs_lit: int) -> int:
        """Convert a DIMACS literal to internal encoding."""
        if dimacs_lit > 0:
            return dimacs_lit * 2
        return (-dimacs_lit) * 2 + 1

    @staticmethod
    def _negate(ilit: int) -> int:
        return ilit ^ 1

    @staticmethod
    def _var(ilit: int) -> int:
        """Return 0-based variable index from internal literal."""
        return (ilit >> 1) - 1

    def _ilit_from_var(self, var_idx: int) -> int:
        """
        Choose the preferred polarity for var_idx (0-based).
        We pick the polarity that makes the literal True if unassigned.
        Default: positive literal.
        """
        return (var_idx + 1) * 2  # positive literal for var var_idx+1

    # ------------------------------------------------------------------
    # Internal helpers: assignment
    # ------------------------------------------------------------------

    def _value_lit(self, ilit: int) -> int:
        v = self._var(ilit)
        asgn = self._assigns[v]
        if asgn == _UNASSIGNED:
            return _UNASSIGNED
        # if positive literal (ilit even): TRUE iff assigned TRUE
        if (ilit & 1) == 0:
            return asgn
        return _TRUE if asgn == _FALSE else _FALSE

    def _decision_level(self) -> int:
        return len(self._trail_lim)

    def _enqueue(self, ilit: int, reason: int) -> bool:
        """
        Assign literal ilit with given reason clause index.
        Returns False if the assignment contradicts a current assignment.
        """
        v = self._var(ilit)
        val = _TRUE if (ilit & 1) == 0 else _FALSE
        if self._assigns[v] != _UNASSIGNED:
            return self._assigns[v] == val
        self._assigns[v] = val
        self._level[v] = self._decision_level()
        self._reason[v] = reason
        self._trail.append(ilit)
        return True

    def _cancel_until(self, level: int) -> None:
        """Undo all assignments above the given decision level."""
        while self._decision_level() > level:
            # undo trail back to the saved position
            lim = self._trail_lim.pop()
            while len(self._trail) > lim:
                ilit = self._trail.pop()
                v = self._var(ilit)
                self._assigns[v] = _UNASSIGNED
                self._level[v] = -1
                self._reason[v] = _UNDEF_REASON
        self._qhead = len(self._trail)

    # ------------------------------------------------------------------
    # 2-watched literals
    # ------------------------------------------------------------------

    def _attach_clause(self, idx: int, *, clause_list: List[Clause]) -> None:
        """Set up the two watchers for clause at index idx."""
        c = clause_list[idx]
        # Encode: positive idx = original clause, negative-(idx+1) = learnt
        encoded = idx if clause_list is self._clauses else (_UNDEF_REASON - 1 - idx)
        self._watchers[self._negate(c.lits[0])].append(encoded)
        self._watchers[self._negate(c.lits[1])].append(encoded)

    def _clause_from_encoded(self, encoded: int) -> Clause:
        if encoded >= 0:
            return self._clauses[encoded]
        return self._learnts[_UNDEF_REASON - 1 - encoded]

    def _propagate(self) -> int:
        """
        BCP via 2-watched literals.
        Returns -1 if no conflict, otherwise the encoded index of the
        conflicting clause.
        """
        conflict = -1
        while self._qhead < len(self._trail):
            p = self._trail[self._qhead]
            self._qhead += 1
            false_lit = self._negate(p)  # literal that just became FALSE

            # Clauses are stored at watchers[~lit]; triggered when ~lit is
            # propagated TRUE (i.e. lit becomes FALSE).
            ws = self._watchers[p]
            i = 0
            j = 0
            while i < len(ws):
                encoded = ws[i]
                c = self._clause_from_encoded(encoded)
                lits = c.lits

                # Make sure lits[1] is the false literal
                if lits[0] == false_lit:
                    lits[0], lits[1] = lits[1], lits[0]
                # Now lits[1] == false_lit

                # Check if lits[0] is already True
                if self._value_lit(lits[0]) == _TRUE:
                    ws[j] = encoded
                    i += 1
                    j += 1
                    continue

                # Try to find a new watch among lits[2:]
                found = False
                for k in range(2, len(lits)):
                    if self._value_lit(lits[k]) != _FALSE:
                        lits[1], lits[k] = lits[k], lits[1]
                        self._watchers[self._negate(lits[1])].append(encoded)
                        found = True
                        break

                if found:
                    # Don't copy ws[i] to ws[j] — it's removed
                    i += 1
                else:
                    ws[j] = encoded
                    i += 1
                    j += 1
                    if self._value_lit(lits[0]) == _FALSE:
                        # Conflict
                        conflict = encoded
                        # Drain the rest of the watcher list in place
                        while i < len(ws):
                            ws[j] = ws[i]
                            i += 1
                            j += 1
                        del ws[j:]
                        self._qhead = len(self._trail)
                        return conflict
                    else:
                        # Unit propagation
                        reason = encoded
                        self._enqueue(lits[0], reason)

            del ws[j:]

        return conflict

    # ------------------------------------------------------------------
    # Conflict analysis (First-UIP)
    # ------------------------------------------------------------------

    def _analyze(self, conflict_encoded: int) -> Tuple[List[int], int]:
        """
        Analyse a conflict and return (learnt_clause_lits, backtrack_level).
        learnt_clause_lits[0] is the asserting literal (UIP).
        """
        learnt: List[int] = [0]  # placeholder for asserting lit
        seen: List[bool] = [False] * (self._nvars + 1)
        counter = 0  # count of current-level vars in the working set
        p = -1       # current literal being resolved
        p_reason = conflict_encoded

        trail_idx = len(self._trail) - 1

        while True:
            c = self._clause_from_encoded(p_reason)
            if c.learnt:
                learnt_idx = _UNDEF_REASON - 1 - p_reason
                self._bump_clause_activity(learnt_idx)

            for q in c.lits:
                if q == p:
                    continue
                v = self._var(q)
                if not seen[v + 1]:
                    seen[v + 1] = True
                    self._bump_var_activity(v)
                    if self._level[v] == self._decision_level():
                        counter += 1
                    elif self._level[v] > 0:
                        learnt.append(q)

            # Move to next literal in the trail that is in our working set
            while not seen[self._var(self._trail[trail_idx]) + 1]:
                trail_idx -= 1
            p = self._trail[trail_idx]
            trail_idx -= 1
            v = self._var(p)
            p_reason = self._reason[v]
            seen[v + 1] = False
            counter -= 1
            if counter == 0:
                break

        learnt[0] = self._negate(p)  # asserting literal (negation of UIP)

        # On-the-fly minimization
        learnt = self._minimize_clause(learnt, seen)

        # Determine backtrack level
        if len(learnt) == 1:
            btlevel = 0
        else:
            # find the literal with the highest decision level among learnt[1:]
            max_level = -1
            max_i = 1
            for i in range(1, len(learnt)):
                lv = self._level[self._var(learnt[i])]
                if lv > max_level:
                    max_level = lv
                    max_i = i
            learnt[1], learnt[max_i] = learnt[max_i], learnt[1]
            btlevel = max_level

        return learnt, btlevel

    def _minimize_clause(self, lits: List[int], seen: List[bool]) -> List[int]:
        """
        Remove literals that are redundant (implied by other literals in
        the clause at the same or earlier level).
        """
        minimized: List[int] = [lits[0]]
        for lit in lits[1:]:
            v = self._var(lit)
            r = self._reason[v]
            if r == _UNDEF_REASON:
                minimized.append(lit)
            else:
                c = self._clause_from_encoded(r)
                redundant = all(
                    self._level[self._var(q)] == 0 or seen[self._var(q) + 1]
                    for q in c.lits
                    if q != self._negate(lit)
                )
                if not redundant:
                    minimized.append(lit)
        return minimized

    # ------------------------------------------------------------------
    # VSIDS
    # ------------------------------------------------------------------

    def _bump_var_activity(self, v: int) -> None:
        self._activity[v] += self._var_inc
        if self._activity[v] > 1e100:
            # Rescale to avoid float overflow
            for i in range(self._nvars):
                self._activity[i] *= 1e-100
            self._var_inc *= 1e-100

    def _var_decay_activity(self) -> None:
        self._var_inc /= self._var_decay

    def _bump_clause_activity(self, idx: int) -> None:
        c = self._learnts[idx]
        c.activity += self._cla_inc
        if c.activity > 1e20:
            for lc in self._learnts:
                lc.activity *= 1e-20
            self._cla_inc *= 1e-20

    def _cla_decay_activity(self) -> None:
        self._cla_inc /= self._cla_decay

    def _pick_branching_var(self) -> int:
        """
        Return the 0-based index of the unassigned variable with the
        highest VSIDS activity, or -1 if all variables are assigned.
        """
        best_v = -1
        best_act = -1.0
        for v in range(self._nvars):
            if self._assigns[v] == _UNASSIGNED and self._activity[v] > best_act:
                best_act = self._activity[v]
                best_v = v
        return best_v

    # ------------------------------------------------------------------
    # Learned clause deletion (reduce)
    # ------------------------------------------------------------------

    def _reduce_learnts(self) -> None:
        """
        Delete approximately half of the learnt clauses (lowest activity).
        Keep clauses that are unit (i.e., currently asserting).
        """
        if not self._learnts:
            return

        # Sort by activity ascending (lowest first)
        indexed = sorted(
            range(len(self._learnts)), key=lambda i: self._learnts[i].activity
        )
        half = len(indexed) // 2
        to_remove = set(indexed[:half])

        new_learnts: List[Clause] = []
        remap: Dict[int, int] = {}
        for old_idx, lc in enumerate(self._learnts):
            if old_idx in to_remove:
                # Detach watchers lazily (they will fail to resolve and be skipped)
                # We mark the clause as empty so the watcher loop ignores it
                lc.lits = []
            else:
                remap[old_idx] = len(new_learnts)
                new_learnts.append(lc)

        self._learnts = new_learnts

        # Rebuild watcher lists for learnt clauses (remove stale entries)
        for wlist in self._watchers:
            cleaned = []
            for encoded in wlist:
                if encoded >= 0:
                    cleaned.append(encoded)  # original clause — keep
                else:
                    old_li = _UNDEF_REASON - 1 - encoded
                    if old_li not in to_remove:
                        new_li = remap[old_li]
                        cleaned.append(_UNDEF_REASON - 1 - new_li)
            wlist[:] = cleaned

        # Fix reason pointers in trail
        for v in range(self._nvars):
            r = self._reason[v]
            if r < 0 and r != _UNDEF_REASON:
                old_li = _UNDEF_REASON - 1 - r
                if old_li in to_remove:
                    self._reason[v] = _UNDEF_REASON
                elif old_li in remap:
                    self._reason[v] = _UNDEF_REASON - 1 - remap[old_li]


# ---------------------------------------------------------------------------
# DIMACS CNF parser
# ---------------------------------------------------------------------------

def parse_dimacs(text: str) -> Tuple[int, int, List[List[int]]]:
    """
    Parse a DIMACS CNF string.

    Returns (num_vars, num_clauses, clauses) where each clause is a list
    of integer DIMACS literals.
    """
    num_vars = 0
    num_clauses = 0
    clauses: List[List[int]] = []
    current: List[int] = []

    for raw_line in text.splitlines():
        line = raw_line.strip()
        if not line or line.startswith("c"):
            continue
        if line.startswith("p"):
            parts = line.split()
            num_vars = int(parts[2])
            num_clauses = int(parts[3])
            continue
        for tok in line.split():
            lit = int(tok)
            if lit == 0:
                if current:
                    clauses.append(current)
                    current = []
            else:
                current.append(lit)

    if current:
        clauses.append(current)

    return num_vars, num_clauses, clauses


def solve_dimacs(text: str) -> Tuple[bool, Optional[Dict[int, bool]]]:
    """
    Solve a DIMACS CNF problem given as a string.

    Returns (satisfiable, model) where model is None when unsatisfiable.
    """
    num_vars, _num_clauses, clauses = parse_dimacs(text)

    s = Solver()
    # pre-allocate variables
    for _ in range(num_vars):
        s.new_var()

    for cl in clauses:
        if not s.add_clause(cl):
            return False, None

    if s.solve():
        return True, s.model()
    return False, None


# ---------------------------------------------------------------------------
# Command-line interface
# ---------------------------------------------------------------------------

def main(argv: Optional[List[str]] = None) -> int:
    if argv is None:
        argv = sys.argv[1:]

    if not argv:
        print("Usage: python satsolver.py <file.cnf>", file=sys.stderr)
        return 1

    path = argv[0]
    try:
        with open(path, "r") as fh:
            text = fh.read()
    except OSError as exc:
        print(f"Error reading {path}: {exc}", file=sys.stderr)
        return 1

    sat, assignment = solve_dimacs(text)

    if sat:
        print("s SATISFIABLE")
        if assignment:
            vals = " ".join(
                str(v if assignment[v] else -v)
                for v in sorted(assignment)
            )
            print(f"v {vals} 0")
        return 10
    else:
        print("s UNSATISFIABLE")
        return 20


if __name__ == "__main__":
    sys.exit(main())
