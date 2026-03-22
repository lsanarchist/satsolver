"""Optional external-library SAT solver wrapper for speed comparison.

This file is intentionally separate from the retained submission path.
It reuses the repo's DIMACS parsing and output formatting, but delegates
the actual SAT solving to PySAT when that library is available.
"""

from __future__ import annotations

import os
import sys

import satsolver as base
import satsolver_io as io

IMPORT_ERROR: Exception | None = None

try:
    from pysat.solvers import Solver as PySATSolver
except Exception as exc:  # pragma: no cover - depends on local external env
    PySATSolver = None
    IMPORT_ERROR = exc


DEFAULT_BACKEND = os.environ.get("SATSOLVER_PYSAT_BACKEND", "minisat22")


def parse_dimacs(text: str) -> tuple[int, list[list[int]]]:
    return io.parse_dimacs(text)


def parse_dimacs_file(path: str) -> tuple[int, list[list[int]]]:
    return io.parse_dimacs_file(path)


def write_result(path: str, model: list[int] | None) -> None:
    io.write_result(path, model, format_model=base.format_model)


def _build_model(num_vars: int, literals: list[int] | None) -> list[int]:
    model = [base.FALSE] * (num_vars + 1)
    if not literals:
        return model

    for literal in literals:
        variable = abs(literal)
        if 1 <= variable <= num_vars:
            model[variable] = base.TRUE if literal > 0 else base.FALSE

    return model


def solve_cnf(
    num_vars: int,
    clauses: list[list[int]],
    *,
    backend: str | None = None,
) -> list[int] | None:
    if PySATSolver is None:  # pragma: no cover - depends on local external env
        raise RuntimeError(
            "PySAT is not available in this interpreter. "
            "Use .venv-external-sat/bin/python satsolver_pysat.py ..."
        ) from IMPORT_ERROR

    solver_name = backend or os.environ.get("SATSOLVER_PYSAT_BACKEND", DEFAULT_BACKEND)

    with PySATSolver(name=solver_name) as solver:
        for clause in clauses:
            solver.add_clause(clause)

        if not solver.solve():
            return None

        return _build_model(num_vars, solver.get_model())


def main(argv: list[str] | None = None) -> int:
    arguments = sys.argv[1:] if argv is None else argv
    if len(arguments) != 2:
        print("Usage: python satsolver_pysat.py input.cnf output.txt", file=sys.stderr)
        return 1

    input_path, output_path = arguments

    try:
        num_vars, clauses = parse_dimacs_file(input_path)
        model = solve_cnf(num_vars, clauses)
        if model is not None and not base.model_satisfies(clauses, model):
            raise RuntimeError("Internal error: produced model does not satisfy the input CNF")
        write_result(output_path, model)
    except Exception as exc:  # pragma: no cover - CLI safety path
        print(f"Error: {exc}", file=sys.stderr)
        return 1

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
