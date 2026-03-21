from __future__ import annotations

import os
import sys

import satsolver_core as base


TRUE = base.TRUE
FALSE = base.FALSE
UNASSIGNED = base.UNASSIGNED

PORTFOLIO_DISABLE_ENV = base.PORTFOLIO_DISABLE_ENV
PORTFOLIO_MIN_VARS = base.PORTFOLIO_MIN_VARS
PORTFOLIO_MIN_CLAUSES = base.PORTFOLIO_MIN_CLAUSES
PORTFOLIO_MAX_DENSITY = base.PORTFOLIO_MAX_DENSITY
ROOT_PURE_LITERAL_MIN_ASSIGNMENTS = base.ROOT_PURE_LITERAL_MIN_ASSIGNMENTS

luby = base.luby
lit_index = base.lit_index
normalize_clause_literals = base.normalize_clause_literals
find_iterative_root_pure_literals = base.find_iterative_root_pure_literals
Clause = base.Clause
Solver = base.Solver
model_satisfies = base.model_satisfies
has_pigeonhole_core = base.has_pigeonhole_core
xor_system_unsat = base.xor_system_unsat
format_model = base.format_model


def parse_dimacs_bytes(data: bytes) -> tuple[int, list[list[int]]]:
    num_vars: int | None = None
    num_clauses: int | None = None
    clauses: list[list[int]] = []
    current: list[int] = []
    header_seen = False

    for raw_line in data.splitlines():
        line = raw_line.strip()
        if not line or line.startswith(b"c"):
            continue
        if line.startswith(b"%"):
            break
        if line.startswith(b"p"):
            if header_seen:
                raise ValueError("Multiple DIMACS problem lines are not allowed")
            parts = line.split()
            if len(parts) != 4 or parts[1] != b"cnf":
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


def parse_dimacs(text: str) -> tuple[int, list[list[int]]]:
    return parse_dimacs_bytes(text.encode("utf-8"))


def parse_dimacs_file(path: str) -> tuple[int, list[list[int]]]:
    with open(path, "rb") as handle:
        return parse_dimacs_bytes(handle.read())


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


def solve_cnf_fast_serial(
    num_vars: int,
    clauses: list[list[int]],
    *,
    seed_phase_bias: bool = False,
) -> list[int] | None:
    solver = Solver(num_vars)
    for clause in clauses:
        if not solver.add_problem_clause(clause):
            return None
    if seed_phase_bias:
        solver.seed_saved_phases_from_bias()
    return solver.solve()


def should_use_parallel_portfolio(num_vars: int, clauses: list[list[int]]) -> bool:
    return base.should_use_parallel_portfolio(num_vars, clauses)


def solve_cnf_portfolio(num_vars: int, clauses: list[list[int]]) -> list[int] | None:
    import multiprocessing as mp

    def solve_portfolio_worker(seed_phase_bias: bool, result_queue) -> None:
        try:
            model = solve_cnf_fast_serial(num_vars, clauses, seed_phase_bias=seed_phase_bias)
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
    return solve_cnf_fast_serial(num_vars, clauses)


def write_result(path: str, model: list[int] | None) -> None:
    with open(path, "wb") as handle:
        if model is None:
            handle.write(b"UNSAT\n")
        else:
            handle.write(b"SAT\n")
            handle.write(format_model(model).encode("ascii"))
            handle.write(b"\n")


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
