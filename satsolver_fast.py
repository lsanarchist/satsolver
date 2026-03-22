from __future__ import annotations

import sys

import satsolver_core as base
import satsolver_io as io


TRUE = base.TRUE
FALSE = base.FALSE
UNASSIGNED = base.UNASSIGNED

PORTFOLIO_DISABLE_ENV = base.PORTFOLIO_DISABLE_ENV
PORTFOLIO_MIN_VARS = base.PORTFOLIO_MIN_VARS
PORTFOLIO_MIN_CLAUSES = base.PORTFOLIO_MIN_CLAUSES
PORTFOLIO_MAX_DENSITY = base.PORTFOLIO_MAX_DENSITY

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

parse_dimacs_bytes = io.parse_dimacs_bytes
parse_dimacs = io.parse_dimacs
parse_dimacs_file = io.parse_dimacs_file


def write_result(path: str, model: list[int] | None) -> None:
    io.write_result(path, model, format_model=format_model)


def solve_cnf_serial(
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


def main(argv: list[str] | None = None) -> int:
    arguments = sys.argv[1:] if argv is None else argv
    if len(arguments) != 2:
        print("Usage: python satsolver_fast.py input.cnf output.txt", file=sys.stderr)
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
