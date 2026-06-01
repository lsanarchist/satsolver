from __future__ import annotations

import sys

import satsolver_core as base
import satsolver_io as io

CLI_MODE = __name__ == "__main__"

if CLI_MODE:
    Solver = base.Solver
    model_satisfies = base.model_satisfies
    has_pigeonhole_core = base.has_pigeonhole_core
    xor_system_unsat = base.xor_system_unsat
    graph_coloring_mycielski_unsat = base.graph_coloring_mycielski_unsat
    format_model = base.format_model
    should_use_parallel_portfolio = base.should_use_parallel_portfolio
else:
    import os

    TRUE = base.TRUE
    FALSE = base.FALSE
    UNASSIGNED = base.UNASSIGNED

    PORTFOLIO_DISABLE_ENV = base.PORTFOLIO_DISABLE_ENV
    PORTFOLIO_MIN_VARS = base.PORTFOLIO_MIN_VARS
    PORTFOLIO_MIN_CLAUSES = base.PORTFOLIO_MIN_CLAUSES
    PORTFOLIO_MAX_DENSITY = base.PORTFOLIO_MAX_DENSITY
    PHASE_PORTFOLIO_MAX_WORKERS = base.PHASE_PORTFOLIO_MAX_WORKERS
    PHASE_MODE_DEFAULT = base.PHASE_MODE_DEFAULT
    PHASE_MODE_BIAS_POSITIVE = base.PHASE_MODE_BIAS_POSITIVE
    PHASE_MODE_BIAS_NEGATIVE = base.PHASE_MODE_BIAS_NEGATIVE
    PHASE_MODE_LCG1 = base.PHASE_MODE_LCG1
    PHASE_PORTFOLIO_MODES = base.PHASE_PORTFOLIO_MODES
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
    parse_graph_coloring_encoding = base.parse_graph_coloring_encoding
    mycielski_chromatic_lower_bound = base.mycielski_chromatic_lower_bound
    graph_coloring_mycielski_unsat = base.graph_coloring_mycielski_unsat
    format_model = base.format_model


parse_dimacs_bytes = io.parse_dimacs_bytes
parse_dimacs = io.parse_dimacs
parse_dimacs_file = io.parse_dimacs_file

if not CLI_MODE:

    def solve_cnf_serial(
        num_vars: int,
        clauses: list[list[int]],
        *,
        phase_mode: str = base.PHASE_MODE_DEFAULT,
        seed_phase_bias: bool = False,
    ) -> list[int] | None:
        if seed_phase_bias:
            phase_mode = base.PHASE_MODE_BIAS_POSITIVE

        solver = Solver(num_vars)
        root_pure_literals = base.find_iterative_root_pure_literals(num_vars, clauses)
        if len(root_pure_literals) >= base.ROOT_PURE_LITERAL_MIN_ASSIGNMENTS:
            for literal in root_pure_literals:
                if not solver.enqueue(literal, None):
                    return None
        for clause in clauses:
            if not solver.add_problem_clause(clause):
                return None
        solver.seed_saved_phases_mode(phase_mode)
        return solver.solve()


def solve_cnf_fast_serial(
    num_vars: int,
    clauses: list[list[int]],
    *,
    phase_mode: str = base.PHASE_MODE_DEFAULT,
    seed_phase_bias: bool = False,
) -> list[int] | None:
    if seed_phase_bias:
        phase_mode = base.PHASE_MODE_BIAS_POSITIVE

    solver = Solver(num_vars)
    for clause in clauses:
        if not solver.add_problem_clause(clause):
            return None
    solver.seed_saved_phases_mode(phase_mode)
    return solver.solve()


if not CLI_MODE:

    def should_use_parallel_portfolio(num_vars: int, clauses: list[list[int]]) -> bool:
        return base.should_use_parallel_portfolio(num_vars, clauses)


def solve_cnf_portfolio(num_vars: int, clauses: list[list[int]]) -> list[int] | None:
    import multiprocessing as mp
    import os

    def solve_portfolio_worker(phase_mode: str, result_queue) -> None:
        try:
            model = solve_cnf_fast_serial(num_vars, clauses, phase_mode=phase_mode)
            result_queue.put((True, phase_mode, model))
        except BaseException as exc:
            result_queue.put((False, phase_mode, f"{type(exc).__name__}: {exc}"))

    context = mp.get_context("fork")
    result_queue = context.Queue()
    cpu_count = os.cpu_count() or 1
    max_workers = min(
        cpu_count,
        base.PHASE_PORTFOLIO_MAX_WORKERS,
        len(base.PHASE_PORTFOLIO_MODES),
    )
    modes = base.PHASE_PORTFOLIO_MODES[:max_workers]
    processes = [
        context.Process(target=solve_portfolio_worker, args=(mode, result_queue))
        for mode in modes
    ]

    for process in processes:
        process.start()

    errors: list[str] = []

    try:
        remaining = len(processes)
        while remaining > 0:
            ok, phase_mode, payload = result_queue.get()
            remaining -= 1
            if ok:
                return payload
            errors.append(f"{phase_mode}: {payload}")
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
    if graph_coloring_mycielski_unsat(num_vars, clauses):
        return None
    if should_use_parallel_portfolio(num_vars, clauses):
        return solve_cnf_portfolio(num_vars, clauses)
    return solve_cnf_fast_serial(num_vars, clauses)


def write_result(path: str, model: list[int] | None) -> None:
    io.write_result(path, model, format_model=format_model)


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
