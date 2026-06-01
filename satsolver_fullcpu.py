from __future__ import annotations

import argparse
import multiprocessing as mp
import os
import queue
import sys
from time import perf_counter
from typing import Any

import satsolver_core as base
import satsolver_io as io


RESTART_BASES = (16384, 8192, 4096, 2048, 1024, 512, 256, 128)
VAR_DECAYS = (0.98, 0.97, 0.96, 0.95, 0.99)
LCG_MULTIPLIERS = (
    2654435761,
    2246822519,
    3266489917,
    668265263,
    374761393,
    1597334677,
    3812015801,
    1103515245,
)


def seed_worker_variant(solver: base.Solver, worker_id: int) -> None:
    solver.restart_base = RESTART_BASES[worker_id % len(RESTART_BASES)]
    solver.var_decay = VAR_DECAYS[worker_id % len(VAR_DECAYS)]

    if worker_id == 0:
        return
    if worker_id % 8 == 1:
        solver.seed_saved_phases_mode(base.PHASE_MODE_BIAS_POSITIVE)
        return
    if worker_id % 8 == 2:
        solver.seed_saved_phases_mode(base.PHASE_MODE_BIAS_NEGATIVE)
        return

    multiplier = LCG_MULTIPLIERS[worker_id % len(LCG_MULTIPLIERS)]
    salt = (worker_id + 1) * 0x9E3779B1
    values = solver.values
    saved_phase = solver.saved_phase
    activity = solver.activity
    for variable in range(1, solver.num_vars + 1):
        if values[variable] != base.UNASSIGNED:
            continue
        mixed = (variable * multiplier + salt) & 0xFFFFFFFF
        saved_phase[variable] = ((mixed >> 16) & 1) == 1
        activity[variable] += (mixed & 1023) * 1e-6


def solve_variant(
    num_vars: int,
    clauses: list[list[int]],
    worker_id: int,
) -> tuple[list[int] | None, int]:
    solver = base.Solver(num_vars)
    for clause in clauses:
        if not solver.add_problem_clause(clause):
            return None, solver.conflicts
    seed_worker_variant(solver, worker_id)
    return solver.solve(), solver.conflicts


def worker_main(
    num_vars: int,
    clauses: list[list[int]],
    worker_id: int,
    result_queue: Any,
) -> None:
    start = perf_counter()
    try:
        model, conflicts = solve_variant(num_vars, clauses, worker_id)
        result_queue.put((worker_id, True, model, conflicts, perf_counter() - start))
    except BaseException as exc:
        result_queue.put(
            (
                worker_id,
                False,
                f"{type(exc).__name__}: {exc}",
                0,
                perf_counter() - start,
            )
        )


def solve_cnf_fullcpu(
    num_vars: int,
    clauses: list[list[int]],
    *,
    workers: int,
    use_detectors: bool,
) -> list[int] | None:
    if workers < 1:
        raise ValueError("workers must be at least 1")

    if use_detectors:
        if base.has_pigeonhole_core(clauses):
            return None
        if base.xor_system_unsat(num_vars, clauses):
            return None
        if base.graph_coloring_mycielski_unsat(num_vars, clauses):
            return None

    if workers == 1:
        model, _ = solve_variant(num_vars, clauses, 0)
        return model

    context_name = "fork" if os.name == "posix" else "spawn"
    context = mp.get_context(context_name)
    result_queue = context.Queue()
    processes = [
        context.Process(target=worker_main, args=(num_vars, clauses, worker_id, result_queue))
        for worker_id in range(workers)
    ]
    live = set(range(len(processes)))
    errors: list[str] = []

    for process in processes:
        process.start()

    try:
        while live:
            try:
                worker_id, ok, payload, conflicts, elapsed = result_queue.get(timeout=0.1)
            except queue.Empty:
                for index in list(live):
                    process = processes[index]
                    if not process.is_alive() and process.exitcode is not None:
                        live.remove(index)
                        if process.exitcode != 0:
                            errors.append(f"worker {index} exited with code {process.exitcode}")
                continue

            live.discard(worker_id)
            if ok:
                model = payload
                if model is not None and not base.model_satisfies(clauses, model):
                    errors.append(f"worker {worker_id} returned an invalid SAT model")
                    continue
                return model
            errors.append(f"worker {worker_id} failed after {elapsed:.4f}s: {payload}")
    finally:
        for process in processes:
            if process.is_alive():
                process.terminate()
        for process in processes:
            process.join()
        result_queue.close()
        result_queue.join_thread()

    raise RuntimeError("all workers failed: " + "; ".join(errors))


def write_result(path: str, model: list[int] | None) -> None:
    io.write_result(path, model, format_model=base.format_model)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Solve one DIMACS CNF with a full-CPU multiprocessing portfolio."
    )
    parser.add_argument("input_path")
    parser.add_argument("output_path")
    parser.add_argument(
        "--workers",
        type=int,
        default=os.cpu_count() or 1,
        help="Number of parallel solver processes to run on the same CNF.",
    )
    parser.add_argument(
        "--use-detectors",
        action="store_true",
        help="Run the same structured UNSAT detectors as satsolver.py before starting workers.",
    )
    args = parser.parse_args(sys.argv[1:] if argv is None else argv)

    try:
        num_vars, clauses = io.parse_dimacs_file(args.input_path)
        model = solve_cnf_fullcpu(
            num_vars,
            clauses,
            workers=args.workers,
            use_detectors=args.use_detectors,
        )
        if model is not None and not base.model_satisfies(clauses, model):
            raise RuntimeError("Internal error: produced model does not satisfy the input CNF")
        write_result(args.output_path, model)
    except Exception as exc:
        print(f"Error: {exc}", file=sys.stderr)
        return 1

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
