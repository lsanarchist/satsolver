from __future__ import annotations

import importlib
import sys
from pathlib import Path
from statistics import mean, median
from time import perf_counter


def benchmark_solver(module_name: str, output_path: str, folders: list[str]) -> int:
    module = importlib.import_module(module_name)

    parse_dimacs_file = module.parse_dimacs_file
    solve_cnf = module.solve_cnf
    model_satisfies = module.model_satisfies

    all_results: list[tuple[str, str, float, bool, bool, int, int]] = []
    suite_start = perf_counter()

    with open(output_path, "w", encoding="utf-8") as handle:
        print(f"solver={module_name}", file=handle)
        print(file=handle)

        for folder in folders:
            paths = sorted(Path(folder).glob("*.cnf"))
            print(f"[{folder}]", file=handle)
            results = []

            for path in paths:
                num_vars, clauses = parse_dimacs_file(str(path))
                start = perf_counter()
                model = solve_cnf(num_vars, clauses)
                elapsed = perf_counter() - start
                sat = model is not None
                ok = (model is None) or model_satisfies(clauses, model)
                results.append((path.name, elapsed, sat, ok, num_vars, len(clauses)))
                status = "SAT" if sat else "UNSAT"
                print(
                    f"{path.name}: {status} ok={ok} vars={num_vars} clauses={len(clauses)} time={elapsed:.4f}s",
                    file=handle,
                )

            folder_times = [result[1] for result in results]
            print(
                (
                    f"SUMMARY {folder}: count={len(results)} total={sum(folder_times):.4f}s "
                    f"avg={mean(folder_times):.4f}s median={median(folder_times):.4f}s "
                    f"max={max(folder_times):.4f}s"
                ),
                file=handle,
            )
            print(file=handle)

            all_results.extend((folder, *result) for result in results)

        total_elapsed = perf_counter() - suite_start
        all_times = [result[2] for result in all_results]
        print("[overall]", file=handle)
        print(
            (
                f"total_cases={len(all_results)} total={sum(all_times):.4f}s "
                f"avg={mean(all_times):.4f}s median={median(all_times):.4f}s "
                f"max={max(all_times):.4f}s wall_clock={total_elapsed:.4f}s"
            ),
            file=handle,
        )
        print("slowest_cases:", file=handle)
        for folder, name, elapsed, sat, ok, num_vars, num_clauses in sorted(
            all_results, key=lambda result: result[2], reverse=True
        )[:10]:
            status = "SAT" if sat else "UNSAT"
            print(
                (
                    f"{folder}/{name}: {status} ok={ok} vars={num_vars} "
                    f"clauses={num_clauses} time={elapsed:.4f}s"
                ),
                file=handle,
            )

    return 0


def main(argv: list[str] | None = None) -> int:
    arguments = sys.argv[1:] if argv is None else argv
    if len(arguments) < 3:
        print(
            "Usage: python benchmark_suite.py <module_name> <output.txt> <folder> [<folder> ...]",
            file=sys.stderr,
        )
        return 1

    module_name = arguments[0]
    output_path = arguments[1]
    folders = arguments[2:]
    return benchmark_solver(module_name, output_path, folders)


if __name__ == "__main__":
    raise SystemExit(main())
