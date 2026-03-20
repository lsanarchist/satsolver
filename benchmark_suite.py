from __future__ import annotations

import argparse
import importlib
import subprocess
import sys
import tempfile
from pathlib import Path
from statistics import mean, median
from time import perf_counter

from tools import checker


def format_elapsed_samples(samples: list[float]) -> str:
    return "[" + ", ".join(f"{sample:.4f}" for sample in samples) + "]"


def summarize_elapsed_samples(samples: list[float]) -> tuple[float, float, float]:
    return min(samples), mean(samples), median(samples)


def summarize_times(times: list[float]) -> tuple[float, float, float, float]:
    if not times:
        return 0.0, 0.0, 0.0, 0.0
    return sum(times), mean(times), median(times), max(times)


def validate_case_output(
    module,
    num_vars: int,
    clauses: list[list[int]],
    model,
    scratch_dir: Path,
    case_id: str,
    brute_force_var_limit: int,
) -> str:
    output_path = scratch_dir / f"{case_id}.out"
    module.write_result(str(output_path), model)
    output_text = output_path.read_text(encoding="utf-8")
    return checker.validate_output_text(
        num_vars,
        clauses,
        output_text,
        brute_force_var_limit=brute_force_var_limit,
    )


def run_case_via_module(
    module,
    num_vars: int,
    clauses: list[list[int]],
    scratch_dir: Path,
    case_id: str,
    brute_force_var_limit: int,
) -> tuple[str, str, float]:
    start = perf_counter()
    model = module.solve_cnf(num_vars, clauses)
    elapsed = perf_counter() - start
    status = "SAT" if model is not None else "UNSAT"
    validation = validate_case_output(
        module,
        num_vars,
        clauses,
        model,
        scratch_dir,
        case_id,
        brute_force_var_limit,
    )
    return status, validation, elapsed


def run_case_via_cli(
    cli_script: Path,
    python_executable: str,
    cnf_path: Path,
    num_vars: int,
    clauses: list[list[int]],
    scratch_dir: Path,
    case_id: str,
    brute_force_var_limit: int,
) -> tuple[str, str, float]:
    output_file = scratch_dir / f"{case_id}.out"
    command = [python_executable, str(cli_script), str(cnf_path), str(output_file)]
    start = perf_counter()
    completed = subprocess.run(command, capture_output=True, text=True, check=False)
    elapsed = perf_counter() - start

    if completed.returncode != 0:
        stderr = completed.stderr.strip() or completed.stdout.strip() or "no error output"
        raise RuntimeError(f"solver exited with code {completed.returncode}: {stderr}")

    output_text = output_file.read_text(encoding="utf-8")
    status, _ = checker.parse_output_text(output_text)
    validation = checker.validate_output_text(
        num_vars,
        clauses,
        output_text,
        brute_force_var_limit=brute_force_var_limit,
    )
    return status, validation, elapsed


def benchmark_solver(
    module_name: str,
    output_path: str,
    folders: list[str],
    brute_force_var_limit: int,
    cli_script: str | None = None,
    python_executable: str | None = None,
    repeat: int = 1,
) -> int:
    if repeat < 1:
        raise ValueError("repeat must be at least 1")

    module = importlib.import_module(module_name)

    parse_dimacs_file = module.parse_dimacs_file
    cli_mode = cli_script is not None
    cli_script_path = Path(cli_script).resolve() if cli_script is not None else None
    python_cmd = sys.executable if python_executable is None else python_executable

    all_results: list[tuple[str, str, float, str, bool, str, int, int, list[float]]] = []
    suite_start = perf_counter()

    with tempfile.TemporaryDirectory(prefix="sat-bench-") as scratch_dir_str:
        scratch_dir = Path(scratch_dir_str)

        with open(output_path, "w", encoding="utf-8") as handle:
            print(f"solver={module_name}", file=handle)
            print(f"mode={'cli' if cli_mode else 'module'}", file=handle)
            if cli_mode:
                print(f"cli_script={cli_script_path}", file=handle)
                print(f"python_executable={python_cmd}", file=handle)
            print(f"bruteforce_var_limit={brute_force_var_limit}", file=handle)
            print(f"repeat={repeat}", file=handle)
            if repeat > 1:
                print("representative_time=median_of_repeats", file=handle)
            print(file=handle)

            for folder in folders:
                paths = sorted(Path(folder).glob("*.cnf"))
                print(f"[{folder}]", file=handle)
                results = []

                for case_index, path in enumerate(paths):
                    status = "ERROR"
                    ok = False
                    validation = ""
                    num_vars = 0
                    num_clauses = 0
                    elapsed = 0.0
                    elapsed_samples: list[float] = []

                    try:
                        num_vars, clauses = parse_dimacs_file(str(path))
                        num_clauses = len(clauses)
                        statuses = []
                        validations = []
                        for repeat_index in range(repeat):
                            repeat_case_id = f"{folder}_{case_index}_r{repeat_index}"
                            if cli_mode:
                                assert cli_script_path is not None
                                status, validation, elapsed = run_case_via_cli(
                                    cli_script_path,
                                    python_cmd,
                                    path,
                                    num_vars,
                                    clauses,
                                    scratch_dir,
                                    repeat_case_id,
                                    brute_force_var_limit,
                                )
                            else:
                                status, validation, elapsed = run_case_via_module(
                                    module,
                                    num_vars,
                                    clauses,
                                    scratch_dir,
                                    repeat_case_id,
                                    brute_force_var_limit,
                                )
                            statuses.append(status)
                            validations.append(validation)
                            elapsed_samples.append(elapsed)
                        distinct_statuses = sorted(set(statuses))
                        if len(distinct_statuses) != 1:
                            raise RuntimeError(
                                f"inconsistent statuses across repeats: {distinct_statuses}"
                            )
                        status = distinct_statuses[0]
                        validation = validations[0]
                        if len(set(validations)) != 1:
                            validation = f"{validation} (details varied across repeats)"
                        _, _, elapsed = summarize_elapsed_samples(elapsed_samples)
                        ok = True
                    except Exception as exc:
                        elapsed = 0.0
                        validation = f"error: {exc}"

                    results.append(
                        (path.name, elapsed, status, ok, validation, num_vars, num_clauses, elapsed_samples)
                    )
                    repeat_suffix = ""
                    if repeat > 1:
                        if elapsed_samples:
                            best_elapsed, mean_elapsed, median_elapsed = summarize_elapsed_samples(
                                elapsed_samples
                            )
                            repeat_suffix = (
                                f" repeat_count={repeat} best={best_elapsed:.4f}s"
                                f" avg={mean_elapsed:.4f}s median={median_elapsed:.4f}s"
                                f" samples={format_elapsed_samples(elapsed_samples)}"
                            )
                        else:
                            repeat_suffix = f" repeat_count={repeat} samples=[]"
                    print(
                        (
                            f"{path.name}: {status} ok={ok} validation={validation!r} "
                            f"vars={num_vars} clauses={num_clauses} time={elapsed:.4f}s"
                            f"{repeat_suffix}"
                        ),
                        file=handle,
                    )

                folder_times = [result[1] for result in results]
                folder_measured_times = [sum(result[7]) for result in results]
                solved_correctly = sum(1 for result in results if result[3])
                sat_count = sum(1 for result in results if result[2] == "SAT")
                unsat_count = sum(1 for result in results if result[2] == "UNSAT")
                error_count = sum(1 for result in results if result[2] == "ERROR")
                total_time, avg_time, median_time, max_time = summarize_times(folder_times)
                print(
                    (
                        f"SUMMARY {folder}: count={len(results)} solved_correctly={solved_correctly} "
                        f"sat={sat_count} unsat={unsat_count} errors={error_count} "
                        f"repeat_count={repeat} total={total_time:.4f}s avg={avg_time:.4f}s "
                        f"median={median_time:.4f}s max={max_time:.4f}s"
                        f"{f' measured_total={sum(folder_measured_times):.4f}s' if repeat > 1 else ''}"
                    ),
                    file=handle,
                )
                print(file=handle)

                all_results.extend((folder, *result) for result in results)

            total_elapsed = perf_counter() - suite_start
            all_times = [result[2] for result in all_results]
            all_measured_times = [sum(result[8]) for result in all_results]
            solved_correctly = sum(1 for result in all_results if result[4])
            sat_count = sum(1 for result in all_results if result[3] == "SAT")
            unsat_count = sum(1 for result in all_results if result[3] == "UNSAT")
            error_count = sum(1 for result in all_results if result[3] == "ERROR")
            total_time, avg_time, median_time, max_time = summarize_times(all_times)
            print("[overall]", file=handle)
            print(
                (
                    f"total_cases={len(all_results)} solved_correctly={solved_correctly} "
                    f"sat={sat_count} unsat={unsat_count} errors={error_count} "
                    f"repeat_count={repeat} total={total_time:.4f}s avg={avg_time:.4f}s "
                    f"median={median_time:.4f}s max={max_time:.4f}s "
                    f"{f'measured_total={sum(all_measured_times):.4f}s ' if repeat > 1 else ''}"
                    f"wall_clock={total_elapsed:.4f}s"
                ),
                file=handle,
            )
            print("slowest_cases:", file=handle)
            for folder, name, elapsed, status, ok, validation, num_vars, num_clauses, elapsed_samples in sorted(
                all_results, key=lambda result: result[2], reverse=True
            )[:10]:
                repeat_suffix = ""
                if repeat > 1:
                    repeat_suffix = f" samples={format_elapsed_samples(elapsed_samples)}"
                print(
                    (
                        f"{folder}/{name}: {status} ok={ok} validation={validation!r} "
                        f"vars={num_vars} clauses={num_clauses} time={elapsed:.4f}s"
                        f"{repeat_suffix}"
                    ),
                    file=handle,
                )

    return 0


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Benchmark and validate a SAT solver module.")
    parser.add_argument("module_name")
    parser.add_argument("output_path")
    parser.add_argument("folders", nargs="+")
    parser.add_argument(
        "--bruteforce-var-limit",
        type=int,
        default=16,
        help="Brute-force UNSAT validation only when num_vars is at most this limit",
    )
    parser.add_argument(
        "--cli-script",
        help="Optional path to a solver script to benchmark via the exact CLI interface",
    )
    parser.add_argument(
        "--python-executable",
        default=sys.executable,
        help="Python executable to use with --cli-script",
    )
    parser.add_argument(
        "--repeat",
        type=int,
        default=1,
        help="Run each case this many times and report median representative time",
    )
    args = parser.parse_args(sys.argv[1:] if argv is None else argv)
    return benchmark_solver(
        args.module_name,
        args.output_path,
        args.folders,
        args.bruteforce_var_limit,
        cli_script=args.cli_script,
        python_executable=args.python_executable,
        repeat=args.repeat,
    )


if __name__ == "__main__":
    raise SystemExit(main())
