from __future__ import annotations

import argparse
import concurrent.futures
import os
import subprocess
import sys
import tempfile
from pathlib import Path
from statistics import mean, median
from time import perf_counter

import satsolver
from tools import checker


PORTFOLIO_DISABLE_ENV = "SATSOLVER_DISABLE_PORTFOLIO"


def format_elapsed_samples(samples: list[float]) -> str:
    return "[" + ", ".join(f"{sample:.4f}" for sample in samples) + "]"


def summarize_elapsed_samples(samples: list[float]) -> tuple[float, float, float]:
    return min(samples), mean(samples), median(samples)


def run_case(
    *,
    case_index: int,
    folder: str,
    cnf_path: str,
    cli_script: str,
    python_executable: str,
    repeat: int,
    brute_force_var_limit: int,
    case_timeout: float | None,
    disable_solver_portfolio: bool,
) -> dict[str, object]:
    path = Path(cnf_path)
    start_case = perf_counter()
    elapsed_samples: list[float] = []
    statuses: list[str] = []
    validations: list[str] = []
    num_vars = 0
    num_clauses = 0

    try:
        num_vars, clauses = satsolver.parse_dimacs_file(str(path))
        num_clauses = len(clauses)

        with tempfile.TemporaryDirectory(prefix="sat-par-bench-") as scratch_dir_str:
            scratch_dir = Path(scratch_dir_str)
            for repeat_index in range(repeat):
                output_path = scratch_dir / f"case_{case_index}_r{repeat_index}.out"
                command = [python_executable, cli_script, str(path), str(output_path)]
                env = os.environ.copy()
                if disable_solver_portfolio:
                    env[PORTFOLIO_DISABLE_ENV] = "1"

                start = perf_counter()
                completed = subprocess.run(
                    command,
                    capture_output=True,
                    text=True,
                    check=False,
                    timeout=case_timeout,
                    env=env,
                )
                elapsed = perf_counter() - start
                elapsed_samples.append(elapsed)

                if completed.returncode != 0:
                    stderr = completed.stderr.strip() or completed.stdout.strip() or "no error output"
                    raise RuntimeError(f"solver exited with code {completed.returncode}: {stderr}")

                output_text = output_path.read_text(encoding="utf-8")
                status, _ = checker.parse_output_text(output_text)
                validation = checker.validate_output_text(
                    num_vars,
                    clauses,
                    output_text,
                    brute_force_var_limit=brute_force_var_limit,
                )
                statuses.append(status)
                validations.append(validation)

        distinct_statuses = sorted(set(statuses))
        if len(distinct_statuses) != 1:
            raise RuntimeError(f"inconsistent statuses across repeats: {distinct_statuses}")

        validation = validations[0]
        if len(set(validations)) != 1:
            validation = f"{validation} (details varied across repeats)"
        best_elapsed, avg_elapsed, median_elapsed = summarize_elapsed_samples(elapsed_samples)
        return {
            "case_index": case_index,
            "folder": folder,
            "name": path.name,
            "status": distinct_statuses[0],
            "ok": True,
            "validation": validation,
            "vars": num_vars,
            "clauses": num_clauses,
            "time": median_elapsed,
            "best": best_elapsed,
            "avg": avg_elapsed,
            "samples": elapsed_samples,
            "wall": perf_counter() - start_case,
        }
    except subprocess.TimeoutExpired as exc:
        validation = f"error: solver timed out after {exc.timeout}s"
    except Exception as exc:
        validation = f"error: {exc}"

    return {
        "case_index": case_index,
        "folder": folder,
        "name": path.name,
        "status": "ERROR",
        "ok": False,
        "validation": validation,
        "vars": num_vars,
        "clauses": num_clauses,
        "time": 0.0,
        "best": 0.0,
        "avg": 0.0,
        "samples": elapsed_samples,
        "wall": perf_counter() - start_case,
    }


def write_summary(handle, label: str, results: list[dict[str, object]], repeat: int) -> None:
    solved = [result for result in results if result["ok"]]
    sat = sum(1 for result in solved if result["status"] == "SAT")
    unsat = sum(1 for result in solved if result["status"] == "UNSAT")
    errors = len(results) - len(solved)
    total = sum(float(result["time"]) for result in solved)
    measured_total = sum(sum(float(sample) for sample in result["samples"]) for result in solved)
    avg_time = total / len(solved) if solved else 0.0
    median_time = median(float(result["time"]) for result in solved) if solved else 0.0
    max_time = max((float(result["time"]) for result in solved), default=0.0)
    print(
        (
            f"SUMMARY {label}: count={len(results)} solved_correctly={len(solved)} "
            f"sat={sat} unsat={unsat} errors={errors} repeat_count={repeat} "
            f"total={total:.4f}s avg={avg_time:.4f}s median={median_time:.4f}s "
            f"max={max_time:.4f}s measured_total={measured_total:.4f}s"
        ),
        file=handle,
    )


def parallel_benchmark(
    output_path: str,
    folders: list[str],
    *,
    cli_script: str,
    python_executable: str,
    repeat: int,
    jobs: int,
    brute_force_var_limit: int,
    case_timeout: float | None,
    disable_solver_portfolio: bool,
) -> int:
    if repeat < 1:
        raise ValueError("repeat must be at least 1")
    if jobs < 1:
        raise ValueError("jobs must be at least 1")

    cases: list[tuple[int, str, str]] = []
    for folder in folders:
        for path in sorted(Path(folder).glob("*.cnf")):
            cases.append((len(cases), folder, str(path)))

    suite_start = perf_counter()
    results: list[dict[str, object]] = []
    with concurrent.futures.ThreadPoolExecutor(max_workers=jobs) as executor:
        futures = [
            executor.submit(
                run_case,
                case_index=case_index,
                folder=folder,
                cnf_path=cnf_path,
                cli_script=cli_script,
                python_executable=python_executable,
                repeat=repeat,
                brute_force_var_limit=brute_force_var_limit,
                case_timeout=case_timeout,
                disable_solver_portfolio=disable_solver_portfolio,
            )
            for case_index, folder, cnf_path in cases
        ]
        for future in concurrent.futures.as_completed(futures):
            results.append(future.result())

    results.sort(key=lambda result: int(result["case_index"]))
    wall_clock = perf_counter() - suite_start

    with open(output_path, "w", encoding="utf-8") as handle:
        print("solver=satsolver", file=handle)
        print("mode=parallel_cli", file=handle)
        print(f"cli_script={Path(cli_script).resolve()}", file=handle)
        print(f"python_executable={python_executable}", file=handle)
        print(f"repeat={repeat}", file=handle)
        print(f"jobs={jobs}", file=handle)
        print(f"case_timeout={case_timeout}", file=handle)
        print(f"disable_solver_portfolio={disable_solver_portfolio}", file=handle)
        print("representative_time=median_of_repeats", file=handle)
        print(file=handle)

        for folder in folders:
            folder_results = [result for result in results if result["folder"] == folder]
            print(f"[{folder}]", file=handle)
            for result in folder_results:
                samples = [float(sample) for sample in result["samples"]]
                repeat_suffix = (
                    f" repeat_count={repeat} best={float(result['best']):.4f}s"
                    f" avg={float(result['avg']):.4f}s median={float(result['time']):.4f}s"
                    f" samples={format_elapsed_samples(samples)}"
                )
                print(
                    (
                        f"{result['name']}: {result['status']} ok={result['ok']} "
                        f"validation={result['validation']!r} vars={result['vars']} "
                        f"clauses={result['clauses']} time={float(result['time']):.4f}s"
                        f"{repeat_suffix} wall={float(result['wall']):.4f}s"
                    ),
                    file=handle,
                )
            write_summary(handle, folder, folder_results, repeat)
            print(file=handle)

        print("[overall]", file=handle)
        write_summary(handle, "overall", results, repeat)
        print(f"wall_clock={wall_clock:.4f}s", file=handle)
        print("slowest_cases:", file=handle)
        for result in sorted(results, key=lambda item: float(item["time"]), reverse=True)[:10]:
            print(
                (
                    f"{result['folder']}/{result['name']}: {result['status']} ok={result['ok']} "
                    f"validation={result['validation']!r} vars={result['vars']} "
                    f"clauses={result['clauses']} time={float(result['time']):.4f}s "
                    f"samples={format_elapsed_samples([float(sample) for sample in result['samples']])}"
                ),
                file=handle,
            )

    return 1 if any(not result["ok"] for result in results) else 0


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Run many SAT solver CLI cases concurrently to measure throughput and load CPU."
    )
    parser.add_argument("output_path")
    parser.add_argument("folders", nargs="+")
    parser.add_argument("--cli-script", default="satsolver.py")
    parser.add_argument("--python-executable", default=sys.executable)
    parser.add_argument("--repeat", type=int, default=1)
    parser.add_argument("--jobs", type=int, default=os.cpu_count() or 1)
    parser.add_argument("--bruteforce-var-limit", type=int, default=16)
    parser.add_argument("--case-timeout", type=float, default=60.0)
    parser.add_argument(
        "--disable-solver-portfolio",
        action="store_true",
        help="Set SATSOLVER_DISABLE_PORTFOLIO=1 in each solver subprocess to avoid nested worker oversubscription.",
    )
    args = parser.parse_args(sys.argv[1:] if argv is None else argv)
    return parallel_benchmark(
        args.output_path,
        args.folders,
        cli_script=args.cli_script,
        python_executable=args.python_executable,
        repeat=args.repeat,
        jobs=args.jobs,
        brute_force_var_limit=args.bruteforce_var_limit,
        case_timeout=args.case_timeout,
        disable_solver_portfolio=args.disable_solver_portfolio,
    )


if __name__ == "__main__":
    raise SystemExit(main())
