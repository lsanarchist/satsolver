from __future__ import annotations

import argparse
import subprocess
import sys
import tempfile
from dataclasses import dataclass
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
DEFAULT_BENCHMARK_FOLDERS = (
    "small",
    "medium",
    "large",
    "special",
    "satlib_subset",
    "satlib_more",
)
SMOKE_SAT_CASE = "small/test_1.cnf"
SMOKE_UNSAT_CASE = "special/tseitin.cnf"
IGNORED_PARTS = {".git", "__pycache__"}
IGNORED_PREFIXES = (".venv",)


@dataclass(frozen=True)
class CommandStep:
    description: str
    command: tuple[str, ...]


def iter_python_sources(root: Path) -> list[Path]:
    sources: list[Path] = []
    for path in root.rglob("*.py"):
        relative = path.relative_to(root)
        if any(part in IGNORED_PARTS or part.startswith(IGNORED_PREFIXES) for part in relative.parts):
            continue
        sources.append(relative)
    return sorted(sources, key=lambda candidate: candidate.as_posix())


def build_compile_command(python_executable: str, root: Path) -> list[str]:
    sources = [str(path) for path in iter_python_sources(root)]
    return [python_executable, "-m", "py_compile", *sources]


def build_benchmark_command(
    python_executable: str,
    module_name: str,
    output_path: str,
    folders: list[str],
    brute_force_var_limit: int,
    repeat: int,
    *,
    cli_script: str | None = None,
) -> list[str]:
    command = [
        python_executable,
        str(ROOT / "benchmark_suite.py"),
        module_name,
        output_path,
        *folders,
        "--bruteforce-var-limit",
        str(brute_force_var_limit),
    ]
    if cli_script is not None:
        command.extend(["--cli-script", cli_script, "--python-executable", python_executable])
    if repeat != 1:
        command.extend(["--repeat", str(repeat)])
    return command


def run_step(step: CommandStep, *, cwd: Path) -> None:
    print(f"== {step.description} ==")
    print(" ".join(step.command))
    subprocess.run(step.command, cwd=cwd, check=True)


def build_steps(
    *,
    python_executable: str,
    solver_script: str,
    module_name: str,
    benchmark_mode: str,
    benchmark_folders: list[str],
    benchmark_output: str | None,
    brute_force_var_limit: int,
    repeat: int,
) -> tuple[list[CommandStep], str | None]:
    benchmark_report = benchmark_output
    steps: list[CommandStep] = [
        CommandStep(
            "Compile Python sources",
            tuple(build_compile_command(python_executable, ROOT)),
        ),
        CommandStep(
            "Validate agent queue control plane",
            (python_executable, "tools/agent_queue_check.py"),
        ),
        CommandStep(
            "Run unit tests",
            (python_executable, "-m", "unittest", "discover", "-s", "tests", "-q"),
        ),
    ]

    with tempfile.NamedTemporaryFile(
        prefix="sat-codex-smoke-sat-",
        suffix=".txt",
        delete=False,
    ) as sat_handle:
        sat_output = sat_handle.name
    with tempfile.NamedTemporaryFile(
        prefix="sat-codex-smoke-unsat-",
        suffix=".txt",
        delete=False,
    ) as unsat_handle:
        unsat_output = unsat_handle.name

    steps.extend(
        [
            CommandStep(
                "Run SAT smoke case",
                (python_executable, solver_script, SMOKE_SAT_CASE, sat_output),
            ),
            CommandStep(
                "Validate SAT smoke output",
                (
                    python_executable,
                    "tools/checker.py",
                    SMOKE_SAT_CASE,
                    sat_output,
                ),
            ),
            CommandStep(
                "Run UNSAT smoke case",
                (python_executable, solver_script, SMOKE_UNSAT_CASE, unsat_output),
            ),
            CommandStep(
                "Validate UNSAT smoke output",
                (
                    python_executable,
                    "tools/checker.py",
                    SMOKE_UNSAT_CASE,
                    unsat_output,
                    "--bruteforce-var-limit",
                    "0",
                ),
            ),
        ]
    )

    if benchmark_mode != "none":
        if benchmark_report is None:
            with tempfile.NamedTemporaryFile(
                prefix="sat-codex-benchmark-",
                suffix=".txt",
                delete=False,
            ) as handle:
                benchmark_report = handle.name

        benchmark_command = build_benchmark_command(
            python_executable,
            module_name,
            benchmark_report,
            benchmark_folders,
            brute_force_var_limit,
            repeat,
            cli_script=solver_script if benchmark_mode == "cli" else None,
        )
        description = (
            "Run benchmark suite in exact-CLI mode"
            if benchmark_mode == "cli"
            else "Run benchmark suite in module mode"
        )
        steps.append(CommandStep(description, tuple(benchmark_command)))

    return steps, benchmark_report


def parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Run the standard verification flow for queued Codex work in this repo."
    )
    parser.add_argument(
        "--python-executable",
        default=sys.executable,
        help="Python interpreter used for compile, tests, smoke checks, and benchmarks",
    )
    parser.add_argument(
        "--solver-script",
        default="satsolver.py",
        help="Solver CLI script used for smoke checks and CLI benchmarks",
    )
    parser.add_argument(
        "--module-name",
        default="satsolver",
        help="Module name used for module-mode benchmarks",
    )
    parser.add_argument(
        "--benchmark-mode",
        choices=("none", "module", "cli"),
        default="none",
        help="Optional benchmark step to append after compile, tests, and smoke checks",
    )
    parser.add_argument(
        "--benchmark-folders",
        nargs="+",
        default=list(DEFAULT_BENCHMARK_FOLDERS),
        help="Benchmark folders passed to benchmark_suite.py",
    )
    parser.add_argument(
        "--benchmark-output",
        help="Optional output path for benchmark_suite.py. Defaults to a temp file when benchmarking.",
    )
    parser.add_argument(
        "--repeat",
        type=int,
        default=1,
        help="Repeat count forwarded to benchmark_suite.py when benchmarking",
    )
    parser.add_argument(
        "--bruteforce-var-limit",
        type=int,
        default=16,
        help="Brute-force limit forwarded to benchmark_suite.py",
    )
    args = parser.parse_args(sys.argv[1:] if argv is None else argv)
    if args.repeat < 1:
        parser.error("--repeat must be at least 1")
    return args


def main(argv: list[str] | None = None) -> int:
    args = parse_args(argv)
    try:
        steps, benchmark_report = build_steps(
            python_executable=args.python_executable,
            solver_script=args.solver_script,
            module_name=args.module_name,
            benchmark_mode=args.benchmark_mode,
            benchmark_folders=args.benchmark_folders,
            benchmark_output=args.benchmark_output,
            brute_force_var_limit=args.bruteforce_var_limit,
            repeat=args.repeat,
        )
        for step in steps:
            run_step(step, cwd=ROOT)
    except subprocess.CalledProcessError as exc:
        return exc.returncode or 1

    if benchmark_report is not None:
        print(f"benchmark_report={benchmark_report}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
