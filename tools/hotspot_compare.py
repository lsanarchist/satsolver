from __future__ import annotations

import argparse
import importlib
import sys
import tempfile
from dataclasses import dataclass
from pathlib import Path
from statistics import mean, median

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

import benchmark_suite
import satsolver


@dataclass(slots=True)
class RunnerConfig:
    label: str
    module_name: str | None
    cli_script: Path | None
    python_executable: str
    module: object | None


@dataclass(slots=True)
class CaseTiming:
    path: str
    status: str
    validation: str
    elapsed_s: float
    elapsed_samples: list[float]


@dataclass(slots=True)
class OrderComparison:
    order_name: str
    baseline_total_s: float
    candidate_total_s: float
    case_rows: list[tuple[CaseTiming, CaseTiming]]


def summarize_elapsed_samples(samples: list[float]) -> tuple[float, float, float]:
    return min(samples), mean(samples), median(samples)


def format_elapsed_samples(samples: list[float]) -> str:
    return "[" + ", ".join(f"{sample:.4f}" for sample in samples) + "]"


def load_runner(
    label: str,
    module_name: str | None,
    cli_script: str | None,
    python_executable: str,
) -> RunnerConfig:
    if (module_name is None) == (cli_script is None):
        raise ValueError(f"{label} runner needs exactly one of module_name or cli_script")

    if module_name is not None:
        return RunnerConfig(
            label=label,
            module_name=module_name,
            cli_script=None,
            python_executable=python_executable,
            module=importlib.import_module(module_name),
        )

    return RunnerConfig(
        label=label,
        module_name=None,
        cli_script=Path(cli_script).resolve(),
        python_executable=python_executable,
        module=None,
    )


def run_runner_case(
    runner: RunnerConfig,
    cnf_path: Path,
    num_vars: int,
    clauses: list[list[int]],
    scratch_dir: Path,
    case_id: str,
    brute_force_var_limit: int,
    repeat: int,
) -> CaseTiming:
    if repeat < 1:
        raise ValueError("repeat must be at least 1")

    statuses: list[str] = []
    validations: list[str] = []
    elapsed_samples: list[float] = []

    for repeat_index in range(repeat):
        repeat_case_id = f"{case_id}_{repeat_index}"
        if runner.module is not None:
            status, validation, elapsed = benchmark_suite.run_case_via_module(
                runner.module,
                num_vars,
                clauses,
                scratch_dir,
                repeat_case_id,
                brute_force_var_limit,
            )
        else:
            assert runner.cli_script is not None
            status, validation, elapsed = benchmark_suite.run_case_via_cli(
                runner.cli_script,
                runner.python_executable,
                cnf_path,
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
            f"{runner.label} produced inconsistent statuses across repeats: {distinct_statuses}"
        )

    distinct_validations = sorted(set(validations))
    if len(distinct_validations) != 1:
        raise RuntimeError(
            f"{runner.label} produced inconsistent validations across repeats: {distinct_validations}"
        )

    _, _, representative_elapsed = summarize_elapsed_samples(elapsed_samples)
    return CaseTiming(
        path=str(cnf_path),
        status=statuses[0],
        validation=validations[0],
        elapsed_s=representative_elapsed,
        elapsed_samples=elapsed_samples,
    )


def compare_runners(
    baseline: RunnerConfig,
    candidate: RunnerConfig,
    case_paths: list[str],
    brute_force_var_limit: int = 16,
    repeat: int = 1,
) -> list[OrderComparison]:
    canonical_cases = [Path(path) for path in case_paths]
    comparisons: list[OrderComparison] = []

    with tempfile.TemporaryDirectory(prefix="sat-hotspot-compare-") as scratch_dir_str:
        scratch_dir = Path(scratch_dir_str)

        for order_name, ordered_cases in (
            ("forward", canonical_cases),
            ("reverse", list(reversed(canonical_cases))),
        ):
            rows: list[tuple[CaseTiming, CaseTiming]] = []
            baseline_total = 0.0
            candidate_total = 0.0

            for case_index, cnf_path in enumerate(ordered_cases):
                num_vars, clauses = satsolver.parse_dimacs_file(str(cnf_path))
                baseline_case = run_runner_case(
                    baseline,
                    cnf_path,
                    num_vars,
                    clauses,
                    scratch_dir,
                    f"{order_name}_baseline_{case_index}",
                    brute_force_var_limit,
                    repeat,
                )
                candidate_case = run_runner_case(
                    candidate,
                    cnf_path,
                    num_vars,
                    clauses,
                    scratch_dir,
                    f"{order_name}_candidate_{case_index}",
                    brute_force_var_limit,
                    repeat,
                )
                rows.append((baseline_case, candidate_case))
                baseline_total += baseline_case.elapsed_s
                candidate_total += candidate_case.elapsed_s

            comparisons.append(
                OrderComparison(
                    order_name=order_name,
                    baseline_total_s=baseline_total,
                    candidate_total_s=candidate_total,
                    case_rows=rows,
                )
            )

    return comparisons


def render_comparisons(
    baseline: RunnerConfig,
    candidate: RunnerConfig,
    comparisons: list[OrderComparison],
    repeat: int,
) -> str:
    lines = [
        f"baseline={baseline.module_name or baseline.cli_script}",
        f"candidate={candidate.module_name or candidate.cli_script}",
        f"repeat={repeat}",
        "",
    ]

    for comparison in comparisons:
        lines.append(
            (
                f"[{comparison.order_name}] baseline_total={comparison.baseline_total_s:.4f}s "
                f"candidate_total={comparison.candidate_total_s:.4f}s"
            )
        )
        for baseline_case, candidate_case in comparison.case_rows:
            repeat_suffix = ""
            if repeat > 1:
                repeat_suffix = (
                    f" baseline_samples={format_elapsed_samples(baseline_case.elapsed_samples)}"
                    f" candidate_samples={format_elapsed_samples(candidate_case.elapsed_samples)}"
                )
            lines.append(
                (
                    f"{baseline_case.path}: baseline={baseline_case.elapsed_s:.4f}s "
                    f"candidate={candidate_case.elapsed_s:.4f}s "
                    f"status={baseline_case.status}/{candidate_case.status} "
                    f"validation={baseline_case.validation!r}/{candidate_case.validation!r}"
                    f"{repeat_suffix}"
                )
            )
        lines.append("")

    if len(comparisons) == 2:
        avg_baseline = (comparisons[0].baseline_total_s + comparisons[1].baseline_total_s) / 2.0
        avg_candidate = (comparisons[0].candidate_total_s + comparisons[1].candidate_total_s) / 2.0
        lines.append(
            f"[two-order-average] baseline={avg_baseline:.4f}s candidate={avg_candidate:.4f}s"
        )

    return "\n".join(lines)


def build_argument_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        description="Compare two SAT solver runners on an ordered hotspot case slice."
    )
    parser.add_argument("cases", nargs="+", help="CNF case paths to compare in order")
    parser.add_argument("--baseline-module")
    parser.add_argument("--baseline-cli-script")
    parser.add_argument(
        "--baseline-python-executable",
        default=sys.executable,
        help="Python executable for --baseline-cli-script",
    )
    parser.add_argument("--candidate-module")
    parser.add_argument("--candidate-cli-script")
    parser.add_argument(
        "--candidate-python-executable",
        default=sys.executable,
        help="Python executable for --candidate-cli-script",
    )
    parser.add_argument(
        "--bruteforce-var-limit",
        type=int,
        default=16,
        help="Brute-force UNSAT validation only when num_vars is at most this limit",
    )
    parser.add_argument(
        "--repeat",
        type=int,
        default=1,
        help="Run each case this many times per runner and use the median as representative time",
    )
    return parser


def main(argv: list[str] | None = None) -> int:
    parser = build_argument_parser()
    args = parser.parse_args(sys.argv[1:] if argv is None else argv)

    baseline = load_runner(
        "baseline",
        args.baseline_module,
        args.baseline_cli_script,
        args.baseline_python_executable,
    )
    candidate = load_runner(
        "candidate",
        args.candidate_module,
        args.candidate_cli_script,
        args.candidate_python_executable,
    )
    comparisons = compare_runners(
        baseline,
        candidate,
        args.cases,
        brute_force_var_limit=args.bruteforce_var_limit,
        repeat=args.repeat,
    )
    print(render_comparisons(baseline, candidate, comparisons, args.repeat))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
