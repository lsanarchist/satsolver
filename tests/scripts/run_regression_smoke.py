from __future__ import annotations

import argparse
import csv
import subprocess
import sys
import tempfile
from dataclasses import dataclass
from pathlib import Path
from time import perf_counter

ROOT = Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

import satsolver
from tools import checker


@dataclass(slots=True)
class ManifestRow:
    cnf_path: Path
    expected: str
    detector: str
    max_seconds: float
    mode: str
    notes: str


@dataclass(slots=True)
class SmokeResult:
    path: Path
    mode: str
    status: str
    elapsed: float
    ok: bool
    details: str


def resolve_case_path(manifest_path: Path, value: str) -> Path:
    candidate = Path(value)
    if candidate.is_absolute():
        return candidate
    repo_candidate = ROOT / candidate
    if repo_candidate.exists():
        return repo_candidate
    return manifest_path.parent / candidate


def read_manifest(manifest_path: Path) -> list[ManifestRow]:
    rows: list[ManifestRow] = []
    with manifest_path.open("r", encoding="utf-8", newline="") as handle:
        reader = csv.DictReader(handle, delimiter="\t")
        for row in reader:
            rows.append(
                ManifestRow(
                    cnf_path=resolve_case_path(manifest_path, row["path"]),
                    expected=row["expected"],
                    detector=row.get("detector", "any"),
                    max_seconds=float(row.get("max_seconds", "60") or "60"),
                    mode=row.get("mode", "solve"),
                    notes=row.get("notes", ""),
                )
            )
    return rows


def discover_manifests(suite: Path) -> list[Path]:
    if suite.is_file():
        return [suite]
    return sorted(suite.rglob("MANIFEST.tsv"))


def detector_result(cnf_path: Path) -> bool:
    num_vars, clauses = satsolver.parse_dimacs_file(str(cnf_path))
    return satsolver.graph_coloring_mycielski_unsat(num_vars, clauses)


def portfolio_result(cnf_path: Path) -> bool:
    num_vars, clauses = satsolver.parse_dimacs_file(str(cnf_path))
    return satsolver.should_use_parallel_portfolio(num_vars, clauses)


def run_solver(
    solver: Path,
    cnf_path: Path,
    output_path: Path,
    timeout: float,
) -> tuple[int, float, str, str]:
    start = perf_counter()
    completed = subprocess.run(
        [sys.executable, str(solver), str(cnf_path), str(output_path)],
        timeout=timeout,
        capture_output=True,
        text=True,
        check=False,
    )
    elapsed = perf_counter() - start
    return completed.returncode, elapsed, completed.stdout, completed.stderr


def check_detector(row: ManifestRow) -> SmokeResult:
    start = perf_counter()
    try:
        actual = detector_result(row.cnf_path)
        elapsed = perf_counter() - start
        if row.detector in {"true", "false"}:
            expected = row.detector == "true"
            if actual != expected:
                return SmokeResult(
                    row.cnf_path,
                    row.mode,
                    "FAIL",
                    elapsed,
                    False,
                    f"detector expected {expected}, got {actual}",
                )
        return SmokeResult(row.cnf_path, row.mode, "OK", elapsed, True, f"detector={actual}")
    except Exception as exc:
        return SmokeResult(row.cnf_path, row.mode, "FAIL", 0.0, False, str(exc))


def check_invalid(row: ManifestRow, solver: Path, scratch_dir: Path) -> SmokeResult:
    output_path = scratch_dir / f"{row.cnf_path.stem}.out"
    try:
        returncode, elapsed, stdout, stderr = run_solver(
            solver,
            row.cnf_path,
            output_path,
            row.max_seconds,
        )
    except subprocess.TimeoutExpired:
        return SmokeResult(row.cnf_path, row.mode, "TIMEOUT", row.max_seconds, False, "timeout")

    if returncode == 0:
        return SmokeResult(row.cnf_path, row.mode, "FAIL", elapsed, False, "invalid DIMACS returned 0")
    if output_path.exists() and output_path.read_text(encoding="utf-8").strip():
        return SmokeResult(row.cnf_path, row.mode, "FAIL", elapsed, False, "invalid DIMACS wrote nonempty output")
    message = (stderr.strip() or stdout.strip() or "nonzero exit").splitlines()[0]
    return SmokeResult(row.cnf_path, row.mode, "OK", elapsed, True, message)


def check_solve(row: ManifestRow, solver: Path, scratch_dir: Path, brute_force_var_limit: int) -> SmokeResult:
    output_path = scratch_dir / f"{row.cnf_path.stem}.out"
    try:
        returncode, elapsed, stdout, stderr = run_solver(
            solver,
            row.cnf_path,
            output_path,
            row.max_seconds,
        )
    except subprocess.TimeoutExpired:
        return SmokeResult(row.cnf_path, row.mode, "TIMEOUT", row.max_seconds, False, "timeout")

    if elapsed > row.max_seconds:
        return SmokeResult(row.cnf_path, row.mode, "TIMEOUT", elapsed, False, "exceeded max_seconds")
    if returncode != 0:
        message = (stderr.strip() or stdout.strip() or f"exit {returncode}").splitlines()[0]
        return SmokeResult(row.cnf_path, row.mode, "FAIL", elapsed, False, message)

    try:
        num_vars, clauses = satsolver.parse_dimacs_file(str(row.cnf_path))
        output_text = output_path.read_text(encoding="utf-8")
        status, _ = checker.parse_output_text(output_text)
        validation = checker.validate_output_text(
            num_vars,
            clauses,
            output_text,
            brute_force_var_limit=brute_force_var_limit,
        )
    except Exception as exc:
        return SmokeResult(row.cnf_path, row.mode, "FAIL", elapsed, False, str(exc))

    if row.expected in {"SAT", "UNSAT"} and status != row.expected:
        return SmokeResult(
            row.cnf_path,
            row.mode,
            "FAIL",
            elapsed,
            False,
            f"expected {row.expected}, got {status}",
        )

    if row.detector in {"true", "false"}:
        actual_detector = detector_result(row.cnf_path)
        expected_detector = row.detector == "true"
        if actual_detector != expected_detector:
            return SmokeResult(
                row.cnf_path,
                row.mode,
                "FAIL",
                elapsed,
                False,
                f"detector expected {expected_detector}, got {actual_detector}",
            )

    if row.detector == "portfolio_true" and not portfolio_result(row.cnf_path):
        return SmokeResult(row.cnf_path, row.mode, "FAIL", elapsed, False, "portfolio gate expected true")
    if row.detector == "portfolio_false" and portfolio_result(row.cnf_path):
        return SmokeResult(row.cnf_path, row.mode, "FAIL", elapsed, False, "portfolio gate expected false")

    return SmokeResult(row.cnf_path, row.mode, status, elapsed, True, validation)


def run_row(
    row: ManifestRow,
    solver: Path,
    scratch_dir: Path,
    brute_force_var_limit: int,
) -> SmokeResult:
    if row.mode == "detector":
        return check_detector(row)
    if row.mode == "invalid":
        return check_invalid(row, solver, scratch_dir)
    if row.mode == "solve":
        return check_solve(row, solver, scratch_dir, brute_force_var_limit)
    return SmokeResult(row.cnf_path, row.mode, "FAIL", 0.0, False, f"unknown mode {row.mode!r}")


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Run generated SAT solver regression smoke suites.")
    parser.add_argument("--solver", type=Path, default=ROOT / "satsolver.py")
    parser.add_argument("--suite", type=Path, required=True)
    parser.add_argument("--timeout", type=float, default=60.0)
    parser.add_argument("--bruteforce-var-limit", type=int, default=16)
    parser.add_argument("--limit", type=int, default=0, help="Optional max rows for quick local smoke.")
    args = parser.parse_args(sys.argv[1:] if argv is None else argv)

    solver = args.solver.resolve()
    manifests = discover_manifests(args.suite)
    if not manifests:
        print(f"No MANIFEST.tsv files found under {args.suite}", file=sys.stderr)
        return 2

    rows: list[ManifestRow] = []
    for manifest in manifests:
        rows.extend(read_manifest(manifest))
    if args.limit:
        rows = rows[: args.limit]
    for row in rows:
        row.max_seconds = min(row.max_seconds, args.timeout)

    results: list[SmokeResult] = []
    with tempfile.TemporaryDirectory(prefix="sat-regression-smoke-") as scratch_dir_str:
        scratch_dir = Path(scratch_dir_str)
        for row in rows:
            result = run_row(row, solver, scratch_dir, args.bruteforce_var_limit)
            results.append(result)
            relative = result.path.relative_to(ROOT) if result.path.is_relative_to(ROOT) else result.path
            print(
                f"{'PASS' if result.ok else 'FAIL'} {relative} mode={result.mode} "
                f"status={result.status} time={result.elapsed:.4f}s {result.details}"
            )

    failures = [result for result in results if not result.ok]
    print(
        f"SUMMARY rows={len(results)} passed={len(results) - len(failures)} "
        f"failed={len(failures)} max_time={max((result.elapsed for result in results), default=0.0):.4f}s"
    )
    if failures:
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
