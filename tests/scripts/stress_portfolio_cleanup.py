from __future__ import annotations

import argparse
import subprocess
import sys
import tempfile
from pathlib import Path
from time import perf_counter

ROOT = Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from tools import checker


DEFAULT_CASES = (
    "formulae/large/test_8.cnf",
    "course_cnf_tests/cnf_training_complex__complex_cnf_hard__planted3sat_balanced_n260_m1108_seed1.cnf",
    "formulae/large/test_6.cnf",
)


def run_case(solver: Path, cnf_path: Path, output_path: Path, timeout: float) -> float:
    start = perf_counter()
    completed = subprocess.run(
        [sys.executable, str(solver), str(cnf_path), str(output_path)],
        timeout=timeout,
        capture_output=True,
        text=True,
        check=False,
    )
    elapsed = perf_counter() - start
    if completed.returncode != 0:
        message = completed.stderr.strip() or completed.stdout.strip() or f"exit {completed.returncode}"
        raise RuntimeError(f"{cnf_path}: {message}")
    checker.validate_output_file(str(cnf_path), str(output_path), brute_force_var_limit=16)
    return elapsed


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Stress the CLI portfolio path for hangs/output corruption.")
    parser.add_argument("--solver", type=Path, default=ROOT / "satsolver.py")
    parser.add_argument("--repeat", type=int, default=5)
    parser.add_argument("--timeout", type=float, default=60.0)
    parser.add_argument("cases", nargs="*", default=list(DEFAULT_CASES))
    args = parser.parse_args(sys.argv[1:] if argv is None else argv)

    solver = args.solver.resolve()
    case_paths = [Path(case) if Path(case).is_absolute() else ROOT / case for case in args.cases]
    timings: list[float] = []

    with tempfile.TemporaryDirectory(prefix="sat-portfolio-stress-") as tmpdir_str:
        tmpdir = Path(tmpdir_str)
        for repeat_index in range(args.repeat):
            for case_index, cnf_path in enumerate(case_paths):
                output_path = tmpdir / f"case_{case_index}_repeat_{repeat_index}.out"
                try:
                    elapsed = run_case(solver, cnf_path, output_path, args.timeout)
                except subprocess.TimeoutExpired:
                    print(f"TIMEOUT {cnf_path}", file=sys.stderr)
                    return 1
                except Exception as exc:
                    print(f"FAIL {exc}", file=sys.stderr)
                    return 1
                timings.append(elapsed)
                print(f"PASS {cnf_path.relative_to(ROOT)} repeat={repeat_index} time={elapsed:.4f}s")

    print(
        f"SUMMARY runs={len(timings)} max_time={max(timings, default=0.0):.4f}s "
        f"avg_time={(sum(timings) / len(timings)) if timings else 0.0:.4f}s"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
