from __future__ import annotations

import argparse
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from tools import checker


REQUIRED_MULTI_FILE_SUBMISSION = ("satsolver.py", "satsolver_core.py", "satsolver_io.py")


def write_unit_case(path: Path) -> None:
    path.write_text("p cnf 1 1\n1 0\n", encoding="utf-8")


def run_solver(tmpdir: Path) -> tuple[int, str, str]:
    input_path = tmpdir / "input.cnf"
    output_path = tmpdir / "output.txt"
    write_unit_case(input_path)
    completed = subprocess.run(
        [sys.executable, "satsolver.py", "input.cnf", "output.txt"],
        cwd=tmpdir,
        capture_output=True,
        text=True,
        check=False,
        timeout=20,
    )
    if completed.returncode == 0:
        checker.validate_output_file(str(input_path), str(output_path))
    return completed.returncode, completed.stdout, completed.stderr


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Check whether the submission path works as single-file or documented multi-file."
    )
    parser.add_argument("--solver", type=Path, default=ROOT / "satsolver.py")
    args = parser.parse_args(sys.argv[1:] if argv is None else argv)

    solver = args.solver.resolve()
    with tempfile.TemporaryDirectory(prefix="sat-single-file-check-") as tmpdir_str:
        tmpdir = Path(tmpdir_str)
        shutil.copy2(solver, tmpdir / "satsolver.py")
        single_returncode, _, single_stderr = run_solver(tmpdir)

    if single_returncode == 0:
        print("single_file_supported=true")
        return 0

    with tempfile.TemporaryDirectory(prefix="sat-multifile-check-") as tmpdir_str:
        tmpdir = Path(tmpdir_str)
        for filename in REQUIRED_MULTI_FILE_SUBMISSION:
            shutil.copy2(ROOT / filename, tmpdir / filename)
        multi_returncode, multi_stdout, multi_stderr = run_solver(tmpdir)

    if multi_returncode != 0:
        print("single_file_supported=false")
        print("multi_file_supported=false")
        print((multi_stderr or multi_stdout or "multi-file run failed").strip(), file=sys.stderr)
        return 1

    print("single_file_supported=false")
    print("multi_file_supported=true")
    print("required_files=" + ",".join(REQUIRED_MULTI_FILE_SUBMISSION))
    if "ModuleNotFoundError" in single_stderr:
        print("single_file_note=single-file-only copy fails because the solver is intentionally modular")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
