from __future__ import annotations

import sys
import tempfile
import unittest
from pathlib import Path

import benchmark_suite


class BenchmarkSuiteCliModeTests(unittest.TestCase):
    def test_cli_mode_validates_sat_and_unsat_outputs(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            cases_dir = root / "cases"
            cases_dir.mkdir()

            (cases_dir / "tiny_sat.cnf").write_text("p cnf 2 1\n1 -2 0\n", encoding="utf-8")
            (cases_dir / "tiny_unsat.cnf").write_text("p cnf 1 2\n1 0\n-1 0\n", encoding="utf-8")

            report_path = root / "report.txt"
            solver_script = Path(__file__).resolve().parents[1] / "satsolver.py"

            result = benchmark_suite.benchmark_solver(
                "satsolver",
                str(report_path),
                [str(cases_dir)],
                brute_force_var_limit=4,
                cli_script=str(solver_script),
                python_executable=sys.executable,
            )

            self.assertEqual(result, 0)
            report = report_path.read_text(encoding="utf-8")
            self.assertIn("mode=cli", report)
            self.assertIn("solved_correctly=2", report)
            self.assertIn("errors=0", report)
            self.assertIn("validation='valid SAT'", report)
            self.assertIn("validation='valid UNSAT (brute-force checked)'", report)

    def test_repeat_mode_reports_repeat_statistics(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            cases_dir = root / "cases"
            cases_dir.mkdir()

            (cases_dir / "tiny_sat.cnf").write_text("p cnf 2 1\n1 -2 0\n", encoding="utf-8")
            (cases_dir / "tiny_unsat.cnf").write_text("p cnf 1 2\n1 0\n-1 0\n", encoding="utf-8")

            report_path = root / "report.txt"
            result = benchmark_suite.benchmark_solver(
                "satsolver",
                str(report_path),
                [str(cases_dir)],
                brute_force_var_limit=4,
                repeat=2,
            )

            self.assertEqual(result, 0)
            report = report_path.read_text(encoding="utf-8")
            self.assertIn("repeat=2", report)
            self.assertIn("representative_time=median_of_repeats", report)
            self.assertIn("repeat_count=2", report)
            self.assertIn("samples=[", report)
            self.assertIn("measured_total=", report)
            self.assertIn("solved_correctly=2", report)

    def test_repeat_must_be_positive(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            cases_dir = root / "cases"
            cases_dir.mkdir()
            (cases_dir / "tiny_sat.cnf").write_text("p cnf 1 1\n1 0\n", encoding="utf-8")

            with self.assertRaisesRegex(ValueError, "repeat must be at least 1"):
                benchmark_suite.benchmark_solver(
                    "satsolver",
                    str(root / "report.txt"),
                    [str(cases_dir)],
                    brute_force_var_limit=4,
                    repeat=0,
                )


if __name__ == "__main__":
    unittest.main()
