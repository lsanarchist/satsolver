from __future__ import annotations

import tempfile
import unittest
from pathlib import Path

from tools import codex_verify


class CodexVerifyTests(unittest.TestCase):
    def test_iter_python_sources_excludes_virtualenv_and_cache_paths(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            (root / "keep.py").write_text("pass\n", encoding="utf-8")
            (root / "pkg").mkdir()
            (root / "pkg" / "also_keep.py").write_text("pass\n", encoding="utf-8")
            (root / ".venv-test").mkdir()
            (root / ".venv-test" / "skip.py").write_text("pass\n", encoding="utf-8")
            (root / "__pycache__").mkdir()
            (root / "__pycache__" / "skip.py").write_text("pass\n", encoding="utf-8")
            (root / ".git").mkdir()
            (root / ".git" / "skip.py").write_text("pass\n", encoding="utf-8")

            paths = codex_verify.iter_python_sources(root)

        self.assertEqual([Path("keep.py"), Path("pkg/also_keep.py")], paths)

    def test_build_benchmark_command_module_mode_omits_cli_flags(self) -> None:
        command = codex_verify.build_benchmark_command(
            "python",
            "satsolver",
            "/tmp/out.txt",
            ["small", "special"],
            16,
            1,
        )

        self.assertEqual(
            [
                "python",
                str(codex_verify.ROOT / "benchmark_suite.py"),
                "satsolver",
                "/tmp/out.txt",
                "small",
                "special",
                "--bruteforce-var-limit",
                "16",
            ],
            command,
        )

    def test_build_benchmark_command_cli_mode_includes_cli_flags(self) -> None:
        command = codex_verify.build_benchmark_command(
            "python",
            "satsolver",
            "/tmp/out.txt",
            ["small"],
            16,
            2,
            cli_script="satsolver.py",
        )

        self.assertIn("--cli-script", command)
        self.assertIn("satsolver.py", command)
        self.assertIn("--python-executable", command)
        self.assertIn("--repeat", command)
        self.assertEqual("2", command[-1])

    def test_build_steps_runs_agent_queue_check_before_unit_tests(self) -> None:
        steps, benchmark_report = codex_verify.build_steps(
            python_executable="python",
            solver_script="satsolver.py",
            module_name="satsolver",
            benchmark_mode="none",
            benchmark_folders=["small"],
            benchmark_output=None,
            brute_force_var_limit=16,
            repeat=1,
        )

        self.assertIsNone(benchmark_report)
        descriptions = [step.description for step in steps]
        queue_step = descriptions.index("Validate agent queue control plane")
        tests_step = descriptions.index("Run unit tests")
        self.assertLess(queue_step, tests_step)
        self.assertEqual(
            ("python", "tools/agent_queue_check.py"),
            steps[queue_step].command,
        )

    def test_iter_alternate_solver_scripts_skips_primary_solver(self) -> None:
        self.assertEqual(
            ("satsolver_fast.py",),
            codex_verify.iter_alternate_solver_scripts("satsolver.py"),
        )
        self.assertEqual(
            (),
            codex_verify.iter_alternate_solver_scripts("./satsolver_fast.py"),
        )

    def test_build_steps_includes_alternate_wrapper_smokes(self) -> None:
        steps, _ = codex_verify.build_steps(
            python_executable="python",
            solver_script="satsolver.py",
            module_name="satsolver",
            benchmark_mode="none",
            benchmark_folders=["small"],
            benchmark_output=None,
            brute_force_var_limit=16,
            repeat=1,
        )

        descriptions = [step.description for step in steps]
        self.assertIn(
            "Run alternate wrapper (satsolver_fast.py) SAT smoke case",
            descriptions,
        )
        self.assertIn(
            "Validate alternate wrapper (satsolver_fast.py) UNSAT smoke output",
            descriptions,
        )
        alt_sat_step = next(
            step
            for step in steps
            if step.description == "Run alternate wrapper (satsolver_fast.py) SAT smoke case"
        )
        self.assertEqual("satsolver_fast.py", alt_sat_step.command[1])

    def test_build_steps_does_not_duplicate_primary_when_fast_wrapper_is_primary(self) -> None:
        steps, _ = codex_verify.build_steps(
            python_executable="python",
            solver_script="satsolver_fast.py",
            module_name="satsolver",
            benchmark_mode="none",
            benchmark_folders=["small"],
            benchmark_output=None,
            brute_force_var_limit=16,
            repeat=1,
        )

        descriptions = [step.description for step in steps]
        self.assertNotIn(
            "Run alternate wrapper (satsolver_fast.py) SAT smoke case",
            descriptions,
        )


if __name__ == "__main__":
    unittest.main()
