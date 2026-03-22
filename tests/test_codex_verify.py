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


if __name__ == "__main__":
    unittest.main()
