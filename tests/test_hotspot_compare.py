from __future__ import annotations

import unittest
from pathlib import Path

from tools import hotspot_compare


ROOT = Path(__file__).resolve().parents[1]


class HotspotCompareTests(unittest.TestCase):
    def test_load_runner_requires_exactly_one_mode(self) -> None:
        with self.assertRaisesRegex(ValueError, "exactly one"):
            hotspot_compare.load_runner("baseline", None, None, "python")

        with self.assertRaisesRegex(ValueError, "exactly one"):
            hotspot_compare.load_runner("baseline", "satsolver", "satsolver.py", "python")

    def test_compare_runners_module_vs_cli_smoke(self) -> None:
        baseline = hotspot_compare.load_runner("baseline", "satsolver", None, "python")
        candidate = hotspot_compare.load_runner(
            "candidate",
            None,
            str(ROOT / "satsolver.py"),
            "python",
        )
        comparisons = hotspot_compare.compare_runners(
            baseline,
            candidate,
            [
                str(ROOT / "small" / "test_1.cnf"),
                str(ROOT / "special" / "tseitin.cnf"),
            ],
            brute_force_var_limit=0,
            repeat=1,
        )

        self.assertEqual(["forward", "reverse"], [comparison.order_name for comparison in comparisons])
        for comparison in comparisons:
            self.assertEqual(2, len(comparison.case_rows))
            self.assertGreaterEqual(comparison.baseline_total_s, 0.0)
            self.assertGreaterEqual(comparison.candidate_total_s, 0.0)
            for baseline_case, candidate_case in comparison.case_rows:
                self.assertEqual(baseline_case.status, candidate_case.status)
                self.assertIn(baseline_case.validation, {"valid SAT", "valid UNSAT (format checked)"})
                self.assertEqual(baseline_case.validation, candidate_case.validation)

        rendered = hotspot_compare.render_comparisons(baseline, candidate, comparisons, repeat=1)
        self.assertIn("[forward]", rendered)
        self.assertIn("[reverse]", rendered)
        self.assertIn("[two-order-average]", rendered)
        self.assertIn("small/test_1.cnf", rendered)
        self.assertIn("special/tseitin.cnf", rendered)

    def test_repeat_must_be_positive(self) -> None:
        baseline = hotspot_compare.load_runner("baseline", "satsolver", None, "python")
        candidate = hotspot_compare.load_runner("candidate", "satsolver", None, "python")
        with self.assertRaisesRegex(ValueError, "repeat must be at least 1"):
            hotspot_compare.compare_runners(
                baseline,
                candidate,
                [str(ROOT / "small" / "test_1.cnf")],
                repeat=0,
            )


if __name__ == "__main__":
    unittest.main()
