from __future__ import annotations

import csv
from pathlib import Path
import unittest

import satsolver


ROOT = Path(__file__).resolve().parents[1]
GENERATED = ROOT / "tests" / "generated"


def manifest_rows(manifest_path: Path) -> list[dict[str, str]]:
    with manifest_path.open("r", encoding="utf-8", newline="") as handle:
        return list(csv.DictReader(handle, delimiter="\t"))


class GeneratedCoverageTests(unittest.TestCase):
    def test_mycielski_detector_expectations(self) -> None:
        rows = manifest_rows(GENERATED / "mycielski" / "MANIFEST.tsv")
        self.assertGreaterEqual(len(rows), 6)
        for row in rows:
            path = GENERATED / "mycielski" / row["path"]
            num_vars, clauses = satsolver.parse_dimacs_file(str(path))
            detector_result = satsolver.graph_coloring_mycielski_unsat(num_vars, clauses)
            if row["detector"] == "true":
                self.assertTrue(detector_result, row["path"])
            elif row["detector"] == "false":
                self.assertFalse(detector_result, row["path"])

    def test_mutated_mycielski_detector_rejects_broken_structures(self) -> None:
        rows = manifest_rows(GENERATED / "mutated_mycielski" / "MANIFEST.tsv")
        self.assertGreaterEqual(len(rows), 8)
        for row in rows:
            if row["detector"] != "false":
                continue
            path = GENERATED / "mutated_mycielski" / row["path"]
            num_vars, clauses = satsolver.parse_dimacs_file(str(path))
            self.assertFalse(
                satsolver.graph_coloring_mycielski_unsat(num_vars, clauses),
                row["path"],
            )

    def test_portfolio_density_gate_boundary(self) -> None:
        rows = manifest_rows(GENERATED / "portfolio_density" / "MANIFEST.tsv")
        self.assertEqual(len(rows), 90)
        for row in rows:
            path = GENERATED / "portfolio_density" / row["path"]
            num_vars, clauses = satsolver.parse_dimacs_file(str(path))
            actual = satsolver.should_use_parallel_portfolio(num_vars, clauses)
            if row["detector"] == "portfolio_true":
                self.assertTrue(actual, row["path"])
            elif row["detector"] == "portfolio_false":
                self.assertFalse(actual, row["path"])

    def test_parser_invalid_edge_cases_raise(self) -> None:
        rows = manifest_rows(GENERATED / "parser_edge_cases" / "MANIFEST.tsv")
        invalid_rows = [row for row in rows if row["mode"] == "invalid"]
        self.assertGreaterEqual(len(invalid_rows), 7)
        for row in invalid_rows:
            path = GENERATED / "parser_edge_cases" / row["path"]
            with self.assertRaises(Exception, msg=row["path"]):
                satsolver.parse_dimacs_file(str(path))


if __name__ == "__main__":
    unittest.main()
