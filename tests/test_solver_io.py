from __future__ import annotations

import tempfile
import unittest
from pathlib import Path

import satsolver
import satsolver_fast
import satsolver_io


class SharedIoTests(unittest.TestCase):
    def test_base_and_fast_wrappers_share_parse_helpers(self) -> None:
        self.assertIs(satsolver.parse_dimacs_bytes, satsolver_io.parse_dimacs_bytes)
        self.assertIs(satsolver.parse_dimacs, satsolver_io.parse_dimacs)
        self.assertIs(satsolver.parse_dimacs_file, satsolver_io.parse_dimacs_file)
        self.assertIs(satsolver_fast.parse_dimacs_bytes, satsolver_io.parse_dimacs_bytes)
        self.assertIs(satsolver_fast.parse_dimacs, satsolver_io.parse_dimacs)
        self.assertIs(satsolver_fast.parse_dimacs_file, satsolver_io.parse_dimacs_file)

    def test_parse_dimacs_file_reads_bytes_via_shared_helper(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            path = Path(temp_dir) / "tiny.cnf"
            path.write_bytes(b"c note\np cnf 2 2\n1 -2 0\n0\n")

            parsed = satsolver_io.parse_dimacs_file(str(path))

        self.assertEqual((2, [[1, -2], []]), parsed)

    def test_write_result_writes_unsat_and_sat_outputs(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            unsat_path = Path(temp_dir) / "unsat.txt"
            sat_path = Path(temp_dir) / "sat.txt"

            satsolver_io.write_result(
                str(unsat_path),
                None,
                format_model=lambda model: "unused",
            )
            satsolver_io.write_result(
                str(sat_path),
                [0, 1, -1],
                format_model=lambda model: "1 -2 0",
            )

            unsat_output = unsat_path.read_text(encoding="utf-8")
            sat_output = sat_path.read_text(encoding="utf-8")

        self.assertEqual("UNSAT\n", unsat_output)
        self.assertEqual("SAT\n1 -2 0\n", sat_output)


if __name__ == "__main__":
    unittest.main()
