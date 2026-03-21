import unittest

import satsolver_pysat


class ExternalSolverWrapperTests(unittest.TestCase):
    def test_build_model_fills_defaults(self) -> None:
        model = satsolver_pysat._build_model(4, [3, -1])

        self.assertEqual(
            model,
            [
                satsolver_pysat.base.FALSE,
                satsolver_pysat.base.FALSE,
                satsolver_pysat.base.FALSE,
                satsolver_pysat.base.TRUE,
                satsolver_pysat.base.FALSE,
            ],
        )

    def test_missing_pysat_raises_runtime_error(self) -> None:
        if satsolver_pysat.IMPORT_ERROR is None:
            self.skipTest("PySAT is available in this interpreter")

        with self.assertRaisesRegex(RuntimeError, r"PySAT is not available"):
            satsolver_pysat.solve_cnf(1, [[1]])


if __name__ == "__main__":
    unittest.main()
