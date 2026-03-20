from __future__ import annotations

import argparse
import itertools
import sys
from pathlib import Path
from typing import Optional

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

import satsolver


class ValidationError(ValueError):
    pass


def build_model_from_line(model_line: str, num_vars: int) -> list[int]:
    tokens = model_line.split()
    if not tokens:
        raise ValidationError("SAT output is missing the assignment line")
    if tokens[-1] != "0":
        raise ValidationError("SAT assignment line must end with 0")

    assignment_tokens = tokens[:-1]
    if len(assignment_tokens) != num_vars:
        raise ValidationError(
            f"SAT assignment must contain exactly {num_vars} literals before 0, "
            f"got {len(assignment_tokens)}"
        )

    model = [0] * (num_vars + 1)
    seen: set[int] = set()
    for token in assignment_tokens:
        literal = int(token)
        variable = abs(literal)
        if variable < 1 or variable > num_vars:
            raise ValidationError(
                f"Assignment literal {literal} is outside the declared variable range 1..{num_vars}"
            )
        if variable in seen:
            raise ValidationError(f"Variable {variable} is assigned more than once")
        seen.add(variable)
        model[variable] = satsolver.TRUE if literal > 0 else satsolver.FALSE

    missing = [str(variable) for variable in range(1, num_vars + 1) if variable not in seen]
    if missing:
        raise ValidationError(f"Assignment is missing variables: {' '.join(missing)}")

    return model


def parse_output_text(output_text: str) -> tuple[str, Optional[str]]:
    lines = output_text.splitlines()
    if not lines:
        raise ValidationError("Output file is empty")
    if lines[0] == "UNSAT":
        if len(lines) != 1:
            raise ValidationError("UNSAT output must contain exactly one line")
        return "UNSAT", None
    if lines[0] != "SAT":
        raise ValidationError("First output line must be SAT or UNSAT")
    if len(lines) != 2:
        raise ValidationError("SAT output must contain exactly two lines")
    return "SAT", lines[1]


def brute_force_status(num_vars: int, clauses: list[list[int]], max_vars: int) -> Optional[str]:
    if num_vars > max_vars:
        return None

    for values in itertools.product((satsolver.FALSE, satsolver.TRUE), repeat=num_vars):
        model = [0, *values]
        if satsolver.model_satisfies(clauses, model):
            return "SAT"
    return "UNSAT"


def validate_output_text(
    num_vars: int,
    clauses: list[list[int]],
    output_text: str,
    *,
    brute_force_var_limit: int = 16,
) -> str:
    status, model_line = parse_output_text(output_text)

    if status == "SAT":
        assert model_line is not None
        model = build_model_from_line(model_line, num_vars)
        if not satsolver.model_satisfies(clauses, model):
            raise ValidationError("SAT assignment does not satisfy the CNF")
        return "valid SAT"

    brute_force_result = brute_force_status(num_vars, clauses, brute_force_var_limit)
    if brute_force_result == "SAT":
        raise ValidationError("Output says UNSAT, but brute force found a satisfying assignment")
    if brute_force_result == "UNSAT":
        return "valid UNSAT (brute-force checked)"
    return "valid UNSAT (format checked)"


def validate_output_file(
    cnf_path: str,
    output_path: str,
    *,
    brute_force_var_limit: int = 16,
) -> str:
    num_vars, clauses = satsolver.parse_dimacs_file(cnf_path)
    output_text = Path(output_path).read_text(encoding="utf-8")
    return validate_output_text(
        num_vars,
        clauses,
        output_text,
        brute_force_var_limit=brute_force_var_limit,
    )


def main(argv: Optional[list[str]] = None) -> int:
    parser = argparse.ArgumentParser(description="Validate SAT solver output against a DIMACS CNF.")
    parser.add_argument("cnf_path", help="Path to the DIMACS CNF input")
    parser.add_argument("output_path", help="Path to the solver output file")
    parser.add_argument(
        "--bruteforce-var-limit",
        type=int,
        default=16,
        help="Brute-force UNSAT validation only when num_vars is at most this limit",
    )
    args = parser.parse_args(sys.argv[1:] if argv is None else argv)

    try:
        result = validate_output_file(
            args.cnf_path,
            args.output_path,
            brute_force_var_limit=args.bruteforce_var_limit,
        )
    except (OSError, ValueError) as exc:
        print(f"INVALID: {exc}", file=sys.stderr)
        return 1

    print(f"VALID: {result}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
