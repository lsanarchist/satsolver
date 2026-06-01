from __future__ import annotations

import argparse
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from tools import checker


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Validate one SAT solver output file.")
    parser.add_argument("cnf_path")
    parser.add_argument("output_path")
    parser.add_argument("--bruteforce-var-limit", type=int, default=16)
    args = parser.parse_args(sys.argv[1:] if argv is None else argv)

    try:
        result = checker.validate_output_file(
            args.cnf_path,
            args.output_path,
            brute_force_var_limit=args.bruteforce_var_limit,
        )
    except Exception as exc:
        print(f"INVALID: {exc}", file=sys.stderr)
        return 1

    print(f"VALID: {result}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
