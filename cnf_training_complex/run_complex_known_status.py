from __future__ import annotations

import argparse
import csv
import subprocess
import sys
import tempfile
from pathlib import Path

def load_manifest(path: Path) -> dict[str, str]:
    statuses: dict[str, str] = {}
    with path.open(newline="", encoding="utf-8") as f:
        for row in csv.DictReader(f):
            statuses[row["filename"]] = row["known_status"]
    return statuses

def first_status(output_path: Path) -> str:
    text = output_path.read_text(encoding="utf-8").splitlines()
    if not text:
        return "EMPTY"
    return text[0].strip()

def main() -> int:
    ap = argparse.ArgumentParser(description="Run SAT solver over complex CNF folders with timeout and known-status checks.")
    ap.add_argument("folders", nargs="+", help="Folders containing .cnf files")
    ap.add_argument("--timeout", type=float, default=60.0, help="Per-case timeout in seconds")
    ap.add_argument("--solver", default="satsolver.py", help="Solver CLI script")
    ap.add_argument("--python", default=sys.executable, help="Python executable")
    ap.add_argument("--manifest", default="COMPLEX_CNF_manifest.csv", help="Manifest CSV; falls back to manifest.csv")
    ap.add_argument("--bruteforce-var-limit", type=int, default=16)
    args = ap.parse_args()

    manifest = Path(args.manifest)
    if not manifest.exists():
        manifest = Path("manifest.csv")
    if not manifest.exists():
        raise SystemExit("Could not find manifest CSV")

    statuses = load_manifest(manifest)
    checker = Path("tools/checker.py")
    solver = Path(args.solver)

    total = ok = timeout_count = mismatch = errors = 0
    with tempfile.TemporaryDirectory(prefix="sat-complex-") as tmp:
        tmpdir = Path(tmp)
        for folder_arg in args.folders:
            folder = Path(folder_arg)
            for cnf in sorted(folder.glob("*.cnf")):
                total += 1
                expected = statuses.get(cnf.name, "UNKNOWN")
                out = tmpdir / (cnf.stem + ".out")
                print(f"{cnf} ... ", end="", flush=True)
                try:
                    cp = subprocess.run(
                        [args.python, str(solver), str(cnf), str(out)],
                        text=True,
                        capture_output=True,
                        timeout=args.timeout,
                    )
                except subprocess.TimeoutExpired:
                    timeout_count += 1
                    print(f"TIMEOUT after {args.timeout:g}s")
                    continue
                if cp.returncode != 0:
                    errors += 1
                    msg = (cp.stderr or cp.stdout or "").strip().splitlines()
                    print(f"SOLVER_ERROR {msg[0] if msg else cp.returncode}")
                    continue
                actual = first_status(out)
                if expected != "UNKNOWN" and actual != expected:
                    mismatch += 1
                    print(f"STATUS_MISMATCH expected={expected} actual={actual}")
                    continue
                if checker.exists():
                    chk = subprocess.run(
                        [args.python, str(checker), str(cnf), str(out), "--bruteforce-var-limit", str(args.bruteforce_var_limit)],
                        text=True,
                        capture_output=True,
                    )
                    if chk.returncode != 0:
                        errors += 1
                        print(f"CHECKER_ERROR {(chk.stderr or chk.stdout).strip()}")
                        continue
                ok += 1
                print(f"OK {actual}")

    print(f"SUMMARY total={total} ok={ok} timeouts={timeout_count} mismatches={mismatch} errors={errors}")
    return 0 if mismatch == 0 and errors == 0 else 1

if __name__ == "__main__":
    raise SystemExit(main())
