from __future__ import annotations

import argparse
import csv
import itertools
import re
import shutil
import subprocess
import sys
from dataclasses import dataclass
from pathlib import Path


PACK_ROOT = Path(__file__).resolve().parent
REPO_ROOT = PACK_ROOT.parent
CASES_DIR = PACK_ROOT / "cnfgen_cases"
MANIFEST_TSV = PACK_ROOT / "MANIFEST.tsv"
MANIFEST_CSV = PACK_ROOT / "manifest.csv"
MAX_VARS = 500
MAX_CLAUSES = 2000
TIMEOUT_SECONDS = 60.0


@dataclass(frozen=True)
class CaseSpec:
    filename: str
    family: str
    level: str
    expected: str
    args: tuple[str, ...]
    seed: int
    max_seconds: float
    notes: str


def add_case(
    cases: list[CaseSpec],
    filename: str,
    family: str,
    level: str,
    expected: str,
    args: list[str],
    *,
    seed: int,
    max_seconds: float = TIMEOUT_SECONDS,
    notes: str = "",
) -> None:
    if expected not in {"SAT", "UNSAT", "BRUTE"}:
        raise ValueError(f"unsupported expected status {expected!r}")
    max_seconds = min(max_seconds, TIMEOUT_SECONDS)
    cases.append(
        CaseSpec(
            filename=filename,
            family=family,
            level=level,
            expected=expected,
            args=tuple(args),
            seed=seed,
            max_seconds=max_seconds,
            notes=notes,
        )
    )


def build_cases() -> list[CaseSpec]:
    cases: list[CaseSpec] = []
    seed = 31001

    def next_seed() -> int:
        nonlocal seed
        seed += 1
        return seed

    add_case(cases, "sanity_true_sat.cnf", "sanity", "easy", "SAT", ["true"], seed=next_seed(), notes="empty true formula")
    add_case(cases, "sanity_false_unsat.cnf", "sanity", "easy", "UNSAT", ["false"], seed=next_seed(), notes="single empty clause")

    for n in (8, 9, 12, 13, 16):
        expected = "SAT" if n % 2 == 0 else "UNSAT"
        add_case(
            cases,
            f"parity_n{n}_{expected.lower()}.cnf",
            "parity",
            "easy" if n < 20 else "moderate",
            expected,
            ["parity", str(n)],
            seed=next_seed(),
            notes="parity principle",
        )

    for domain, part in ((8, 2), (9, 2), (10, 2), (11, 2), (6, 3), (7, 3)):
        expected = "SAT" if domain % part == 0 else "UNSAT"
        add_case(
            cases,
            f"count_m{domain}_p{part}_{expected.lower()}.cnf",
            "counting",
            "easy" if domain <= 20 else "moderate",
            expected,
            ["count", str(domain), str(part)],
            seed=next_seed(),
            notes="counting partition principle",
        )

    for k, rows in (
        (2, [(50, 60), (50, 120), (80, 160), (120, 260), (180, 360), (240, 520)]),
        (3, [(30, 90), (60, 240), (90, 380), (120, 510), (200, 860), (320, 1360), (500, 2000)]),
        (4, [(40, 180), (80, 520), (120, 900), (180, 1440)]),
    ):
        for variant in range(1, 4):
            for nvars, clauses in rows:
                level = "easy" if nvars <= 60 else "moderate" if nvars <= 180 else "stress"
                add_case(
                    cases,
                    f"planted_rand{k}cnf_v{nvars}_m{clauses}_s{variant}_sat.cnf",
                    "planted_randkcnf",
                    level,
                    "SAT",
                    ["randkcnf", "-p", str(k), str(nvars), str(clauses)],
                    seed=next_seed(),
                    notes="CNFgen planted random k-CNF",
                )

    for nvars in range(8, 17):
        for multiplier in (3, 4, 5):
            for variant in range(1, 3):
                clauses = nvars * multiplier
                add_case(
                    cases,
                    f"exact_random3cnf_v{nvars}_m{clauses}_s{variant}.cnf",
                    "exact_small_randkcnf",
                    "easy",
                    "BRUTE",
                    ["randkcnf", "3", str(nvars), str(clauses)],
                    seed=next_seed(),
                    notes="status brute-forced during generation",
                )

    for k, rows in (
        (3, [(24, 24), (32, 40), (48, 64), (64, 90), (96, 128), (128, 180)]),
        (4, [(24, 18), (48, 36), (64, 56), (96, 90), (128, 120)]),
    ):
        for variant in range(1, 3):
            for nvars, equations in rows:
                level = "easy" if nvars <= 48 else "moderate" if nvars <= 96 else "stress"
                add_case(
                    cases,
                    f"planted_rand{k}xor_v{nvars}_e{equations}_s{variant}_sat.cnf",
                    "planted_randkxor",
                    level,
                    "SAT",
                    ["randkxor", "-p", str(k), str(nvars), str(equations)],
                    seed=next_seed(),
                    notes="CNFgen planted random XOR encoded as CNF",
                )

    for pigeons, holes in ((5, 5), (6, 5), (8, 8), (9, 8), (12, 11), (15, 14), (16, 16), (16, 15)):
        expected = "SAT" if pigeons <= holes else "UNSAT"
        add_case(
            cases,
            f"php_p{pigeons}_h{holes}_{expected.lower()}.cnf",
            "pigeonhole",
            "moderate" if pigeons >= 12 else "easy",
            expected,
            ["php", str(pigeons), str(holes)],
            seed=next_seed(),
            notes="plain pigeonhole principle",
        )

    for pigeons, holes in ((5, 5), (6, 5), (7, 6), (8, 8), (8, 7), (9, 8)):
        expected = "SAT" if pigeons <= holes else "UNSAT"
        add_case(
            cases,
            f"bphp_p{pigeons}_h{holes}_{expected.lower()}.cnf",
            "binary_pigeonhole",
            "moderate",
            expected,
            ["bphp", str(pigeons), str(holes)],
            seed=next_seed(),
            notes="binary pigeonhole principle",
        )

    for pigeons, resting, holes in ((8, 12, 10), (10, 8, 12), (8, 14, 12), (10, 12, 12), (12, 10, 12)):
        expected = "SAT" if pigeons <= resting and pigeons <= holes else "UNSAT"
        add_case(
            cases,
            f"rphp_p{pigeons}_r{resting}_h{holes}_{expected.lower()}.cnf",
            "relativized_pigeonhole",
            "moderate",
            expected,
            ["rphp", str(pigeons), str(resting), str(holes)],
            seed=next_seed(),
            notes="relativized pigeonhole principle",
        )

    for nverts, degree in ((20, 3), (40, 3), (60, 3), (64, 4), (80, 4), (100, 4)):
        level = "easy" if nverts <= 40 else "moderate" if nverts <= 80 else "stress"
        for charge, expected in (("zero", "SAT"), ("first", "UNSAT")):
            add_case(
                cases,
                f"tseitin_{charge}_v{nverts}_d{degree}_{expected.lower()}.cnf",
                "tseitin",
                level,
                expected,
                ["tseitin", charge, "gnd", str(nverts), str(degree)],
                seed=next_seed(),
                notes="Tseitin formula on random regular graph",
            )

    for n in (6, 8, 10, 12, 13):
        add_case(
            cases,
            f"ordering_no_minimum_n{n}_unsat.cnf",
            "ordering",
            "easy" if n <= 8 else "moderate",
            "UNSAT",
            ["op", str(n)],
            seed=next_seed(),
            notes="ordering principle",
        )

    for args, expected, label, level in (
        (["ram", "3", "3", "5"], "SAT", "ram_3_3_n5_sat", "easy"),
        (["ram", "3", "3", "6"], "UNSAT", "ram_3_3_n6_unsat", "easy"),
        (["ram", "3", "3", "7"], "UNSAT", "ram_3_3_n7_unsat", "moderate"),
        (["ram", "3", "4", "8"], "SAT", "ram_3_4_n8_sat", "moderate"),
        (["ram", "3", "4", "9"], "UNSAT", "ram_3_4_n9_unsat", "moderate"),
        (["ram", "3", "4", "10"], "UNSAT", "ram_3_4_n10_unsat", "stress"),
    ):
        add_case(cases, f"{label}.cnf", "ramsey", level, expected, args, seed=next_seed(), notes="Ramsey principle")

    for args, expected, label, level in (
        (["vdw", "8", "3", "3"], "SAT", "vdw_2color_k3_n8_sat", "easy"),
        (["vdw", "9", "3", "3"], "UNSAT", "vdw_2color_k3_n9_unsat", "easy"),
        (["vdw", "16", "3", "3"], "UNSAT", "vdw_2color_k3_n16_unsat", "moderate"),
        (["vdw", "34", "4", "4"], "SAT", "vdw_2color_k4_n34_sat", "moderate"),
        (["vdw", "35", "4", "4"], "UNSAT", "vdw_2color_k4_n35_unsat", "stress"),
    ):
        add_case(cases, f"{label}.cnf", "van_der_waerden", level, expected, args, seed=next_seed(), notes="Van der Waerden principle")

    for colors, graph_args, expected, label in (
        (3, ["complete", "3"], "SAT", "kcolor_k3_complete3_sat"),
        (3, ["complete", "4"], "UNSAT", "kcolor_k3_complete4_unsat"),
        (4, ["complete", "4"], "SAT", "kcolor_k4_complete4_sat"),
        (4, ["complete", "5"], "UNSAT", "kcolor_k4_complete5_unsat"),
        (2, ["empty", "24"], "SAT", "kcolor_k2_empty24_sat"),
        (2, ["grid", "3", "3"], "SAT", "kcolor_k2_grid3x3_sat"),
    ):
        add_case(
            cases,
            f"{label}.cnf",
            "graph_coloring",
            "easy",
            expected,
            ["kcolor", str(colors), *graph_args],
            seed=next_seed(),
            notes="known graph-coloring instance",
        )

    for size, graph_args, expected, label in (
        (4, ["complete", "4"], "SAT", "kclique_k4_complete4_sat"),
        (4, ["empty", "8"], "UNSAT", "kclique_k4_empty8_unsat"),
        (5, ["complete", "8"], "SAT", "kclique_k5_complete8_sat"),
        (6, ["complete", "5"], "UNSAT", "kclique_k6_complete5_unsat"),
    ):
        add_case(
            cases,
            f"{label}.cnf",
            "clique",
            "easy",
            expected,
            ["kclique", str(size), *graph_args],
            seed=next_seed(),
            notes="known clique instance",
        )

    for graph_args, expected, label in (
        (["complete", "8"], "SAT", "matching_complete8_sat"),
        (["complete", "9"], "UNSAT", "matching_complete9_unsat"),
        (["empty", "6"], "UNSAT", "matching_empty6_unsat"),
        (["grid", "4", "4"], "SAT", "matching_grid4x4_sat"),
    ):
        add_case(
            cases,
            f"{label}.cnf",
            "matching",
            "easy",
            expected,
            ["matching", *graph_args],
            seed=next_seed(),
            notes="perfect matching principle",
        )

    for args, expected, label in (
        (["subgraph", "-G", "complete", "5", "-H", "complete", "4"], "SAT", "subgraph_k4_in_k5_sat"),
        (["subgraph", "-G", "grid", "3", "3", "-H", "complete", "3"], "UNSAT", "subgraph_triangle_in_grid3x3_unsat"),
        (["subgraph", "-G", "complete", "8", "-H", "grid", "2", "2"], "SAT", "subgraph_grid2x2_in_k8_sat"),
    ):
        add_case(cases, f"{label}.cnf", "subgraph", "easy", expected, args, seed=next_seed(), notes="subgraph containment")

    for nverts, clique_size, colors, expected in ((10, 4, 3, "UNSAT"), (10, 4, 4, "SAT"), (8, 3, 4, "SAT"), (6, 5, 4, "UNSAT")):
        add_case(
            cases,
            f"cliquecoloring_n{nverts}_k{clique_size}_c{colors}_{expected.lower()}.cnf",
            "clique_coloring",
            "moderate",
            expected,
            ["cliquecoloring", str(nverts), str(clique_size), str(colors)],
            seed=next_seed(),
            notes="clique-coloring principle",
        )

    for n in (10, 16):
        add_case(
            cases,
            f"subsetcard_n{n}_unsat.cnf",
            "subset_cardinality",
            "moderate" if n <= 20 else "stress",
            "UNSAT",
            ["subsetcard", str(n)],
            seed=next_seed(),
            notes="subset cardinality principle",
        )

    for dag_args, label in (
        (["path", "12"], "peb_path12_unsat"),
        (["pyramid", "4"], "peb_pyramid4_unsat"),
        (["tree", "4"], "peb_tree4_unsat"),
    ):
        add_case(cases, f"{label}.cnf", "pebbling", "easy", "UNSAT", ["peb", *dag_args], seed=next_seed(), notes="pebbling formula")

    for stones, dag_args, label in (
        (4, ["path", "8"], "stone4_path8_unsat"),
        (4, ["pyramid", "3"], "stone4_pyramid3_unsat"),
        (5, ["tree", "3"], "stone5_tree3_unsat"),
    ):
        add_case(
            cases,
            f"{label}.cnf",
            "stone",
            "moderate",
            "UNSAT",
            ["stone", str(stones), *dag_args, "--sparse", "3"],
            seed=next_seed(),
            notes="sparse stone formula",
        )

    transform_cases = [
        ("shuffle_php_p7_h6_unsat", "UNSAT", ["php", "7", "6", "-T", "shuffle"], "pigeonhole"),
        ("flip_php_p6_h6_sat", "SAT", ["php", "6", "6", "-T", "flip"], "pigeonhole"),
        ("shuffle_ram_3_3_n6_unsat", "UNSAT", ["ram", "3", "3", "6", "-T", "shuffle"], "ramsey"),
        ("shuffle_vdw_k3_n9_unsat", "UNSAT", ["vdw", "9", "3", "3", "-T", "shuffle"], "van_der_waerden"),
        ("xor2_parity_n5_unsat", "UNSAT", ["parity", "5", "-T", "xor", "2"], "parity"),
        ("shuffle_count_m7_p3_unsat", "UNSAT", ["count", "7", "3", "-T", "shuffle"], "counting"),
        ("shuffle_kcolor_k3_complete4_unsat", "UNSAT", ["kcolor", "3", "complete", "4", "-T", "shuffle"], "graph_coloring"),
        ("xor2_rand3cnf_v12_m42_planted_sat", "SAT", ["randkcnf", "-p", "3", "12", "42", "-T", "xor", "2"], "planted_randkcnf"),
        ("or2_rand3cnf_v12_m42_planted_sat", "SAT", ["randkcnf", "-p", "3", "12", "42", "-T", "or", "2"], "planted_randkcnf"),
        ("eq2_rand3cnf_v12_m42_planted_sat", "SAT", ["randkcnf", "-p", "3", "12", "42", "-T", "eq", "2"], "planted_randkcnf"),
        ("shuffle_tseitin_first_v20_d3_unsat", "UNSAT", ["tseitin", "first", "gnd", "20", "3", "-T", "shuffle"], "tseitin"),
        ("flip_cliquecoloring_n5_k5_c4_unsat", "UNSAT", ["cliquecoloring", "5", "5", "4", "-T", "flip"], "clique_coloring"),
    ]
    for label, expected, args, family in transform_cases:
        add_case(
            cases,
            f"{label}.cnf",
            f"{family}_transform",
            "moderate",
            expected,
            args,
            seed=next_seed(),
            notes="satisfiability-preserving CNFgen transformation",
        )

    filenames = [case.filename for case in cases]
    if len(filenames) != len(set(filenames)):
        duplicates = sorted({name for name in filenames if filenames.count(name) > 1})
        raise AssertionError(f"duplicate filenames: {duplicates}")
    return cases


def parse_dimacs(path: Path) -> tuple[int, list[list[int]]]:
    num_vars = -1
    clauses: list[list[int]] = []
    current: list[int] = []
    for line in path.read_text(encoding="utf-8").splitlines():
        stripped = line.strip()
        if not stripped or stripped.startswith("c"):
            continue
        if stripped.startswith("p "):
            parts = stripped.split()
            if len(parts) != 4 or parts[1] != "cnf":
                raise ValueError(f"bad DIMACS header in {path}")
            num_vars = int(parts[2])
            continue
        for token in stripped.split():
            literal = int(token)
            if literal == 0:
                clauses.append(current)
                current = []
            else:
                current.append(literal)
    if current:
        raise ValueError(f"unterminated clause in {path}")
    if num_vars < 0:
        raise ValueError(f"missing DIMACS header in {path}")
    return num_vars, clauses


def clause_satisfied(clause: list[int], values: tuple[bool, ...]) -> bool:
    for literal in clause:
        value = values[abs(literal) - 1]
        if (literal > 0 and value) or (literal < 0 and not value):
            return True
    return False


def brute_force_status(num_vars: int, clauses: list[list[int]]) -> str:
    if num_vars > 16:
        raise ValueError(f"refusing to brute-force {num_vars} variables")
    for values in itertools.product((False, True), repeat=num_vars):
        if all(clause_satisfied(clause, values) for clause in clauses):
            return "SAT"
    return "UNSAT"


def header_counts(path: Path) -> tuple[int, int]:
    text = path.read_text(encoding="utf-8")
    match = re.search(r"^p cnf\s+(\d+)\s+(\d+)$", text, re.MULTILINE)
    if not match:
        raise ValueError(f"missing p cnf header in {path}")
    return int(match.group(1)), int(match.group(2))


def add_metadata(path: Path, case: CaseSpec, expected: str) -> None:
    lines = path.read_text(encoding="utf-8").splitlines()
    metadata = [
        f"c known_status: {expected}",
        f"c pack_family: {case.family}",
        f"c pack_level: {case.level}",
        f"c pack_notes: {case.notes}",
    ]
    for index, line in enumerate(lines):
        if line.startswith("p cnf"):
            lines[index:index] = metadata
            path.write_text("\n".join(lines) + "\n", encoding="utf-8")
            return
    raise ValueError(f"missing header in {path}")


def locate_cnfgen(explicit: str | None) -> str:
    if explicit:
        return explicit
    discovered = shutil.which("cnfgen")
    if discovered:
        return discovered
    raise SystemExit("Could not find cnfgen. Install CNFgen or pass --cnfgen /path/to/cnfgen.")


def generate_case(cnfgen: str, case: CaseSpec) -> tuple[str, int, int, str]:
    output_path = CASES_DIR / case.filename
    relative_output = output_path.relative_to(REPO_ROOT)
    command = [
        cnfgen,
        "-S",
        str(case.seed),
        "-o",
        str(relative_output),
        *case.args,
    ]
    completed = subprocess.run(
        command,
        cwd=REPO_ROOT,
        text=True,
        capture_output=True,
        check=False,
    )
    if completed.returncode != 0:
        message = completed.stderr.strip() or completed.stdout.strip() or f"exit {completed.returncode}"
        raise RuntimeError(f"CNFgen failed for {case.filename}: {message}")

    expected = case.expected
    if expected == "BRUTE":
        num_vars, clauses = parse_dimacs(output_path)
        expected = brute_force_status(num_vars, clauses)
    add_metadata(output_path, case, expected)
    vars_count, clauses_count = header_counts(output_path)
    if expected not in {"SAT", "UNSAT"}:
        output_path.unlink(missing_ok=True)
        raise ValueError(f"{case.filename} has non-final expected status {expected!r}")
    if vars_count > MAX_VARS or clauses_count > MAX_CLAUSES:
        output_path.unlink(missing_ok=True)
        raise ValueError(
            f"{case.filename} exceeds pack limits: vars={vars_count}/{MAX_VARS}, "
            f"clauses={clauses_count}/{MAX_CLAUSES}"
        )
    source_command = "cnfgen -S " + str(case.seed) + " " + " ".join(case.args)
    return expected, vars_count, clauses_count, source_command


def write_manifests(rows: list[dict[str, str]]) -> None:
    with MANIFEST_TSV.open("w", encoding="utf-8", newline="") as handle:
        writer = csv.DictWriter(
            handle,
            delimiter="\t",
            fieldnames=["path", "expected", "detector", "max_seconds", "mode", "notes"],
        )
        writer.writeheader()
        for row in rows:
            writer.writerow(
                {
                    "path": row["path"],
                    "expected": row["known_status"],
                    "detector": "any",
                    "max_seconds": row["max_seconds"],
                    "mode": "solve",
                    "notes": f"{row['family']} {row['level']} {row['notes']}".strip(),
                }
            )

    with MANIFEST_CSV.open("w", encoding="utf-8", newline="") as handle:
        writer = csv.DictWriter(
            handle,
            extrasaction="ignore",
            fieldnames=[
                "folder",
                "filename",
                "family",
                "known_status",
                "level",
                "vars",
                "clauses",
                "max_seconds",
                "source_command",
                "notes",
            ],
        )
        writer.writeheader()
        writer.writerows(rows)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Generate a deterministic CNFgen regression pack.")
    parser.add_argument("--cnfgen", help="Path to the CNFgen executable; defaults to PATH lookup.")
    args = parser.parse_args(sys.argv[1:] if argv is None else argv)

    cnfgen = locate_cnfgen(args.cnfgen)
    cases = build_cases()

    CASES_DIR.mkdir(parents=True, exist_ok=True)
    for old_case in CASES_DIR.glob("*.cnf"):
        old_case.unlink()

    rows: list[dict[str, str]] = []
    for case in cases:
        expected, vars_count, clauses_count, source_command = generate_case(cnfgen, case)
        rows.append(
            {
                "folder": str(CASES_DIR.relative_to(PACK_ROOT)),
                "path": str((CASES_DIR / case.filename).relative_to(REPO_ROOT)),
                "filename": case.filename,
                "family": case.family,
                "known_status": expected,
                "level": case.level,
                "vars": str(vars_count),
                "clauses": str(clauses_count),
                "max_seconds": f"{case.max_seconds:g}",
                "source_command": source_command,
                "notes": case.notes,
            }
        )

    rows.sort(key=lambda row: row["filename"])
    write_manifests(rows)

    sat_count = sum(1 for row in rows if row["known_status"] == "SAT")
    unsat_count = sum(1 for row in rows if row["known_status"] == "UNSAT")
    print(
        f"Generated {len(rows)} CNFgen cases in {CASES_DIR.relative_to(REPO_ROOT)} "
        f"({sat_count} SAT, {unsat_count} UNSAT)."
    )
    print(f"Wrote {MANIFEST_TSV.relative_to(REPO_ROOT)} and {MANIFEST_CSV.relative_to(REPO_ROOT)}.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
