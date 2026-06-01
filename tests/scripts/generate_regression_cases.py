from __future__ import annotations

import argparse
import random
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))
GENERATED = ROOT / "tests" / "generated"


def write_dimacs(path: Path, num_vars: int, clauses: list[list[int]], comment: str = "") -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", encoding="utf-8") as handle:
        if comment:
            handle.write(f"c {comment}\n")
        handle.write(f"p cnf {num_vars} {len(clauses)}\n")
        for clause in clauses:
            handle.write(" ".join(str(literal) for literal in clause))
            handle.write(" 0\n")


def write_raw(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8")


def write_manifest(path: Path, rows: list[tuple[str, str, str, str, str, str]]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    lines = ["path\texpected\tdetector\tmax_seconds\tmode\tnotes"]
    lines.extend("\t".join(row) for row in rows)
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def mycielski_graph(iterations: int) -> list[set[int]]:
    adjacency = [{1}, {0}]
    for _ in range(iterations):
        n = len(adjacency)
        new_adjacency = [set(neighbors) for neighbors in adjacency]
        new_adjacency.extend(set() for _ in range(n + 1))
        apex = 2 * n

        for vertex, neighbors in enumerate(adjacency):
            copy_vertex = n + vertex
            for neighbor in neighbors:
                new_adjacency[copy_vertex].add(neighbor)
                new_adjacency[neighbor].add(copy_vertex)
            new_adjacency[copy_vertex].add(apex)
            new_adjacency[apex].add(copy_vertex)

        adjacency = new_adjacency
    return adjacency


def graph_coloring_cnf(adjacency: list[set[int]], color_count: int) -> tuple[int, list[list[int]]]:
    clauses: list[list[int]] = []
    vertex_count = len(adjacency)

    def variable(vertex: int, color: int) -> int:
        return vertex * color_count + color + 1

    for vertex in range(vertex_count):
        clauses.append([variable(vertex, color) for color in range(color_count)])

    for vertex in range(vertex_count):
        for first_color in range(color_count):
            for second_color in range(first_color + 1, color_count):
                clauses.append([-variable(vertex, first_color), -variable(vertex, second_color)])

    for first_vertex in range(vertex_count):
        for second_vertex in sorted(adjacency[first_vertex]):
            if first_vertex >= second_vertex:
                continue
            for color in range(color_count):
                clauses.append([-variable(first_vertex, color), -variable(second_vertex, color)])

    return vertex_count * color_count, clauses


def complete_graph(size: int) -> list[set[int]]:
    return [set(range(size)) - {vertex} for vertex in range(size)]


def cycle_graph(size: int) -> list[set[int]]:
    adjacency = [set() for _ in range(size)]
    for vertex in range(size):
        other = (vertex + 1) % size
        adjacency[vertex].add(other)
        adjacency[other].add(vertex)
    return adjacency


def bipartite_graph(left_count: int, right_count: int) -> list[set[int]]:
    adjacency = [set() for _ in range(left_count + right_count)]
    for left in range(left_count):
        for right in range(left_count, left_count + right_count):
            adjacency[left].add(right)
            adjacency[right].add(left)
    return adjacency


def planted_colorable_graph(vertex_count: int, color_count: int, seed: int) -> list[set[int]]:
    rng = random.Random(seed)
    colors = [vertex % color_count for vertex in range(vertex_count)]
    adjacency = [set() for _ in range(vertex_count)]
    for first in range(vertex_count):
        for second in range(first + 1, vertex_count):
            if colors[first] != colors[second] and rng.random() < 0.45:
                adjacency[first].add(second)
                adjacency[second].add(first)
    return adjacency


def random_graph_with_k3(vertex_count: int, seed: int) -> list[set[int]]:
    rng = random.Random(seed)
    adjacency = [set() for _ in range(vertex_count)]
    for first, second in ((0, 1), (0, 2), (1, 2)):
        adjacency[first].add(second)
        adjacency[second].add(first)
    for first in range(vertex_count):
        for second in range(first + 1, vertex_count):
            if second < 3 and first < 3:
                continue
            if rng.random() < 0.16:
                adjacency[first].add(second)
                adjacency[second].add(first)
    return adjacency


def planted_3sat(num_vars: int, num_clauses: int, seed: int) -> list[list[int]]:
    rng = random.Random(seed)
    clauses: list[list[int]] = []
    seen: set[tuple[int, ...]] = set()
    while len(clauses) < num_clauses:
        variables = rng.sample(range(1, num_vars + 1), 3)
        literals = []
        has_positive = False
        for variable in variables:
            if rng.random() < 0.55:
                literals.append(variable)
                has_positive = True
            else:
                literals.append(-variable)
        if not has_positive:
            positive_index = rng.randrange(3)
            literals[positive_index] = abs(literals[positive_index])
        key = tuple(sorted(literals, key=abs))
        if key in seen:
            continue
        seen.add(key)
        clauses.append(literals)
    return clauses


def xor_equation_cnf(variables: tuple[int, ...], rhs: int) -> list[list[int]]:
    clauses: list[list[int]] = []
    for mask in range(1 << len(variables)):
        parity = mask.bit_count() & 1
        if parity == rhs:
            continue
        clause = []
        for index, variable in enumerate(variables):
            bit = (mask >> index) & 1
            clause.append(-variable if bit else variable)
        clauses.append(clause)
    return clauses


def xor_sparse_unsat(num_vars: int = 240, equations: int = 330, seed: int = 1) -> list[list[int]]:
    rng = random.Random(seed)
    rows: list[tuple[tuple[int, ...], int]] = [((1, 2, 3), 0), ((1, 2, 3), 1)]
    while len(rows) < equations:
        width = 3 if len(rows) % 2 == 0 else 4
        variables = tuple(sorted(rng.sample(range(1, num_vars + 1), width)))
        rhs = rng.randrange(2)
        rows.append((variables, rhs))

    clauses: list[list[int]] = []
    for variables, rhs in rows:
        clauses.extend(xor_equation_cnf(variables, rhs))
    return clauses


def pigeonhole(pigeons: int, holes: int) -> tuple[int, list[list[int]]]:
    clauses: list[list[int]] = []

    def variable(pigeon: int, hole: int) -> int:
        return pigeon * holes + hole + 1

    for pigeon in range(pigeons):
        clauses.append([variable(pigeon, hole) for hole in range(holes)])

    for hole in range(holes):
        for first_pigeon in range(pigeons):
            for second_pigeon in range(first_pigeon + 1, pigeons):
                clauses.append([-variable(first_pigeon, hole), -variable(second_pigeon, hole)])

    return pigeons * holes, clauses


def permute_literals(clauses: list[list[int]], permutation: dict[int, int]) -> list[list[int]]:
    return [
        [(1 if literal > 0 else -1) * permutation[abs(literal)] for literal in clause]
        for clause in clauses
    ]


def mutate_hard_mycielski() -> list[tuple[str, int, list[list[int]], str, str, str]]:
    hard_path = ROOT / "course_cnf_tests" / (
        "cnf_training_complex__complex_cnf_hard__mycielski_iter4_color5_unsat.cnf"
    )
    import satsolver

    num_vars, clauses = satsolver.parse_dimacs_file(str(hard_path))
    negative_index = next(
        index for index, clause in enumerate(clauses) if len(clause) == 2 and clause[0] < 0 and clause[1] < 0
    )
    positive_index = next(index for index, clause in enumerate(clauses) if all(literal > 0 for literal in clause))
    rng = random.Random(42)
    shuffled = list(clauses)
    rng.shuffle(shuffled)
    permutation = {variable: ((variable * 37) % num_vars) + 1 for variable in range(1, num_vars + 1)}
    if len(set(permutation.values())) != num_vars:
        permutation = {variable: num_vars + 1 - variable for variable in range(1, num_vars + 1)}
    changed_block = [list(clause) for clause in clauses]
    changed_block[positive_index] = changed_block[positive_index][:-1] + [num_vars]

    return [
        ("shuffle_clauses.cnf", num_vars, shuffled, "UNSAT", "true", "same formula with clause order shuffled"),
        (
            "renumber_variables_permutation.cnf",
            num_vars,
            permute_literals(clauses, permutation),
            "UNSAT",
            "false",
            "same formula under a deterministic variable permutation; strict color-position parser may reject safely",
        ),
        (
            "remove_one_edge_clause.cnf",
            num_vars,
            [clause for index, clause in enumerate(clauses) if index != negative_index],
            "UNKNOWN",
            "false",
            "broken exact graph-coloring structure; detector must reject",
        ),
        (
            "add_one_extra_edge_clause.cnf",
            num_vars,
            clauses + [[-1, -num_vars]],
            "UNKNOWN",
            "false",
            "extra constraint breaks strict edge-color completeness",
        ),
        (
            "remove_one_vertex_color_clause.cnf",
            num_vars,
            [clause for index, clause in enumerate(clauses) if index != positive_index],
            "UNKNOWN",
            "false",
            "missing at-least-one-color clause",
        ),
        (
            "duplicate_some_clauses.cnf",
            num_vars,
            clauses + clauses[:3],
            "UNKNOWN",
            "false",
            "duplicate clauses should not be accepted by the strict detector",
        ),
        (
            "add_tautology_clause.cnf",
            num_vars,
            clauses + [[1, -1]],
            "UNKNOWN",
            "false",
            "tautology clause breaks exact graph-coloring structure",
        ),
        (
            "change_one_color_block.cnf",
            num_vars,
            changed_block,
            "UNKNOWN",
            "false",
            "malformed color block must reject",
        ),
        (
            "add_unused_variable.cnf",
            num_vars + 1,
            clauses,
            "UNKNOWN",
            "false",
            "declared variable not covered by color blocks",
        ),
    ]


def generate_mycielski() -> None:
    rows: list[tuple[str, str, str, str, str, str]] = []
    cases = [
        ("mycielski_iter2_color3_unsat.cnf", 2, 3, "UNSAT", "true"),
        ("mycielski_iter2_color4_sat.cnf", 2, 4, "SAT", "false"),
        ("mycielski_iter3_color4_unsat.cnf", 3, 4, "UNSAT", "true"),
        ("mycielski_iter3_color5_sat.cnf", 3, 5, "SAT", "false"),
        ("mycielski_iter4_color5_unsat.cnf", 4, 5, "UNSAT", "true"),
        ("mycielski_iter4_color6_sat.cnf", 4, 6, "SAT", "false"),
    ]
    for filename, iterations, color_count, expected, detector in cases:
        num_vars, clauses = graph_coloring_cnf(mycielski_graph(iterations), color_count)
        write_dimacs(GENERATED / "mycielski" / filename, num_vars, clauses, filename)
        rows.append((filename, expected, detector, "60", "solve", f"Mycielski iter{iterations} color{color_count}"))
    write_manifest(GENERATED / "mycielski" / "MANIFEST.tsv", rows)


def generate_graph_coloring() -> None:
    rows: list[tuple[str, str, str, str, str, str]] = []
    cases = [
        ("K4_color3_unsat.cnf", complete_graph(4), 3, "UNSAT"),
        ("K4_color4_sat.cnf", complete_graph(4), 4, "SAT"),
        ("K5_color4_unsat.cnf", complete_graph(5), 4, "UNSAT"),
        ("C5_color2_unsat.cnf", cycle_graph(5), 2, "UNSAT"),
        ("C5_color3_sat.cnf", cycle_graph(5), 3, "SAT"),
        ("bipartite_20_color2_sat.cnf", bipartite_graph(10, 10), 2, "SAT"),
        ("random_graph_v20_k3_sat.cnf", planted_colorable_graph(20, 3, 7), 3, "SAT"),
        ("random_graph_v20_k2_unsat.cnf", random_graph_with_k3(20, 8), 2, "UNSAT"),
    ]
    for filename, adjacency, color_count, expected in cases:
        num_vars, clauses = graph_coloring_cnf(adjacency, color_count)
        write_dimacs(GENERATED / "graph_coloring" / filename, num_vars, clauses, filename)
        detector = "true" if filename == "C5_color2_unsat.cnf" else "false"
        notes = (
            "C5 is also the first Mycielski graph M(K2)"
            if filename == "C5_color2_unsat.cnf"
            else "ordinary graph-coloring guard"
        )
        rows.append((filename, expected, detector, "60", "solve", notes))
    write_manifest(GENERATED / "graph_coloring" / "MANIFEST.tsv", rows)


def generate_near_limit() -> None:
    rows: list[tuple[str, str, str, str, str, str]] = []
    cases: list[tuple[str, int, list[list[int]], str, str]] = [
        ("random3sat_n500_m2000_seed1.cnf", 500, planted_3sat(500, 2000, 1), "SAT", "planted all-true SAT"),
        ("random3sat_n500_m2000_seed2.cnf", 500, planted_3sat(500, 2000, 2), "SAT", "planted all-true SAT"),
        ("planted3sat_n450_m1900_seed1.cnf", 450, planted_3sat(450, 1900, 11), "SAT", "planted all-true SAT"),
        ("planted3sat_n450_m1900_seed2.cnf", 450, planted_3sat(450, 1900, 12), "SAT", "planted all-true SAT"),
        ("xor_sparse_unsat_n240_eq330_w3_4_seed1.cnf", 240, xor_sparse_unsat(), "UNSAT", "inconsistent XOR system"),
    ]
    php_vars, php_clauses = pigeonhole(15, 14)
    cases.append(("pigeonhole_php_15_into_14_near_limit.cnf", php_vars, php_clauses, "UNSAT", "near-limit pigeonhole"))

    for filename, num_vars, clauses, expected, notes in cases:
        write_dimacs(GENERATED / "random_near_limit" / filename, num_vars, clauses, filename)
        rows.append((filename, expected, "any", "60", "solve", notes))
    write_manifest(GENERATED / "random_near_limit" / "MANIFEST.tsv", rows)


def generate_portfolio_density() -> None:
    rows: list[tuple[str, str, str, str, str, str]] = []
    densities = (4.20, 4.25, 4.30, 4.35, 4.40, 4.50)
    sizes = (260, 320, 400)
    seeds = range(1, 6)
    for density in densities:
        for num_vars in sizes:
            clause_count = int(round(num_vars * density))
            for seed in seeds:
                filename = f"planted3sat_n{num_vars}_d{density:.2f}_seed{seed}.cnf"
                clauses = planted_3sat(num_vars, clause_count, seed + int(density * 1000) + num_vars)
                write_dimacs(GENERATED / "portfolio_density" / filename, num_vars, clauses, filename)
                detector = "portfolio_true" if density <= 4.30 else "portfolio_false"
                rows.append((filename, "SAT", detector, "60", "solve", "portfolio density boundary planted SAT"))
    write_manifest(GENERATED / "portfolio_density" / "MANIFEST.tsv", rows)


def generate_parser_cases() -> None:
    valid_rows: list[tuple[str, str, str, str, str, str]] = []
    invalid_rows: list[tuple[str, str, str, str, str, str]] = []
    valid_cases = {
        "empty_formula_n0.cnf": (0, [], "SAT"),
        "empty_formula_n5.cnf": (5, [], "SAT"),
        "empty_clause_unsat.cnf": (1, [[]], "UNSAT"),
        "unit_conflict_unsat.cnf": (1, [[1], [-1]], "UNSAT"),
        "duplicate_literals_sat.cnf": (2, [[1, 1], [2]], "SAT"),
        "tautology_only_sat.cnf": (1, [[1, -1]], "SAT"),
        "tautology_plus_empty_unsat.cnf": (1, [[1, -1], []], "UNSAT"),
        "unmentioned_variables_sat.cnf": (5, [[1], [-2, 1]], "SAT"),
    }
    for filename, (num_vars, clauses, expected) in valid_cases.items():
        write_dimacs(GENERATED / "parser_edge_cases" / filename, num_vars, clauses, filename)
        valid_rows.append((filename, expected, "any", "20", "solve", "valid DIMACS edge case"))

    write_raw(
        GENERATED / "parser_edge_cases" / "comments_before_header.cnf",
        "c first comment\nc second comment\np cnf 1 1\n1 0\n",
    )
    write_raw(
        GENERATED / "parser_edge_cases" / "comments_after_header.cnf",
        "p cnf 1 1\nc after header\n1 0\n",
    )
    write_raw(
        GENERATED / "parser_edge_cases" / "blank_lines.cnf",
        "\n\nc blank lines\n\np cnf 2 1\n\n1 -2 0\n\n",
    )
    write_raw(
        GENERATED / "parser_edge_cases" / "multiple_clauses_on_one_line.cnf",
        "p cnf 2 2\n1 0 -2 0\n",
    )
    for filename in (
        "comments_before_header.cnf",
        "comments_after_header.cnf",
        "blank_lines.cnf",
        "multiple_clauses_on_one_line.cnf",
    ):
        valid_rows.append((filename, "SAT", "any", "20", "solve", "valid parser formatting edge case"))

    invalid_cases = {
        "missing_header.cnf": "1 0\n",
        "bad_header_token.cnf": "p sat 1 1\n1 0\n",
        "wrong_clause_count.cnf": "p cnf 1 2\n1 0\n",
        "literal_out_of_range.cnf": "p cnf 1 1\n2 0\n",
        "unterminated_clause_no_zero.cnf": "p cnf 1 1\n1\n",
        "non_integer_literal.cnf": "p cnf 1 1\nx 0\n",
        "negative_var_index_invalid_token.cnf": "p cnf 1 1\n--1 0\n",
    }
    for filename, text in invalid_cases.items():
        write_raw(GENERATED / "parser_edge_cases" / filename, text)
        invalid_rows.append((filename, "ERROR", "any", "20", "invalid", "invalid DIMACS should fail"))

    write_manifest(GENERATED / "parser_edge_cases" / "MANIFEST.tsv", valid_rows + invalid_rows)


def generate_mutations() -> None:
    rows: list[tuple[str, str, str, str, str, str]] = []
    for filename, num_vars, clauses, expected, detector, notes in mutate_hard_mycielski():
        write_dimacs(GENERATED / "mutated_mycielski" / filename, num_vars, clauses, filename)
        mode = "solve" if expected in {"SAT", "UNSAT"} and detector == "true" else "detector"
        rows.append((filename, expected, detector, "60", mode, notes))

    sat_path = GENERATED / "mycielski" / "mycielski_iter3_color5_sat.cnf"
    import satsolver

    num_vars, clauses = satsolver.parse_dimacs_file(str(sat_path))
    sat_mutations = [
        ("sat_guard_duplicate_clause.cnf", num_vars, clauses + [clauses[0]], "SAT", "false", "SAT guard with duplicate clause"),
        ("sat_guard_add_tautology.cnf", num_vars, clauses + [[1, -1]], "SAT", "false", "SAT guard with tautology"),
    ]
    for filename, case_vars, case_clauses, expected, detector, notes in sat_mutations:
        write_dimacs(GENERATED / "mutated_mycielski" / filename, case_vars, case_clauses, filename)
        rows.append((filename, expected, detector, "60", "solve", notes))
    write_manifest(GENERATED / "mutated_mycielski" / "MANIFEST.tsv", rows)


def main(argv: list[str] | None = None) -> int:
    global ROOT, GENERATED

    parser = argparse.ArgumentParser(description="Generate deterministic SAT solver regression CNFs.")
    parser.add_argument("--root", type=Path, default=ROOT)
    args = parser.parse_args(argv)
    ROOT = args.root.resolve()
    GENERATED = ROOT / "tests" / "generated"

    generate_mycielski()
    generate_graph_coloring()
    generate_near_limit()
    generate_portfolio_density()
    generate_parser_cases()
    generate_mutations()
    print(f"Generated regression CNFs under {GENERATED}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
