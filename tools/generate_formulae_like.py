from __future__ import annotations

import random
import shutil
from dataclasses import dataclass
from itertools import combinations, product
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
OUT_DIR = ROOT / "formulae_like"
SEED = 20260531


Clause = tuple[int, ...]


@dataclass(frozen=True)
class Formula:
    category: str
    name: str
    family: str
    status: str
    num_vars: int
    clauses: list[Clause]
    notes: str


def planted_3sat(num_vars: int, num_clauses: int, *, seed: int) -> tuple[int, list[Clause], str]:
    rng = random.Random(seed)
    assignment = [False] + [rng.choice((False, True)) for _ in range(num_vars)]
    clauses: list[Clause] = []
    seen: set[Clause] = set()

    while len(clauses) < num_clauses:
        variables = rng.sample(range(1, num_vars + 1), 3)
        literals = [variable if rng.choice((False, True)) else -variable for variable in variables]
        if not any((literal > 0) == assignment[abs(literal)] for literal in literals):
            index = rng.randrange(3)
            variable = abs(literals[index])
            literals[index] = variable if assignment[variable] else -variable
        clause = tuple(sorted(literals, key=abs))
        if clause in seen:
            continue
        seen.add(clause)
        clauses.append(clause)

    return num_vars, clauses, "SAT"


def php(pigeons: int, holes: int) -> tuple[int, list[Clause], str]:
    def var(pigeon: int, hole: int) -> int:
        return (pigeon - 1) * holes + hole

    clauses: list[Clause] = []
    for pigeon in range(1, pigeons + 1):
        clauses.append(tuple(var(pigeon, hole) for hole in range(1, holes + 1)))
    for hole in range(1, holes + 1):
        for first, second in combinations(range(1, pigeons + 1), 2):
            clauses.append((-var(first, hole), -var(second, hole)))
    return pigeons * holes, clauses, "UNSAT"


def xor_equation_clause(variables: tuple[int, int, int], rhs: int) -> list[Clause]:
    clauses: list[Clause] = []
    for values in product((0, 1), repeat=3):
        if (values[0] ^ values[1] ^ values[2]) == rhs:
            continue
        clauses.append(
            tuple(variable if value == 0 else -variable for variable, value in zip(variables, values))
        )
    return clauses


def xor_system(
    num_vars: int,
    equations: int,
    *,
    seed: int,
    satisfiable: bool,
) -> tuple[int, list[Clause], str]:
    rng = random.Random(seed)
    assignment = [0] + [rng.randrange(2) for _ in range(num_vars)]
    equation_rows: list[tuple[tuple[int, int, int], int]] = []
    seen: set[tuple[tuple[int, int, int], int]] = set()

    if not satisfiable:
        variables = tuple(sorted(rng.sample(range(1, num_vars + 1), 3)))
        rhs = assignment[variables[0]] ^ assignment[variables[1]] ^ assignment[variables[2]]
        equation_rows.append((variables, rhs))
        equation_rows.append((variables, rhs ^ 1))
        seen.add((variables, rhs))
        seen.add((variables, rhs ^ 1))

    while len(equation_rows) < equations:
        variables = tuple(sorted(rng.sample(range(1, num_vars + 1), 3)))
        rhs = assignment[variables[0]] ^ assignment[variables[1]] ^ assignment[variables[2]]
        if not satisfiable and rng.random() < 0.35:
            rhs ^= 1
        row = (variables, rhs)
        if row in seen:
            continue
        seen.add(row)
        equation_rows.append(row)

    clauses: list[Clause] = []
    for variables, rhs in equation_rows:
        clauses.extend(xor_equation_clause(variables, rhs))
    return num_vars, clauses, "SAT" if satisfiable else "UNSAT"


def graph_coloring_unsat(colors: int) -> tuple[int, list[Clause], str]:
    vertices = colors + 1

    def var(vertex: int, color: int) -> int:
        return (vertex - 1) * colors + color

    clauses: list[Clause] = []
    for vertex in range(1, vertices + 1):
        clauses.append(tuple(var(vertex, color) for color in range(1, colors + 1)))
        for first, second in combinations(range(1, colors + 1), 2):
            clauses.append((-var(vertex, first), -var(vertex, second)))

    for first, second in combinations(range(1, vertices + 1), 2):
        for color in range(1, colors + 1):
            clauses.append((-var(first, color), -var(second, color)))
    return vertices * colors, clauses, "UNSAT"


def planted_graph_coloring(
    vertices: int,
    colors: int,
    edges: int,
    *,
    seed: int,
) -> tuple[int, list[Clause], str]:
    rng = random.Random(seed)
    coloring = {vertex: (vertex - 1) % colors + 1 for vertex in range(1, vertices + 1)}
    candidates = [
        edge
        for edge in combinations(range(1, vertices + 1), 2)
        if coloring[edge[0]] != coloring[edge[1]]
    ]
    rng.shuffle(candidates)
    selected_edges = candidates[:edges]

    def var(vertex: int, color: int) -> int:
        return (vertex - 1) * colors + color

    clauses: list[Clause] = []
    for vertex in range(1, vertices + 1):
        clauses.append(tuple(var(vertex, color) for color in range(1, colors + 1)))
        for first, second in combinations(range(1, colors + 1), 2):
            clauses.append((-var(vertex, first), -var(vertex, second)))

    for first, second in selected_edges:
        for color in range(1, colors + 1):
            clauses.append((-var(first, color), -var(second, color)))
    return vertices * colors, clauses, "SAT"


def nqueens(size: int) -> tuple[int, list[Clause], str]:
    def var(row: int, col: int) -> int:
        return row * size + col + 1

    clauses: list[Clause] = []
    for row in range(size):
        clauses.append(tuple(var(row, col) for col in range(size)))
        for first, second in combinations(range(size), 2):
            clauses.append((-var(row, first), -var(row, second)))

    for col in range(size):
        for first, second in combinations(range(size), 2):
            clauses.append((-var(first, col), -var(second, col)))

    cells = [(row, col) for row in range(size) for col in range(size)]
    for (row1, col1), (row2, col2) in combinations(cells, 2):
        if abs(row1 - row2) == abs(col1 - col2):
            clauses.append((-var(row1, col1), -var(row2, col2)))

    return size * size, clauses, "SAT"


def exactly_one(groups: int, size: int, *, satisfiable: bool) -> tuple[int, list[Clause], str]:
    def var(group: int, item: int) -> int:
        return group * size + item + 1

    clauses: list[Clause] = []
    for group in range(groups):
        clauses.append(tuple(var(group, item) for item in range(size)))
        for first, second in combinations(range(size), 2):
            clauses.append((-var(group, first), -var(group, second)))

    if not satisfiable:
        clauses.append((var(0, 0),))
        clauses.append((var(0, 1),))
    return groups * size, clauses, "SAT" if satisfiable else "UNSAT"


def horn_chain(length: int, *, satisfiable: bool) -> tuple[int, list[Clause], str]:
    clauses: list[Clause] = [(1,)]
    for variable in range(1, length):
        clauses.append((-variable, variable + 1))
    if not satisfiable:
        clauses.append((-length,))
    return length, clauses, "SAT" if satisfiable else "UNSAT"


def unit_sat(num_vars: int) -> tuple[int, list[Clause], str]:
    return num_vars, [(variable,) for variable in range(1, num_vars + 1)], "SAT"


def make_formula(
    category: str,
    name: str,
    family: str,
    generated: tuple[int, list[Clause], str],
    notes: str,
) -> Formula:
    num_vars, clauses, status = generated
    return Formula(category, name, family, status, num_vars, clauses, notes)


def build_formulas() -> list[Formula]:
    return [
        make_formula("small", "test_1.cnf", "planted_3sat", planted_3sat(20, 85, seed=101), "hidden assignment near 4.25 ratio"),
        make_formula("small", "test_2.cnf", "planted_3sat", planted_3sat(30, 128, seed=102), "hidden assignment near 4.27 ratio"),
        make_formula("small", "test_3.cnf", "planted_3sat", planted_3sat(40, 170, seed=103), "hidden assignment near 4.25 ratio"),
        make_formula("small", "test_4.cnf", "xor_parity", xor_system(18, 12, seed=104, satisfiable=False), "contradictory sparse parity pair"),
        make_formula("small", "test_5.cnf", "xor_parity", xor_system(24, 24, seed=105, satisfiable=True), "sparse parity system with hidden model"),
        make_formula("small", "test_6.cnf", "pigeonhole", php(5, 4), "classic PHP unsat"),
        make_formula("small", "test_7.cnf", "graph_coloring", graph_coloring_unsat(3), "K4 is not 3-colorable"),
        make_formula("small", "test_8.cnf", "nqueens", nqueens(5), "5x5 queens"),
        make_formula("small", "test_9.cnf", "cardinality", exactly_one(8, 4, satisfiable=True), "independent exactly-one groups"),
        make_formula("small", "test_10.cnf", "horn_chain", horn_chain(48, satisfiable=False), "forced true chain ending with false"),
        make_formula("medium", "test_1.cnf", "planted_3sat", planted_3sat(60, 255, seed=201), "hidden assignment near 4.25 ratio"),
        make_formula("medium", "test_2.cnf", "planted_3sat", planted_3sat(100, 425, seed=202), "hidden assignment near 4.25 ratio"),
        make_formula("medium", "test_3.cnf", "planted_3sat", planted_3sat(160, 682, seed=203), "hidden assignment near 4.26 ratio"),
        make_formula("medium", "test_4.cnf", "planted_3sat", planted_3sat(200, 850, seed=204), "hidden assignment near 4.25 ratio"),
        make_formula("medium", "test_5.cnf", "pigeonhole", php(9, 8), "classic PHP unsat"),
        make_formula("medium", "test_6.cnf", "pigeonhole", php(10, 9), "classic PHP unsat"),
        make_formula("medium", "test_7.cnf", "graph_coloring", graph_coloring_unsat(7), "K8 is not 7-colorable"),
        make_formula("medium", "test_8.cnf", "xor_parity", xor_system(96, 125, seed=208, satisfiable=True), "sparse parity system with hidden model"),
        make_formula("medium", "test_9.cnf", "xor_parity", xor_system(128, 165, seed=209, satisfiable=False), "contradictory sparse parity pair"),
        make_formula("medium", "test_10.cnf", "graph_coloring", planted_graph_coloring(30, 3, 150, seed=210), "planted 3-coloring"),
        make_formula("large", "test_1.cnf", "planted_3sat", planted_3sat(220, 1050, seed=301), "large hidden assignment instance"),
        make_formula("large", "test_2.cnf", "planted_3sat", planted_3sat(260, 1108, seed=302), "large hidden assignment instance"),
        make_formula("large", "test_3.cnf", "planted_3sat", planted_3sat(300, 1000, seed=303), "large lower-density hidden assignment instance"),
        make_formula("large", "test_4.cnf", "planted_3sat", planted_3sat(360, 1000, seed=304), "large lower-density hidden assignment instance"),
        make_formula("large", "test_5.cnf", "planted_3sat", planted_3sat(420, 1100, seed=305), "large lower-density hidden assignment instance"),
        make_formula("large", "test_6.cnf", "planted_3sat", planted_3sat(480, 1200, seed=306), "large lower-density hidden assignment instance"),
        make_formula("large", "test_7.cnf", "pigeonhole", php(15, 14), "large PHP unsat inside clause limit"),
        make_formula("large", "test_8.cnf", "pigeonhole", php(16, 15), "larger PHP unsat inside clause limit"),
        make_formula("large", "test_9.cnf", "xor_parity", xor_system(256, 380, seed=309, satisfiable=False), "large contradictory parity system"),
        make_formula("large", "test_10.cnf", "graph_coloring", planted_graph_coloring(120, 3, 480, seed=310), "large planted 3-coloring"),
        make_formula("special", "easy.cnf", "unit", unit_sat(120), "very easy all-unit SAT"),
        make_formula("special", "dense.cnf", "planted_3sat_dense", planted_3sat(200, 1500, seed=401), "dense hidden-assignment 3-SAT"),
        make_formula("special", "hard.cnf", "graph_coloring", graph_coloring_unsat(9), "K10 is not 9-colorable"),
        make_formula("special", "xor.cnf", "xor_parity", xor_system(320, 480, seed=404, satisfiable=False), "large sparse contradictory parity system"),
        make_formula("special", "coloring.cnf", "graph_coloring", planted_graph_coloring(125, 4, 275, seed=405), "500-variable planted 4-coloring"),
    ]


def validate_ranges(formulas: list[Formula]) -> None:
    expected_counts = {"small": 10, "medium": 10, "large": 10, "special": 5}
    ranges = {
        "small": ((10, 50), (20, 200)),
        "medium": ((50, 200), (200, 1000)),
        "large": ((200, 500), (1000, 2000)),
        "special": ((1, 500), (1, 2000)),
    }
    for category, expected in expected_counts.items():
        actual = sum(1 for formula in formulas if formula.category == category)
        if actual != expected:
            raise ValueError(f"{category} has {actual} formulas, expected {expected}")

    for formula in formulas:
        var_range, clause_range = ranges[formula.category]
        if not var_range[0] <= formula.num_vars <= var_range[1]:
            raise ValueError(f"{formula.category}/{formula.name} has {formula.num_vars} vars")
        if len(formula.clauses) != len(set(formula.clauses)):
            raise ValueError(f"{formula.category}/{formula.name} contains duplicate clauses")
        if not clause_range[0] <= len(formula.clauses) <= clause_range[1]:
            raise ValueError(f"{formula.category}/{formula.name} has {len(formula.clauses)} clauses")
        for clause in formula.clauses:
            for literal in clause:
                if abs(literal) < 1 or abs(literal) > formula.num_vars:
                    raise ValueError(f"{formula.category}/{formula.name} literal {literal} out of range")


def write_formula(formula: Formula) -> None:
    target = OUT_DIR / formula.category / formula.name
    target.parent.mkdir(parents=True, exist_ok=True)
    with target.open("w", encoding="ascii") as handle:
        handle.write("c generated_for formulae_like benchmark\n")
        handle.write(f"c seed {SEED}\n")
        handle.write(f"c family {formula.family}\n")
        handle.write(f"c expected_status {formula.status}\n")
        handle.write(f"c notes {formula.notes}\n")
        handle.write(f"p cnf {formula.num_vars} {len(formula.clauses)}\n")
        for clause in formula.clauses:
            handle.write(" ".join(str(literal) for literal in clause))
            handle.write(" 0\n")


def write_manifest(formulas: list[Formula]) -> None:
    manifest = OUT_DIR / "MANIFEST.tsv"
    with manifest.open("w", encoding="utf-8") as handle:
        handle.write("category\tfile\tvars\tclauses\texpected_status\tfamily\tnotes\n")
        for formula in formulas:
            handle.write(
                f"{formula.category}\t{formula.category}/{formula.name}\t"
                f"{formula.num_vars}\t{len(formula.clauses)}\t{formula.status}\t"
                f"{formula.family}\t{formula.notes}\n"
            )


def write_readme() -> None:
    (OUT_DIR / "README.md").write_text(
        "\n".join(
            [
                "# formulae_like",
                "",
                "Synthetic DIMACS benchmark set shaped like the LPI assignment data set.",
                "",
                "- `small/`: 10 formulas, 10-50 variables, 20-200 clauses",
                "- `medium/`: 10 formulas, 50-200 variables, 200-1000 clauses",
                "- `large/`: 10 formulas, 200-500 variables, 1000-2000 clauses",
                "- `special/`: 5 structured formulas within the assignment hard limits",
                "",
                "Generated with `python tools/generate_formulae_like.py` using only the Python standard library.",
                "Expected SAT/UNSAT labels are recorded in `MANIFEST.tsv` and as DIMACS comments.",
                "",
            ]
        ),
        encoding="utf-8",
    )


def main() -> int:
    formulas = build_formulas()
    validate_ranges(formulas)
    if OUT_DIR.exists():
        shutil.rmtree(OUT_DIR)
    OUT_DIR.mkdir()
    for formula in formulas:
        write_formula(formula)
    write_manifest(formulas)
    write_readme()
    print(f"wrote {len(formulas)} formulas to {OUT_DIR}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
