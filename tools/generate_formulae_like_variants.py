from __future__ import annotations

import argparse
import shutil
from dataclasses import dataclass
from pathlib import Path

from generate_formulae_like import (
    Formula,
    exactly_one,
    graph_coloring_unsat,
    horn_chain,
    make_formula,
    nqueens,
    php,
    planted_3sat,
    planted_graph_coloring,
    unit_sat,
    validate_ranges,
    xor_system,
)


ROOT = Path(__file__).resolve().parents[1]
BASE_SEED = 20260601


@dataclass(frozen=True)
class VariantSpec:
    index: int
    out_dir: Path

    @property
    def seed_base(self) -> int:
        return BASE_SEED + self.index * 10000

    def seed(self, value: int) -> int:
        return self.seed_base + value

    def pick(self, values: tuple[int, ...]) -> int:
        return values[(self.index - 1) % len(values)]


def build_formulas(spec: VariantSpec) -> list[Formula]:
    medium_test3_clauses = spec.pick((650, 682, 710))
    medium_test4_clauses = spec.pick((820, 850, 880))
    medium_graph_colors = spec.pick((7, 8, 9))
    medium_graph_vertices = spec.pick((30, 34, 38))
    medium_graph_edges = spec.pick((150, 175, 200))

    large_specs = (
        ((220, 1000), (260, 1060), (300, 1000), (360, 1000), (420, 1050), (480, 1120)),
        ((230, 1035), (270, 1080), (310, 1010), (370, 1040), (430, 1120), (490, 1200)),
        ((240, 1050), (280, 1120), (320, 1020), (380, 1060), (440, 1150), (500, 1250)),
    )
    large_planted = large_specs[(spec.index - 1) % len(large_specs)]
    large_test1_seed = (4301, 5301, 30301)[(spec.index - 1) % 3]
    large_xor_vars = spec.pick((240, 256, 280))
    large_xor_equations = spec.pick((340, 380, 430))
    large_coloring_vertices = spec.pick((115, 120, 125))
    large_coloring_edges = spec.pick((480, 490, 500))

    special_dense_clauses = spec.pick((1300, 1450, 1600))
    special_hard_colors = spec.pick((9, 10, 11))
    special_xor_vars = spec.pick((300, 320, 340))
    special_xor_equations = spec.pick((420, 450, 480))
    special_coloring_edges = spec.pick((250, 265, 280))

    return [
        make_formula("small", "test_1.cnf", "planted_3sat", planted_3sat(20, 85, seed=spec.seed(101)), "hidden assignment near 4.25 ratio"),
        make_formula("small", "test_2.cnf", "planted_3sat", planted_3sat(30, 128, seed=spec.seed(102)), "hidden assignment near 4.27 ratio"),
        make_formula("small", "test_3.cnf", "planted_3sat", planted_3sat(40, 170, seed=spec.seed(103)), "hidden assignment near 4.25 ratio"),
        make_formula("small", "test_4.cnf", "xor_parity", xor_system(18, 12, seed=spec.seed(104), satisfiable=False), "contradictory sparse parity pair"),
        make_formula("small", "test_5.cnf", "xor_parity", xor_system(24, 24, seed=spec.seed(105), satisfiable=True), "sparse parity system with hidden model"),
        make_formula("small", "test_6.cnf", "pigeonhole", php(spec.pick((5, 6, 5)), spec.pick((4, 5, 4))), "classic PHP unsat"),
        make_formula("small", "test_7.cnf", "graph_coloring", graph_coloring_unsat(spec.pick((3, 4, 3))), "complete graph coloring UNSAT"),
        make_formula("small", "test_8.cnf", "nqueens", nqueens(5), "5x5 queens"),
        make_formula("small", "test_9.cnf", "cardinality", exactly_one(spec.pick((8, 9, 10)), spec.pick((4, 5, 4)), satisfiable=True), "independent exactly-one groups"),
        make_formula("small", "test_10.cnf", "horn_chain", horn_chain(spec.pick((40, 44, 48)), satisfiable=False), "forced true chain ending with false"),
        make_formula("medium", "test_1.cnf", "planted_3sat", planted_3sat(60, 255, seed=spec.seed(201)), "hidden assignment near 4.25 ratio"),
        make_formula("medium", "test_2.cnf", "planted_3sat", planted_3sat(100, 425, seed=spec.seed(202)), "hidden assignment near 4.25 ratio"),
        make_formula("medium", "test_3.cnf", "planted_3sat", planted_3sat(160, medium_test3_clauses, seed=spec.seed(203)), "hidden assignment near threshold"),
        make_formula("medium", "test_4.cnf", "planted_3sat", planted_3sat(200, medium_test4_clauses, seed=spec.seed(204)), "hidden assignment near threshold"),
        make_formula("medium", "test_5.cnf", "pigeonhole", php(9, 8), "classic PHP unsat"),
        make_formula("medium", "test_6.cnf", "pigeonhole", php(10, 9), "classic PHP unsat"),
        make_formula("medium", "test_7.cnf", "graph_coloring", graph_coloring_unsat(medium_graph_colors), "complete graph coloring UNSAT"),
        make_formula("medium", "test_8.cnf", "xor_parity", xor_system(96, 125, seed=spec.seed(208), satisfiable=True), "sparse parity system with hidden model"),
        make_formula("medium", "test_9.cnf", "xor_parity", xor_system(128, 165, seed=spec.seed(209), satisfiable=False), "contradictory sparse parity pair"),
        make_formula("medium", "test_10.cnf", "graph_coloring", planted_graph_coloring(medium_graph_vertices, 3, medium_graph_edges, seed=spec.seed(210)), "planted 3-coloring"),
        make_formula("large", "test_1.cnf", "planted_3sat", planted_3sat(*large_planted[0], seed=large_test1_seed), "large hidden assignment instance"),
        make_formula("large", "test_2.cnf", "planted_3sat", planted_3sat(*large_planted[1], seed=spec.seed(302)), "large hidden assignment instance"),
        make_formula("large", "test_3.cnf", "planted_3sat", planted_3sat(*large_planted[2], seed=spec.seed(303)), "large lower-density hidden assignment instance"),
        make_formula("large", "test_4.cnf", "planted_3sat", planted_3sat(*large_planted[3], seed=spec.seed(304)), "large lower-density hidden assignment instance"),
        make_formula("large", "test_5.cnf", "planted_3sat", planted_3sat(*large_planted[4], seed=spec.seed(305)), "large lower-density hidden assignment instance"),
        make_formula("large", "test_6.cnf", "planted_3sat", planted_3sat(*large_planted[5], seed=spec.seed(306)), "large lower-density hidden assignment instance"),
        make_formula("large", "test_7.cnf", "pigeonhole", php(15, 14), "large PHP unsat inside clause limit"),
        make_formula("large", "test_8.cnf", "pigeonhole", php(16, 15), "larger PHP unsat inside clause limit"),
        make_formula("large", "test_9.cnf", "xor_parity", xor_system(large_xor_vars, large_xor_equations, seed=spec.seed(309), satisfiable=False), "large contradictory parity system"),
        make_formula("large", "test_10.cnf", "graph_coloring", planted_graph_coloring(large_coloring_vertices, 3, large_coloring_edges, seed=spec.seed(310)), "large planted 3-coloring"),
        make_formula("special", "easy.cnf", "unit", unit_sat(spec.pick((100, 140, 180))), "very easy all-unit SAT"),
        make_formula("special", "dense.cnf", "planted_3sat_dense", planted_3sat(200, special_dense_clauses, seed=spec.seed(401)), "dense hidden-assignment 3-SAT"),
        make_formula("special", "hard.cnf", "graph_coloring", graph_coloring_unsat(special_hard_colors), "complete graph coloring UNSAT"),
        make_formula("special", "xor.cnf", "xor_parity", xor_system(special_xor_vars, special_xor_equations, seed=spec.seed(404), satisfiable=False), "large sparse contradictory parity system"),
        make_formula("special", "coloring.cnf", "graph_coloring", planted_graph_coloring(125, 4, special_coloring_edges, seed=spec.seed(405)), "500-variable planted 4-coloring"),
    ]


def write_formula(spec: VariantSpec, formula: Formula) -> None:
    target = spec.out_dir / formula.category / formula.name
    target.parent.mkdir(parents=True, exist_ok=True)
    with target.open("w", encoding="ascii") as handle:
        handle.write("c generated_for formulae_like_variant benchmark\n")
        handle.write(f"c dataset {spec.out_dir.name}\n")
        handle.write(f"c variant {spec.index}\n")
        handle.write(f"c seed_base {spec.seed_base}\n")
        handle.write(f"c family {formula.family}\n")
        handle.write(f"c expected_status {formula.status}\n")
        handle.write(f"c notes {formula.notes}\n")
        handle.write(f"p cnf {formula.num_vars} {len(formula.clauses)}\n")
        for clause in formula.clauses:
            handle.write(" ".join(str(literal) for literal in clause))
            handle.write(" 0\n")


def write_manifest(spec: VariantSpec, formulas: list[Formula]) -> None:
    manifest = spec.out_dir / "MANIFEST.tsv"
    with manifest.open("w", encoding="utf-8") as handle:
        handle.write("category\tfile\tvars\tclauses\texpected_status\tfamily\tnotes\n")
        for formula in formulas:
            handle.write(
                f"{formula.category}\t{formula.category}/{formula.name}\t"
                f"{formula.num_vars}\t{len(formula.clauses)}\t{formula.status}\t"
                f"{formula.family}\t{formula.notes}\n"
            )


def write_readme(spec: VariantSpec) -> None:
    (spec.out_dir / "README.md").write_text(
        "\n".join(
            [
                f"# {spec.out_dir.name}",
                "",
                "Synthetic DIMACS benchmark set shaped like the LPI assignment data set.",
                "",
                "- `small/`: 10 formulas, 10-50 variables, 20-200 clauses",
                "- `medium/`: 10 formulas, 50-200 variables, 200-1000 clauses",
                "- `large/`: 10 formulas, 200-500 variables, 1000-2000 clauses",
                "- `special/`: 5 structured formulas within the assignment hard limits",
                "",
                f"Variant index: `{spec.index}`",
                f"Seed base: `{spec.seed_base}`",
                "Generated with `python tools/generate_formulae_like_variants.py` using only the Python standard library.",
                "Expected SAT/UNSAT labels are recorded in `MANIFEST.tsv` and as DIMACS comments.",
                "",
            ]
        ),
        encoding="utf-8",
    )


def write_dataset(spec: VariantSpec) -> None:
    formulas = build_formulas(spec)
    validate_ranges(formulas)
    if spec.out_dir.exists():
        shutil.rmtree(spec.out_dir)
    spec.out_dir.mkdir(parents=True)
    for formula in formulas:
        write_formula(spec, formula)
    write_manifest(spec, formulas)
    write_readme(spec)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate several LPI-shaped DIMACS datasets.")
    parser.add_argument("--count", type=int, default=3, help="How many datasets to generate.")
    parser.add_argument("--start", type=int, default=1, help="First variant index.")
    parser.add_argument("--prefix", default="formulae_like_", help="Output directory prefix.")
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    if args.count < 1:
        raise ValueError("--count must be positive")
    for index in range(args.start, args.start + args.count):
        spec = VariantSpec(index=index, out_dir=ROOT / f"{args.prefix}{index:02d}")
        write_dataset(spec)
        print(f"wrote 35 formulas to {spec.out_dir}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
