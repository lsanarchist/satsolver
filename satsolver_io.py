from __future__ import annotations

from collections.abc import Callable


def parse_dimacs_bytes(data: bytes) -> tuple[int, list[list[int]]]:
    num_vars: int | None = None
    num_clauses: int | None = None
    clauses: list[list[int]] = []
    current: list[int] = []
    header_seen = False

    for raw_line in data.splitlines():
        line = raw_line.strip()
        if not line or line.startswith(b"c"):
            continue
        if line.startswith(b"%"):
            break
        if line.startswith(b"p"):
            if header_seen:
                raise ValueError("Multiple DIMACS problem lines are not allowed")
            parts = line.split()
            if len(parts) != 4 or parts[1] != b"cnf":
                raise ValueError("Invalid DIMACS problem line")
            num_vars = int(parts[2])
            num_clauses = int(parts[3])
            header_seen = True
            continue
        if not header_seen:
            raise ValueError("DIMACS clauses must appear after the problem line")

        for token in line.split():
            literal = int(token)
            if literal == 0:
                clauses.append(current)
                current = []
            else:
                assert num_vars is not None
                if abs(literal) > num_vars:
                    raise ValueError(
                        f"Literal {literal} exceeds declared variable range 1..{num_vars}"
                    )
                current.append(literal)

    if num_vars is None or num_clauses is None:
        raise ValueError("Missing DIMACS problem line")
    if current:
        raise ValueError("Last clause is missing its terminating 0")
    if len(clauses) != num_clauses:
        raise ValueError(
            f"Clause count mismatch: header says {num_clauses}, parsed {len(clauses)}"
        )

    return num_vars, clauses


def parse_dimacs(text: str) -> tuple[int, list[list[int]]]:
    return parse_dimacs_bytes(text.encode("utf-8"))


def parse_dimacs_file(path: str) -> tuple[int, list[list[int]]]:
    with open(path, "rb") as handle:
        return parse_dimacs_bytes(handle.read())


def write_result(
    path: str,
    model: list[int] | None,
    *,
    format_model: Callable[[list[int]], str],
) -> None:
    with open(path, "wb") as handle:
        if model is None:
            handle.write(b"UNSAT")
            return
        handle.write(b"SAT\n")
        handle.write(format_model(model).encode("ascii"))
