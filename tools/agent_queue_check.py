from __future__ import annotations

import argparse
import re
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
DEFAULT_STATE_PATH = ROOT / ".agent" / "STATE.yaml"
DEFAULT_TASK_QUEUE_PATH = ROOT / ".agent" / "TASK_QUEUE.yaml"

REQUIRED_SELECTION_POLICY = {
    "continue_in_progress_first": True,
    "pick_status": "todo",
    "dependencies_must_be_done": True,
    "tie_breaker": ["priority_desc", "phase_asc", "id_asc"],
}
REQUIRED_STATUSES = {"todo", "in_progress", "blocked", "done", "dropped"}
REQUIRED_TASK_KEYS = {
    "id",
    "phase",
    "priority",
    "status",
    "title",
    "size",
    "depends_on",
    "goal",
    "deliverables",
    "verify",
}
INTEGER_PATTERN = re.compile(r"-?\d+\Z")


class YamlSubsetError(ValueError):
    pass


@dataclass(frozen=True)
class ParsedLine:
    indent: int
    content: str
    lineno: int


def parse_scalar(text: str) -> Any:
    if text == "[]":
        return []
    if text == "{}":
        return {}
    if text in {"null", "Null", "NULL"}:
        return None
    if text in {"true", "True", "TRUE"}:
        return True
    if text in {"false", "False", "FALSE"}:
        return False
    if INTEGER_PATTERN.fullmatch(text):
        return int(text)
    if len(text) >= 2 and text[0] == text[-1] and text[0] in {"'", '"'}:
        return text[1:-1]
    return text


def tokenize_yaml_subset(text: str) -> list[ParsedLine]:
    parsed_lines: list[ParsedLine] = []
    for lineno, raw_line in enumerate(text.splitlines(), start=1):
        stripped = raw_line.strip()
        if not stripped or stripped.startswith("#"):
            continue
        if "\t" in raw_line:
            raise YamlSubsetError(f"line {lineno}: tabs are not supported")
        indent = len(raw_line) - len(raw_line.lstrip(" "))
        parsed_lines.append(ParsedLine(indent=indent, content=raw_line[indent:], lineno=lineno))
    return parsed_lines


def parse_yaml_subset(text: str) -> Any:
    parsed_lines = tokenize_yaml_subset(text)
    if not parsed_lines:
        return None
    if parsed_lines[0].indent != 0:
        raise YamlSubsetError("top-level content must start at indentation 0")
    value, index = parse_block(parsed_lines, 0, 0)
    if index != len(parsed_lines):
        line = parsed_lines[index]
        raise YamlSubsetError(f"line {line.lineno}: unexpected trailing content")
    return value


def parse_block(lines: list[ParsedLine], index: int, indent: int) -> tuple[Any, int]:
    if index >= len(lines):
        raise YamlSubsetError("unexpected end of YAML input")
    line = lines[index]
    if line.indent != indent:
        raise YamlSubsetError(
            f"line {line.lineno}: expected indentation {indent}, got {line.indent}"
        )
    if line.content.startswith("- "):
        return parse_sequence(lines, index, indent)
    return parse_mapping(lines, index, indent)


def parse_mapping(lines: list[ParsedLine], index: int, indent: int) -> tuple[dict[str, Any], int]:
    mapping: dict[str, Any] = {}

    while index < len(lines):
        line = lines[index]
        if line.indent < indent:
            break
        if line.indent > indent:
            raise YamlSubsetError(
                f"line {line.lineno}: unexpected indentation {line.indent} inside mapping"
            )
        if line.content.startswith("- "):
            raise YamlSubsetError(f"line {line.lineno}: unexpected list item inside mapping")
        key, separator, remainder = line.content.partition(":")
        if not separator or not key.strip():
            raise YamlSubsetError(f"line {line.lineno}: expected a key-value mapping entry")
        key = key.strip()
        remainder = remainder.lstrip()
        if key in mapping:
            raise YamlSubsetError(f"line {line.lineno}: duplicate key {key!r}")
        index += 1
        if remainder:
            mapping[key] = parse_scalar(remainder)
            continue
        if index >= len(lines) or lines[index].indent <= indent:
            mapping[key] = None
            continue
        value, index = parse_block(lines, index, lines[index].indent)
        mapping[key] = value

    return mapping, index


def parse_sequence(lines: list[ParsedLine], index: int, indent: int) -> tuple[list[Any], int]:
    items: list[Any] = []

    while index < len(lines):
        line = lines[index]
        if line.indent < indent:
            break
        if line.indent > indent:
            raise YamlSubsetError(
                f"line {line.lineno}: unexpected indentation {line.indent} inside sequence"
            )
        if not line.content.startswith("- "):
            break

        entry = line.content[2:].lstrip()
        index += 1
        if not entry:
            if index >= len(lines) or lines[index].indent <= indent:
                items.append(None)
                continue
            item, index = parse_block(lines, index, lines[index].indent)
            items.append(item)
            continue

        if ":" in entry:
            key, separator, remainder = entry.partition(":")
            if separator and key.strip():
                item: dict[str, Any] = {}
                key = key.strip()
                remainder = remainder.lstrip()
                item[key] = parse_scalar(remainder) if remainder else None

                if item[key] is None and index < len(lines) and lines[index].indent > indent:
                    next_line = lines[index]
                    if next_line.content.startswith("- ") or ":" not in next_line.content:
                        value, index = parse_block(lines, index, next_line.indent)
                        item[key] = value

                if index < len(lines) and lines[index].indent > indent:
                    extra_mapping, index = parse_mapping(lines, index, lines[index].indent)
                    for extra_key, value in extra_mapping.items():
                        if extra_key in item:
                            raise YamlSubsetError(f"duplicate key {extra_key!r} inside list item")
                        item[extra_key] = value

                items.append(item)
                continue

        items.append(parse_scalar(entry))

    return items, index


def load_yaml_subset_file(path: Path) -> Any:
    return parse_yaml_subset(path.read_text(encoding="utf-8"))


def task_sort_key(task: dict[str, Any]) -> tuple[int, int, str]:
    return (-task["priority"], task["phase"], task["id"])


def is_explicitly_blocked(task_id: str, blockers: list[str]) -> bool:
    return any(blocker == task_id or blocker.startswith(f"{task_id}:") for blocker in blockers)


def collect_validation_errors(state: dict[str, Any], task_queue: dict[str, Any]) -> list[str]:
    errors: list[str] = []

    if not isinstance(state, dict):
        return ["STATE.yaml root must be a mapping"]
    if not isinstance(task_queue, dict):
        return ["TASK_QUEUE.yaml root must be a mapping"]

    if state.get("schema_version") != 1:
        errors.append("STATE.yaml schema_version must be 1")
    if state.get("mode") != "autonomous_queue":
        errors.append("STATE.yaml mode must be autonomous_queue")
    if not isinstance(state.get("project"), str) or not state["project"]:
        errors.append("STATE.yaml project must be a non-empty string")
    if not isinstance(state.get("current_phase"), int):
        errors.append("STATE.yaml current_phase must be an integer")

    blockers = state.get("blockers")
    if not isinstance(blockers, list) or not all(isinstance(item, str) for item in blockers):
        errors.append("STATE.yaml blockers must be a list of strings")
        blockers = []

    selection_policy = task_queue.get("selection_policy")
    if selection_policy != REQUIRED_SELECTION_POLICY:
        errors.append("TASK_QUEUE.yaml selection_policy must match the documented deterministic policy")

    statuses = task_queue.get("statuses")
    if not isinstance(statuses, list) or set(statuses) != REQUIRED_STATUSES:
        errors.append("TASK_QUEUE.yaml statuses must contain exactly todo, in_progress, blocked, done, dropped")

    tasks = task_queue.get("tasks")
    if not isinstance(tasks, list):
        errors.append("TASK_QUEUE.yaml tasks must be a list")
        return errors

    tasks_by_id: dict[str, dict[str, Any]] = {}
    for index, task in enumerate(tasks):
        if not isinstance(task, dict):
            errors.append(f"task at index {index} must be a mapping")
            continue
        missing_keys = sorted(REQUIRED_TASK_KEYS - task.keys())
        if missing_keys:
            errors.append(
                f"task {task.get('id', f'index {index}')!r} is missing required keys: {', '.join(missing_keys)}"
            )
        task_id = task.get("id")
        if not isinstance(task_id, str) or not task_id:
            errors.append(f"task at index {index} must have a non-empty string id")
            continue
        if task_id in tasks_by_id:
            errors.append(f"duplicate task id {task_id!r}")
            continue
        tasks_by_id[task_id] = task

        if not isinstance(task.get("phase"), int):
            errors.append(f"task {task_id!r} phase must be an integer")
        if not isinstance(task.get("priority"), int):
            errors.append(f"task {task_id!r} priority must be an integer")
        if task.get("status") not in REQUIRED_STATUSES:
            errors.append(f"task {task_id!r} has invalid status {task.get('status')!r}")
        if not isinstance(task.get("depends_on"), list) or not all(
            isinstance(dep, str) for dep in task["depends_on"]
        ):
            errors.append(f"task {task_id!r} depends_on must be a list of task ids")
        if not isinstance(task.get("deliverables"), list) or not all(
            isinstance(item, str) for item in task["deliverables"]
        ):
            errors.append(f"task {task_id!r} deliverables must be a list of strings")
        if not isinstance(task.get("verify"), list) or not all(
            isinstance(item, str) for item in task["verify"]
        ):
            errors.append(f"task {task_id!r} verify must be a list of strings")

    if errors:
        return errors

    for task in tasks:
        task_id = task["id"]
        dependencies = task["depends_on"]
        if task_id in dependencies:
            errors.append(f"task {task_id!r} cannot depend on itself")
        for dependency in dependencies:
            if dependency not in tasks_by_id:
                errors.append(f"task {task_id!r} depends on unknown task {dependency!r}")
        if task["status"] == "done":
            incomplete_dependencies = [
                dependency
                for dependency in dependencies
                if tasks_by_id[dependency]["status"] != "done"
            ]
            if incomplete_dependencies:
                errors.append(
                    f"done task {task_id!r} depends on unfinished tasks: {', '.join(incomplete_dependencies)}"
                )

    in_progress_tasks = sorted(
        [task for task in tasks if task["status"] == "in_progress"],
        key=task_sort_key,
    )
    if len(in_progress_tasks) > 1:
        errors.append("TASK_QUEUE.yaml may contain at most one in_progress task")

    blocked_tasks = [task for task in tasks if task["status"] == "blocked"]
    if blocked_tasks and not blockers:
        blocked_ids = ", ".join(task["id"] for task in blocked_tasks)
        errors.append(f"blocked tasks require STATE.yaml blockers: {blocked_ids}")

    current_task_id = state.get("current_task_id")
    if current_task_id is None:
        if in_progress_tasks:
            errors.append(
                "STATE.yaml current_task_id must name the in_progress task when the queue has one"
            )
    else:
        current_task = tasks_by_id.get(current_task_id)
        if current_task is None:
            errors.append(f"STATE.yaml current_task_id {current_task_id!r} is not in TASK_QUEUE.yaml")
        elif current_task["status"] != "in_progress":
            errors.append(
                f"STATE.yaml current_task_id {current_task_id!r} must refer to an in_progress task"
            )
        elif len(in_progress_tasks) == 1 and in_progress_tasks[0]["id"] != current_task_id:
            errors.append("STATE.yaml current_task_id does not match the queue's in_progress task")
        if isinstance(state.get("current_phase"), int) and current_task is not None:
            if state["current_phase"] != current_task["phase"]:
                errors.append("STATE.yaml current_phase must match the in_progress task phase")

    last_completed_task_id = state.get("last_completed_task_id")
    if last_completed_task_id is not None:
        last_completed = tasks_by_id.get(last_completed_task_id)
        if last_completed is None:
            errors.append(
                f"STATE.yaml last_completed_task_id {last_completed_task_id!r} is not in TASK_QUEUE.yaml"
            )
        elif last_completed["status"] != "done":
            errors.append(
                f"STATE.yaml last_completed_task_id {last_completed_task_id!r} must refer to a done task"
            )

    cycle_errors = find_dependency_cycle_errors(tasks_by_id)
    errors.extend(cycle_errors)
    if errors:
        return errors

    if current_task_id is None:
        next_task = select_next_task(task_queue, blockers)
        expected_next_id = None if next_task is None else next_task["id"]
        if state.get("next_task_hint") != expected_next_id:
            errors.append(
                f"STATE.yaml next_task_hint must be {expected_next_id!r} based on queue selection"
            )
        if next_task is not None and state["current_phase"] != next_task["phase"]:
            errors.append("STATE.yaml current_phase must match the next eligible task phase")

    return errors


def find_dependency_cycle_errors(tasks_by_id: dict[str, dict[str, Any]]) -> list[str]:
    errors: list[str] = []
    temporary: set[str] = set()
    permanent: set[str] = set()

    def visit(task_id: str, stack: list[str]) -> None:
        if task_id in permanent or task_id in temporary:
            if task_id in temporary:
                cycle_start = stack.index(task_id)
                cycle = stack[cycle_start:] + [task_id]
                errors.append(f"dependency cycle detected: {' -> '.join(cycle)}")
            return

        temporary.add(task_id)
        stack.append(task_id)
        for dependency in tasks_by_id[task_id]["depends_on"]:
            if dependency in tasks_by_id:
                visit(dependency, stack)
        stack.pop()
        temporary.remove(task_id)
        permanent.add(task_id)

    for task_id in sorted(tasks_by_id):
        visit(task_id, [])

    return errors


def select_next_task(task_queue: dict[str, Any], blockers: list[str]) -> dict[str, Any] | None:
    tasks = task_queue.get("tasks", [])
    if not isinstance(tasks, list):
        return None

    tasks_by_id = {
        task["id"]: task
        for task in tasks
        if isinstance(task, dict) and isinstance(task.get("id"), str)
    }
    eligible: list[dict[str, Any]] = []
    for task in tasks:
        if not isinstance(task, dict):
            continue
        if task.get("status") != "todo":
            continue
        dependencies = task.get("depends_on")
        if not isinstance(dependencies, list):
            continue
        if any(
            dependency not in tasks_by_id or tasks_by_id[dependency].get("status") != "done"
            for dependency in dependencies
        ):
            continue
        if is_explicitly_blocked(task["id"], blockers):
            continue
        eligible.append(task)

    if not eligible:
        return None
    return sorted(eligible, key=task_sort_key)[0]


def parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Validate .agent/STATE.yaml and .agent/TASK_QUEUE.yaml consistency."
    )
    parser.add_argument(
        "--state",
        default=str(DEFAULT_STATE_PATH),
        help="Path to the STATE.yaml file",
    )
    parser.add_argument(
        "--queue",
        default=str(DEFAULT_TASK_QUEUE_PATH),
        help="Path to the TASK_QUEUE.yaml file",
    )
    return parser.parse_args(sys.argv[1:] if argv is None else argv)


def main(argv: list[str] | None = None) -> int:
    args = parse_args(argv)
    try:
        state = load_yaml_subset_file(Path(args.state))
        task_queue = load_yaml_subset_file(Path(args.queue))
        errors = collect_validation_errors(state, task_queue)
    except (OSError, ValueError) as exc:
        print(f"INVALID: {exc}", file=sys.stderr)
        return 1

    if errors:
        print("INVALID: control-plane consistency check failed", file=sys.stderr)
        for error in errors:
            print(f"- {error}", file=sys.stderr)
        return 1

    current_task_id = state.get("current_task_id")
    blockers = state.get("blockers", [])
    selected_next_task = select_next_task(task_queue, blockers)
    next_task = current_task_id or (selected_next_task["id"] if selected_next_task is not None else None)
    print(f"OK: control plane consistent (current_or_next_task={next_task!r})")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
