from __future__ import annotations

import contextlib
import io
import tempfile
import unittest
from pathlib import Path

from tools import agent_queue_check


STATE_TEMPLATE = """\
schema_version: 1
project: satsolver
mode: autonomous_queue
current_phase: {current_phase}
current_task_id: {current_task_id}
last_completed_task_id: cp-002
repo_health: {repo_health}
working_assumptions:
  - Queue control plane is authoritative.
blockers:{blockers}
recent_files:
  - AGENT.md
next_task_hint: {next_task_hint}
notes:
  - seeded for tests
"""

TASK_QUEUE_TEMPLATE = """\
schema_version: 1
selection_policy:
  continue_in_progress_first: true
  pick_status: todo
  dependencies_must_be_done: true
  tie_breaker:
    - priority_desc
    - phase_asc
    - id_asc
statuses:
  - todo
  - in_progress
  - blocked
  - done
  - dropped
tasks:
  - id: cp-001
    phase: 0
    priority: 100
    status: done
    title: Bootstrap
    size: M
    depends_on: []
    goal: bootstrap queue
    deliverables:
      - AGENT.md
    verify:
      - python tools/codex_verify.py
  - id: cp-002
    phase: 0
    priority: 95
    status: done
    title: Sync docs
    size: S
    depends_on:
      - cp-001
    goal: sync queue docs
    deliverables:
      - README.md
    verify:
      - python tools/codex_verify.py
  - id: cp-003
    phase: 0
    priority: 90
    status: {cp_003_status}
    title: Add queue checker
    size: M
    depends_on:
      - cp-001
      - cp-002
    goal: add the queue checker
    deliverables:
      - tools/agent_queue_check.py
    verify:
      - python tools/codex_verify.py
  - id: sat-001
    phase: 1
    priority: 80
    status: todo
    title: Deduplicate shared helpers
    size: M
    depends_on: []
    goal: deduplicate shared helpers
    deliverables:
      - satsolver_common.py
    verify:
      - python tools/codex_verify.py
"""


def render_blockers(blockers: list[str]) -> str:
    if not blockers:
        return " []"
    return "\n" + "\n".join(f"  - {blocker}" for blocker in blockers)


def write_control_plane(
    temp_dir: str,
    *,
    current_phase: int,
    current_task_id: str,
    next_task_hint: str,
    cp_003_status: str,
    blockers: list[str] | None = None,
    repo_health: str = "green_verified",
) -> tuple[Path, Path]:
    state_path = Path(temp_dir) / "STATE.yaml"
    queue_path = Path(temp_dir) / "TASK_QUEUE.yaml"
    rendered_state = STATE_TEMPLATE.format(
        current_phase=current_phase,
        current_task_id=current_task_id,
        next_task_hint=next_task_hint,
        blockers=render_blockers(blockers or []),
        repo_health=repo_health,
    )
    state_path.write_text(rendered_state, encoding="utf-8")
    queue_path.write_text(
        TASK_QUEUE_TEMPLATE.format(cp_003_status=cp_003_status),
        encoding="utf-8",
    )
    return state_path, queue_path


class AgentQueueCheckTests(unittest.TestCase):
    def test_yaml_subset_parser_handles_nested_task_queue(self) -> None:
        parsed = agent_queue_check.parse_yaml_subset(TASK_QUEUE_TEMPLATE.format(cp_003_status="todo"))

        self.assertEqual(1, parsed["schema_version"])
        self.assertEqual(
            ["priority_desc", "phase_asc", "id_asc"],
            parsed["selection_policy"]["tie_breaker"],
        )
        self.assertEqual("cp-003", parsed["tasks"][2]["id"])
        self.assertEqual(["cp-001", "cp-002"], parsed["tasks"][2]["depends_on"])

    def test_collect_validation_errors_accepts_consistent_idle_queue(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            state_path, queue_path = write_control_plane(
                temp_dir,
                current_phase=0,
                current_task_id="null",
                next_task_hint="cp-003",
                cp_003_status="todo",
            )
            state = agent_queue_check.load_yaml_subset_file(state_path)
            task_queue = agent_queue_check.load_yaml_subset_file(queue_path)

        self.assertEqual([], agent_queue_check.collect_validation_errors(state, task_queue))
        self.assertEqual("cp-003", agent_queue_check.select_next_task(task_queue, [])["id"])

    def test_collect_validation_errors_accepts_consistent_in_progress_queue(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            state_path, queue_path = write_control_plane(
                temp_dir,
                current_phase=0,
                current_task_id="cp-003",
                next_task_hint="cp-003",
                cp_003_status="in_progress",
                repo_health="dirty_in_progress",
            )
            state = agent_queue_check.load_yaml_subset_file(state_path)
            task_queue = agent_queue_check.load_yaml_subset_file(queue_path)

        self.assertEqual([], agent_queue_check.collect_validation_errors(state, task_queue))

    def test_collect_validation_errors_rejects_mismatched_current_task(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            state_path, queue_path = write_control_plane(
                temp_dir,
                current_phase=0,
                current_task_id="cp-003",
                next_task_hint="cp-003",
                cp_003_status="todo",
            )
            state = agent_queue_check.load_yaml_subset_file(state_path)
            task_queue = agent_queue_check.load_yaml_subset_file(queue_path)

        errors = agent_queue_check.collect_validation_errors(state, task_queue)

        self.assertTrue(any("current_task_id 'cp-003' must refer to an in_progress task" in error for error in errors))

    def test_collect_validation_errors_rejects_wrong_next_task_hint(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            state_path, queue_path = write_control_plane(
                temp_dir,
                current_phase=0,
                current_task_id="null",
                next_task_hint="sat-001",
                cp_003_status="todo",
            )
            state = agent_queue_check.load_yaml_subset_file(state_path)
            task_queue = agent_queue_check.load_yaml_subset_file(queue_path)

        errors = agent_queue_check.collect_validation_errors(state, task_queue)

        self.assertIn("STATE.yaml next_task_hint must be 'cp-003' based on queue selection", errors)

    def test_main_returns_nonzero_for_invalid_queue(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            state_path, queue_path = write_control_plane(
                temp_dir,
                current_phase=0,
                current_task_id="null",
                next_task_hint="sat-001",
                cp_003_status="todo",
            )

            with contextlib.redirect_stderr(io.StringIO()):
                exit_code = agent_queue_check.main(
                    ["--state", str(state_path), "--queue", str(queue_path)]
                )

        self.assertEqual(1, exit_code)


if __name__ == "__main__":
    unittest.main()
