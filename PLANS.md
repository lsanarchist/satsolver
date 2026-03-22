# PLANS.md

Use this file for queued or multi-step Codex work so the execution state survives beyond a single chat turn.

## How To Use This File

- Add a new section at the top for each queued task.
- Keep one active section at a time.
- Record assumptions, plan steps, commands run, and the final outcome.
- Use short durable notes, not a full transcript.
- When the task is finished, mark the section completed and keep only the verification and conclusion that future runs need.

## Template

## YYYY-MM-DD `<task-slug>`

- Status: active
- Task family:
- Branch/worktree:
- Prompt summary:
- Assumptions:
- Escalations:

### Plan

- [ ] Step 1
- [ ] Step 2
- [ ] Step 3

### Verification

- `command`
- result

### Outcome

- Short summary

### Remaining risks

- Risk or `none`

## 2026-03-22 `perf-033-step3-tail-position-profile`

- Status: completed
- Task family: native-only learnt-large profiling refresh
- Branch/worktree: current checkout
- Prompt summary: continue the next deterministic queue task, `perf-033`, by profiling exact `sub10 step-3` source-pop tail-position behavior on `special/hard.cnf` and `large/test_6.cnf`
- Assumptions:
  - `perf-032` rejected the dense exact-step self-assignment skip as a retained solver keep, so this run should stay measurement-only and explain how often that tail case actually occurs on the dense anchors.
  - The current profiler already identifies exact `sub10 step-3` learnt-large relocations, so the missing last-slot versus overwrite split should be a profiler-only update with no solver-behavior change.
  - A completed measurement-only outcome is valid if it separates exact step-3 last-slot removals from overwrite removals on the dense anchors and leaves the queue with a narrower next experiment.
- Escalations: none

### Plan

- [x] Mark `perf-033` in progress in the control plane and record the active profiling task in `PLANS.md`.
- [x] Add profiler-only exact `sub10 step-3` tail-position counters plus regression coverage, then profile the dense anchors.
- [x] Close the measurement run, queue the next deterministic task, verify the final state, and commit.

### Verification

- `python -m unittest discover -s tests -p 'test_profile_solver.py' -q`
- passed: the profiler test file stayed green at `16/16`, including the new exact `sub10 step-3` tail-position coverage and the stronger invariant that exact `step-3` counts equal `last-slot + overwrite`
- `python tools/profile_solver.py large/test_6.cnf special/hard.cnf`
- passed: exact `sub10 step-3` dense-anchor traffic is dominated by non-last overwrites on both anchors, not by the tail self-assignment case. `large/test_6.cnf` reported `94,161` exact `step-3` hits split into `17,207` last-slot versus `76,954` overwrite, and `special/hard.cnf` reported `109,933` split into `20,980` last-slot versus `88,953` overwrite
- `python tools/agent_queue_check.py`
- passed after the final control-plane sync: the queue now resolves deterministically to `current_or_next_task='perf-034'`
- `python tools/codex_verify.py`
- passed after the final control-plane sync: the repo recompiled, the queue check passed, all `76/76` tests passed, and both default wrapper smoke paths remained green
- `git diff --check`
- passed after the final control-plane sync

### Outcome

- Closed `perf-033` as a measurement-only profiling run with no solver change.
- Added profiler-only exact `sub10 step-3` source-pop tail-position counters in `tools/profile_solver.py`, plus regression coverage in `tests/test_profile_solver.py`, so the repo can now separate last-slot self-assignment removals from non-last overwrite removals on the dense anchors.
- The tail-position question is now answered clearly. Across the two dense anchors together, exact `step-3` hits split `38,187` last-slot versus `165,907` overwrite, so only about `18.7%` of the lane is the self-assignment tail while about `81.3%` is still the non-last overwrite path.
- The queue therefore advances to `perf-034`, which should target the dominant exact `step-3` non-last overwrite path on the dense anchors and keep the newly measured last-slot tail as a guardrail rather than as the primary optimization lane.

### Remaining risks

- The new counters explain which exact `step-3` sublane dominates, but they do not guarantee that a source-pop overwrite rewrite will survive the focused seven-case and supplemental guard slices. The next solver-core task still has to stay narrow and benchmark-driven.

## 2026-03-22 `perf-032-dense-step3-learnt-large-bookkeeping`

- Status: completed
- Task family: native-only learnt-large propagation bookkeeping experiment
- Branch/worktree: current checkout
- Prompt summary: continue the next deterministic queue task, `perf-032`, by testing one bounded dense-UNSAT solver-core change aimed at exact `sub10 step-3` learnt-large bookkeeping on `special/hard.cnf` and `large/test_6.cnf`
- Assumptions:
  - `perf-031` showed that exact `sub10 step-3` traffic is dominated by the dense UNSAT anchors, so this run should optimize that exact anchor lane first rather than reopening the whole focused slice equally.
  - `perf-030` already ruled out the direct watched-slot rewrite across the exact `step-3` aggregate, so this run should choose a different same-search bookkeeping deletion inside the current traversal shape.
  - A retained-noop outcome is valid if any early gate rejects the candidate before the broader repeat-aware exact-CLI suite.
- Escalations: none

### Plan

- [x] Mark `perf-032` in progress in the control plane and record the active bounded experiment in `PLANS.md`.
- [x] Implement and benchmark one exact `sub10 step-3` dense-UNSAT bookkeeping candidate against the anchor pair, focused seven-case slice, and supplemental `satlib_more` guard slice.
- [x] Keep or revert the candidate based on same-day evidence, then sync the control plane, verify, and commit.

### Verification

- `python tools/codex_verify.py`
- passed on the temporary candidate before the performance gates: the repo compiled, the queue check passed, all `75/75` tests passed, and both default wrapper smoke paths remained green
- `python tools/hotspot_compare.py --baseline-cli-script /tmp/perf032_dense_step3_baseline/satsolver.py --candidate-cli-script satsolver.py large/test_6.cnf special/hard.cnf`
- mixed but positive on the dense anchor pair alone: the two-order average improved from `25.1356s` to `24.9710s`, led by consistent `large/test_6.cnf` wins while `special/hard.cnf` split direction and regressed in reverse order
- `python tools/hotspot_compare.py --baseline-cli-script /tmp/perf032_dense_step3_baseline/satsolver.py --candidate-cli-script satsolver.py large/test_6.cnf special/hard.cnf large/test_10.cnf medium/test_4.cnf medium/test_3.cnf satlib_more/uuf150-01.cnf large/test_8.cnf`
- candidate rejected on the focused seven-case gate: the two-order average regressed from `30.1872s` to `30.4647s`, with losses spreading beyond the dense anchor pair into `large/test_10.cnf`, `medium/test_4.cnf`, and smaller tail movement
- `python tools/hotspot_compare.py --baseline-cli-script /tmp/perf032_dense_step3_baseline/satsolver.py --candidate-cli-script satsolver.py satlib_more/uuf125-010.cnf satlib_more/uf125-01.cnf satlib_more/uf125-010.cnf satlib_more/jnh10.cnf satlib_more/jnh1.cnf`
- candidate also rejected on the supplemental slice: the two-order average regressed from `0.3643s` to `0.3799s`, with the clearest damage on the SAT-side `uf*` pair
- `python tools/profile_solver.py large/test_6.cnf special/hard.cnf`
- passed on the temporary candidate and showed unchanged dense hard-case search counters (`72,886/59,201` on `large/test_6.cnf`, `54,245/44,619` on `special/hard.cnf`), so the mixed anchor result looks like same-search bookkeeping rather than heuristic drift
- `python tools/agent_queue_check.py`
- passed after reverting the candidate and syncing the control plane: the queue now resolves deterministically to `current_or_next_task='perf-033'`
- `python tools/codex_verify.py`
- passed after reverting the candidate and syncing the control plane: the repo recompiled, the queue check passed, all `75/75` tests passed, and both default wrapper smoke paths remained green
- `git diff --check`
- passed after the final control-plane sync

### Outcome

- Tested one bounded solver-core candidate by keeping the existing watched-slot swap and destination append, but using the popped last watcher directly on exact `sub10 step-3` learnt-large successes so the source list could skip a redundant self-assignment when the relocating clause was already last.
- Reverted the candidate and kept no solver change because the focused seven-case gate and the supplemental `satlib_more` slice both regressed, even though the dense anchor pair alone improved slightly.
- The durable lesson is that this same-search bookkeeping deletion is still too broad for retention: it helps `large/test_6.cnf`, hurts `special/hard.cnf`, and does not generalize to the rest of the focused or supplemental guard slices. The next sensible step is to measure exact step-3 source-pop tail-position behavior on the dense anchors before trying another solver-core candidate on this lane.

### Remaining risks

- The reject rules out this exact step-3 source-list self-assignment skip, but it does not prove that the dense step-3 lane is exhausted. The next task should restore measurement on tail-position behavior before trying a different bookkeeping idea there.

## 2026-03-22 `perf-031-step3-hotspot-profile-refresh`

- Status: completed
- Task family: native-only learnt-large profiling refresh
- Branch/worktree: current checkout
- Prompt summary: continue the next deterministic queue task, `perf-031`, by profiling exact `sub10 step-3` learnt-large relocation traffic on the focused seven-case hotspot slice after the `perf-030` reject
- Assumptions:
  - `perf-030` ruled out applying the direct watched-slot rewrite across the whole exact `sub10 step-3` aggregate, so this run should restore measurement before any new solver-core candidate.
  - The current profiler already exposes exact `sub10 step-3` counters, so a measurement-only run may not need code changes if the seven-case hotspot profile is already sufficiently explanatory.
  - A completed measurement-only outcome is valid if it names where exact `step-3` traffic is materially present inside the focused hotspot slice and leaves the queue with a narrower next experiment.
- Escalations: none

### Plan

- [x] Mark `perf-031` in progress in the control plane and record the active profiling task in `PLANS.md`.
- [x] Run the focused seven-case hotspot profile and determine how much exact `sub10 step-3` learnt-large traffic each case actually contributes.
- [x] Update the queue with the measured split, verify the final state, and commit.

### Verification

- `python tools/profile_solver.py large/test_6.cnf special/hard.cnf large/test_10.cnf medium/test_4.cnf medium/test_3.cnf satlib_more/uuf150-01.cnf large/test_8.cnf`
- passed: exact `sub10 step-3` learnt-large traffic was material across the whole focused slice, but it concentrated overwhelmingly in the dense UNSAT anchors, with `special/hard.cnf` at `109,933`, `large/test_6.cnf` at `94,161`, and the other five cases at `15,010` or below each
- `python tools/agent_queue_check.py`
- passed after the final control-plane sync: the queue now resolves deterministically to `current_or_next_task='perf-032'`
- `python tools/codex_verify.py`
- passed after the final control-plane sync: the repo recompiled, the queue check passed, all `75/75` tests passed, and both default wrapper smoke paths remained green
- `git diff --check`
- passed after the final control-plane sync

### Outcome

- Closed `perf-031` as a measurement-only profiling run with no solver change.
- The focused seven-case hotspot profile showed that exact `sub10 step-3` learnt-large traffic is not evenly spread across the slice: `special/hard.cnf` plus `large/test_6.cnf` alone contributed `204,094 / 258,637` exact step-3 hits, about `78.9%` of the total.
- The remaining five cases are much smaller tails by volume, though they still matter as guardrails: `medium/test_4.cnf` and `large/test_10.cnf` were each about `5%` of the total, `large/test_8.cnf` was a SAT-side guardrail at `14,675`, and `satlib_more/uuf150-01.cnf` plus `medium/test_3.cnf` were small exact-step tails.
- The queue therefore advances to `perf-032`, a bounded dense-UNSAT solver-core experiment that should target exact `sub10 step-3` learnt-large bookkeeping on `special/hard.cnf` and `large/test_6.cnf` first while keeping the rest of the focused slice and the supplemental `satlib_more` cases as guardrails.

### Remaining risks

- The new profile explains where the exact `step-3` volume lives, but it does not prove which alternative bookkeeping idea will help there. The next task still needs a different solver-core candidate than the already-rejected direct watched-slot rewrite.

## 2026-03-22 `perf-030-sub10-step3-learnt-large-success-path`

- Status: completed
- Task family: native-only learnt-large propagation bookkeeping experiment
- Branch/worktree: current checkout
- Prompt summary: continue the next deterministic queue task, `perf-030`, by testing one bounded solver-core change that only touches exact `sub10 step-3` learnt-large successful relocations on the supplemental learnt-large target trio
- Assumptions:
  - `perf-029` narrowed the surviving exact-step signal to `sub10 step-3`, so this run should avoid reopening the rejected broader `step-3/4` lane from `perf-028`.
  - The smallest plausible candidate is the earlier direct watched-slot rewrite, gated only to learnt clauses whose successful replacement probe is both sub-10 and exact `step-3`.
  - A retained-noop outcome is valid if either early gate rejects the candidate before the broader repeat-aware exact-CLI suite.
- Escalations: none

### Plan

- [x] Mark `perf-030` in progress in the control plane and record the active bounded experiment in `PLANS.md`.
- [x] Implement and benchmark one exact `sub10 step-3` learnt-large successful-probe bookkeeping candidate against the focused seven-case and supplemental `satlib_more` slices.
- [x] Keep or revert the candidate based on same-day evidence, then sync the control plane, verify, and commit.

### Verification

- `python tools/codex_verify.py`
- passed on the temporary candidate before the performance gates: the repo compiled, the queue check passed, all `75/75` tests passed, and both default wrapper smoke paths remained green
- `python tools/hotspot_compare.py --baseline-cli-script /tmp/perf030_step3_baseline/satsolver.py --candidate-cli-script satsolver.py large/test_6.cnf special/hard.cnf large/test_10.cnf medium/test_4.cnf medium/test_3.cnf satlib_more/uuf150-01.cnf large/test_8.cnf`
- candidate rejected on the primary early gate: the seven-case two-order average regressed from `30.5886s` to `31.0224s`, with the largest stable losses on `large/test_6.cnf`, `special/hard.cnf`, and `large/test_10.cnf`
- `python tools/hotspot_compare.py --baseline-cli-script /tmp/perf030_step3_baseline/satsolver.py --candidate-cli-script satsolver.py satlib_more/uuf125-010.cnf satlib_more/uf125-01.cnf satlib_more/uf125-010.cnf satlib_more/jnh10.cnf satlib_more/jnh1.cnf`
- candidate also rejected on the supplemental slice: the two-order average regressed from `0.3734s` to `0.3939s`, with the clearest damage on `satlib_more/uf125-01.cnf` and mixed movement elsewhere
- `python tools/agent_queue_check.py`
- passed after reverting the candidate and syncing the control plane: the queue now resolves deterministically to `current_or_next_task='perf-031'`
- `python tools/codex_verify.py`
- passed after reverting the candidate and syncing the control plane: the repo recompiled, the queue check passed, all `75/75` tests passed, and both default wrapper smoke paths remained green
- `git diff --check`
- passed after the final control-plane sync

### Outcome

- Tested one bounded solver-core candidate by applying the earlier direct watched-slot rewrite only to learnt clauses whose successful large-clause replacement probe was both sub-10 and exact `step-3`.
- Reverted the candidate and kept no solver change because both early gates regressed, so even the exact `step-3` aggregate is still too wide for this rewrite.
- The durable lesson is that the direct watched-slot rewrite should be treated as rejected for the whole exact `sub10 step-3` lane. The next sensible step is to profile exact `step-3` traffic on the focused seven-case hotspot before another solver-core edit, so the next candidate can be chosen from actual hotspot-case evidence rather than from the supplemental trio alone.

### Remaining risks

- The reject rules out this rewrite on the exact `step-3` aggregate, but it does not prove the whole lane is dead for every other bookkeeping idea. The next task should restore focused-hotspot measurement before trying a different solver-core change on this lane.

## 2026-03-22 `perf-029-sub10-step34-exact-step-split`

- Status: completed
- Task family: native-only learnt-large profiling refresh
- Branch/worktree: current checkout
- Prompt summary: continue the next deterministic queue task, `perf-029`, by splitting the surviving `sub10 step-3/4` learnt-large lane into exact `step-3` versus `step-4` counts before another solver-core experiment
- Assumptions:
  - `perf-028` ruled out applying the direct watched-slot rewrite across the whole `sub10 step-3/4` aggregate, so this run should restore measurement before any new solver-core candidate.
  - The current profiler already exposes `learnt_large_success_sub10_step3_4`, which should be refined into exact `step-3` and `step-4` counters without changing solver behavior.
  - A completed measurement-only outcome is valid if it adds the missing exact-step counters, verifies them, and leaves the queue with a narrower next experiment.
- Escalations: none

### Plan

- [x] Mark `perf-029` in progress in the control plane and record the active profiling task in `PLANS.md`.
- [x] Add profiler-only exact `step-3` and `step-4` learnt-large success counters plus regression coverage, then run the supplemental `satlib_more` profile sweep.
- [x] Update the queue with the measured split, verify the final state, and commit.

### Verification

- `python -m unittest discover -s tests -p 'test_profile_solver.py' -q`
- passed: the updated profiler invariants and direct learnt-large success-bucket test stayed green, and the profiler test file still ran `15/15` green
- `python tools/profile_solver.py satlib_more/uuf125-010.cnf satlib_more/uf125-01.cnf satlib_more/uf125-010.cnf satlib_more/jnh10.cnf satlib_more/jnh1.cnf`
- passed: the surviving `sub10 step-3/4` lane split in favor of exact `step-3` on the real target trio, with `uuf125-010` at `1713 vs 843`, `uf125-01` at `12 vs 9`, and `uf125-010` at `126 vs 99` for `step-3` versus `step-4`; `jnh10` stayed balanced at `2 vs 2`, while `jnh1` showed a small `step-4`-only tail at `0 vs 3`
- `python tools/agent_queue_check.py`
- passed after the final control-plane sync: the queue now resolves deterministically to `current_or_next_task='perf-030'`
- `python tools/codex_verify.py`
- passed after the final control-plane sync: the repo recompiled, the queue check passed, all `75/75` tests passed, and both default wrapper smoke paths remained green
- `git diff --check`
- passed after the final control-plane sync

### Outcome

- Closed `perf-029` as a measurement-only profiling run with no solver change.
- Added profiler-only exact-step counters in `tools/profile_solver.py` plus matching regression coverage in `tests/test_profile_solver.py`, so the repo can now separate `sub10 step-3` from `sub10 step-4` learnt-large successes instead of treating all `step-3/4` work as one bucket.
- The queue question is now answered: the surviving exact-step signal is led by `step-3` across `uuf125-010` and the `uf*` pair, while `step-4` remains present mainly as a guardrail tail, especially on `jnh1`.
- The queue therefore advances to `perf-030`, a bounded solver-core experiment that should touch only the exact `sub10 step-3` learnt-large success lane before re-running the usual focused and supplemental gates.

### Remaining risks

- The new counters explain which exact `sub10 step-3/4` sublane is strongest, but they do not guarantee that a `step-3` rewrite will clear the primary seven-case gate. The next task still has to stay narrow and treat `step-4` as a guardrail rather than reopening the whole rejected aggregate.

## 2026-03-22 `perf-028-sub10-step34-learnt-large-success-path`

- Status: completed
- Task family: native-only learnt-large propagation bookkeeping experiment
- Branch/worktree: current checkout
- Prompt summary: continue the next deterministic queue task, `perf-028`, by testing one bounded solver-core change that only touches sub-10-literal step-3/4 learnt-large successful relocations on the supplemental learnt-large target trio
- Assumptions:
  - `perf-027` narrowed the surviving short-deep lane to `sub10 step-3/4`, so this run should avoid reopening the rejected broader `step-3+` lane from `perf-026`.
  - The smallest plausible candidate is the earlier direct watched-slot rewrite, gated only to learnt clauses whose successful replacement probe is both sub-10 and exactly step-3/4.
  - A retained-noop outcome is valid if either early gate rejects the candidate before the broader repeat-aware exact-CLI suite.
- Escalations: none

### Plan

- [x] Mark `perf-028` in progress in the control plane and record the active bounded experiment in `PLANS.md`.
- [x] Implement and benchmark one sub-10 step-3/4 learnt-large successful-probe bookkeeping candidate against the focused seven-case and supplemental `satlib_more` slices.
- [x] Keep or revert the candidate based on same-day evidence, then sync the control plane, verify, and commit.

### Verification

- `python tools/codex_verify.py`
- passed on the temporary candidate before the performance gates: the repo compiled, the queue check passed, all 75 tests passed, and both default wrapper smoke paths remained green
- `python tools/hotspot_compare.py --baseline-cli-script /tmp/perf028_step34_baseline/satsolver.py --candidate-cli-script satsolver.py large/test_6.cnf special/hard.cnf large/test_10.cnf medium/test_4.cnf medium/test_3.cnf satlib_more/uuf150-01.cnf large/test_8.cnf`
- candidate rejected on the primary early gate: the seven-case two-order average regressed from `31.7919s` to `32.8583s`, with the largest stable losses on `special/hard.cnf`, `large/test_6.cnf`, and `medium/test_4.cnf`
- `python tools/hotspot_compare.py --baseline-cli-script /tmp/perf028_step34_baseline/satsolver.py --candidate-cli-script satsolver.py satlib_more/uuf125-010.cnf satlib_more/uf125-01.cnf satlib_more/uf125-010.cnf satlib_more/jnh10.cnf satlib_more/jnh1.cnf`
- mixed but not enough to rescue the keep: the supplemental slice improved only marginally from `0.3771s` to `0.3759s`, with `uuf125-010` slightly positive but `jnh1` still unstable
- `python tools/agent_queue_check.py`
- passed after reverting the candidate and syncing the control plane: the queue now resolves deterministically to `current_or_next_task='perf-029'`
- `python tools/codex_verify.py`
- passed after reverting the candidate and syncing the control plane: the repo recompiled, the queue check passed, all 75 tests passed, and both default wrapper smoke paths remained green
- `git diff --check`
- passed after the final control-plane sync

### Outcome

- Tested one bounded solver-core candidate by applying the earlier direct watched-slot rewrite only to learnt clauses whose successful large-clause replacement probe was both sub-10 and exact `step-3/4`.
- Reverted the candidate and kept no solver change because the primary seven-case gate regressed clearly even after the exact-depth narrowing, while the supplemental target-family slice was only barely positive.
- The durable lesson is that the whole `sub10 step-3/4` aggregate is still too wide for that bookkeeping rewrite. The next sensible step is to restore measurement and split that aggregate one level deeper, `step-3` versus `step-4`, before another solver-core candidate.

### Remaining risks

- The narrow reject rules out only this direct watched-slot rewrite on the aggregate `step-3/4` lane. It does not prove that both exact steps are equally bad, so the next task should restore profiler evidence before trying another solver-core edit.

## 2026-03-22 `perf-027-short-deep-depth-split`

- Status: completed
- Task family: native-only learnt-large profiling refresh
- Branch/worktree: current checkout
- Prompt summary: continue the next deterministic queue task, `perf-027`, by splitting the surviving short-but-deep learnt-large success lane into exact `step-3/4` versus `step-5+` buckets before another solver-core experiment
- Assumptions:
  - `perf-026` already rejected the whole short-but-deep aggregate as too wide, so this run should restore measurement before any further solver-core change.
  - The current profiler exposes `learnt_large_success_sub10_step3_plus`, but not the finer `step-3/4` versus `step-5+` split needed for the next bounded candidate.
  - A completed measurement-only outcome is valid if it adds the missing counters, verifies them, and leaves the queue with a narrower next experiment.
- Escalations: none

### Plan

- [x] Mark `perf-027` in progress in the control plane and record the active profiling task in `PLANS.md`.
- [x] Add profiler-only short-deep depth-split counters and tests, then run the supplemental `satlib_more` profile sweep.
- [x] Update the queue with the measured split, verify the final state, and commit.

### Verification

- `python -m unittest discover -s tests -p 'test_profile_solver.py' -q`
- passed: the updated profiler invariants and direct learnt-large success-bucket test stayed green, and the profiler test file still ran 15/15 green
- `python tools/profile_solver.py satlib_more/uuf125-010.cnf satlib_more/uf125-01.cnf satlib_more/uf125-010.cnf satlib_more/jnh10.cnf satlib_more/jnh1.cnf`
- passed: the surviving short-but-deep lane was dominated by `step-3/4` rather than `step-5+` in every real target case, with `uuf125-010` at `2556 vs 573` (`81.69%` vs `18.31%`), `uf125-01` at `21 vs 10` (`67.74%` vs `32.26%`), and `uf125-010` at `225 vs 79` (`74.01%` vs `25.99%`); `jnh10` and `jnh1` stayed low-volume guardrails and showed no step-5+ learnt-large successes at all
- `python tools/codex_verify.py`
- passed while `perf-027` was active: the repo compiled, the queue check passed, all 75 tests passed, and both default wrapper smoke paths remained green
- `python tools/agent_queue_check.py`
- passed after the final control-plane sync: the queue now resolves deterministically to `current_or_next_task='perf-028'`
- `python tools/codex_verify.py`
- passed after the final control-plane sync: the repo recompiled, the queue check passed, all 75 tests passed, and both default wrapper smoke paths remained green
- `git diff --check`
- passed after the final control-plane sync

### Outcome

- Closed `perf-027` as a measurement-only profiling run with no solver change.
- Added profiler-only short-deep depth-split counters in `tools/profile_solver.py` plus matching regression coverage in `tests/test_profile_solver.py`, so the repo can now separate `sub10 step-3/4` from `sub10 step-5+` learnt-large successes instead of treating all `step-3+` work as one bucket.
- The queue question is now answered: the remaining short-but-deep signal is dominated by `sub10 step-3/4`, while `step-5+` is a smaller tail on the real learnt-large target trio. The problem-large guardrails `jnh10` and `jnh1` still do not justify chasing the `step-5+` tail.
- The queue therefore advances to `perf-028`, a bounded solver-core experiment that should touch only the `sub10 step-3/4` learnt-large success lane before re-running the usual focused and supplemental gates.

### Remaining risks

- The new counters explain which exact short-deep sublane survived `perf-026`, but they do not guarantee that a `step-3/4` rewrite will clear the primary seven-case gate. The next task still has to stay narrow and verify both early gates before earning a full repeat-aware exact-CLI suite run.

## 2026-03-22 `perf-026-short-but-deep-learnt-large-success-path`

- Status: completed
- Task family: native-only learnt-large propagation bookkeeping experiment
- Branch/worktree: current checkout
- Prompt summary: continue the next deterministic queue task, `perf-026`, by testing one bounded solver-core change that only touches sub-10-literal step-3+ learnt-large successful relocations on the supplemental learnt-large target trio
- Assumptions:
  - `perf-025` resolved the surviving non-overlap lane in favor of sub-10 step-3+ learnt-large successes, so this run should stay narrowly focused there instead of reopening long-clause, overlap, or mixed-family rewrites.
  - The smallest plausible candidate is the earlier direct watched-slot rewrite, gated only to learnt clauses whose successful replacement probe is both sub-10 and step-3+.
  - A retained-noop outcome is valid if the focused seven-case or supplemental `satlib_more` gate rejects the candidate before the repeat-aware full-suite run.
- Escalations: none

### Plan

- [x] Mark `perf-026` in progress in the control plane and record the active bounded experiment in `PLANS.md`.
- [x] Implement and benchmark one sub-10 step-3+ learnt-large successful-probe bookkeeping candidate against the focused seven-case and supplemental `satlib_more` slices.
- [x] Keep or revert the candidate based on same-day evidence, then sync the control plane, verify, and commit.

### Verification

- `python tools/codex_verify.py`
- passed on the temporary candidate before the performance gates: the repo compiled, the queue check passed, all 75 tests passed, and both default wrapper smoke paths remained green
- `python tools/hotspot_compare.py --baseline-cli-script /tmp/perf026_shortdeep_baseline/satsolver.py --candidate-cli-script satsolver.py large/test_6.cnf special/hard.cnf large/test_10.cnf medium/test_4.cnf medium/test_3.cnf satlib_more/uuf150-01.cnf large/test_8.cnf`
- mixed but too small to trust by itself: the focused seven-case two-order average improved only marginally from `33.6689s` to `33.5759s`, with `large/test_6.cnf` and `special/hard.cnf` splitting direction across forward and reverse order
- `python tools/hotspot_compare.py --baseline-cli-script /tmp/perf026_shortdeep_baseline/satsolver.py --candidate-cli-script satsolver.py satlib_more/uuf125-010.cnf satlib_more/uf125-01.cnf satlib_more/uf125-010.cnf satlib_more/jnh10.cnf satlib_more/jnh1.cnf`
- candidate rejected on the target-family gate: the supplemental slice regressed from `0.3869s` to `0.4523s`, with the largest stable damage on `satlib_more/jnh10.cnf` and a major forward loss on `satlib_more/uuf125-010.cnf`
- `python tools/codex_verify.py`
- passed after reverting the candidate and syncing the control plane: the repo recompiled, the queue check passed, all 75 tests passed, and both default wrapper smoke paths remained green
- `python tools/agent_queue_check.py`
- passed after the final control-plane sync: the queue now resolves deterministically to `current_or_next_task='perf-027'`
- `git diff --check`
- passed after the final control-plane sync

### Outcome

- Tested one bounded solver-core candidate by applying the earlier direct watched-slot rewrite only to learnt clauses whose successful large-clause replacement probe was both sub-10 and step-3+.
- Rejected the candidate and retained no solver change. The primary seven-case gate moved only slightly in the right direction, which was too small and split by order to justify trust on its own, while the more relevant supplemental target-family gate regressed clearly overall.
- The durable lesson is that the whole short-but-deep aggregate is still too wide. The next sensible step is to reintroduce measurement and split that aggregate by exact depth, step-3/4 versus step-5+, before another solver-core candidate.

### Remaining risks

- The short-but-deep lane is still the best remaining hypothesis from `perf-025`, but this run shows that treating all step-3+ successes as one family is too coarse. The next task should narrow by exact depth before any more solver edits.

## 2026-03-22 `perf-025-non-overlap-learnt-large-success-buckets`

- Status: completed
- Task family: native-only learnt-large profiling refresh
- Branch/worktree: current checkout
- Prompt summary: continue the next deterministic queue task, `perf-025`, by measuring which remaining non-overlap learnt-large successful-probe sublane still matters after the overlap-only rewrite lost both early gates
- Assumptions:
  - `perf-024` already ruled out the true overlap lane, so this run should restore measurement before any further solver-core change.
  - The repo profiler already exposes clause-length and probe-depth marginals, but not the cross-split needed to distinguish long-but-shallow from short-but-deep learnt-large successes.
  - A completed measurement-only outcome is valid if it adds the missing counters, verifies them, and leaves the queue with a narrower next solver experiment.
- Escalations: none

### Plan

- [x] Mark `perf-025` in progress in the control plane and record the active profiling task in `PLANS.md`.
- [x] Add profiler-only counters and tests for the learnt-large non-overlap successful-probe buckets, then run the supplemental `satlib_more` profile sweep.
- [x] Update the queue with the measured winner or retained no-op conclusion, verify the final state, and commit.

### Verification

- `python -m unittest discover -s tests -p 'test_profile_solver.py' -q`
- passed: the new helper boundaries and direct learnt-large relocation bucket test both passed, and the profiler test file now runs 15/15 green
- `python tools/profile_solver.py satlib_more/uuf125-010.cnf satlib_more/uf125-01.cnf satlib_more/uf125-010.cnf satlib_more/jnh10.cnf satlib_more/jnh1.cnf`
- passed: the targeted learnt-large family favored the short-but-deep non-overlap lane in every real target case, with `uuf125-010` at `3129 > 1861`, `uf125-01` at `31 > 17`, and `uf125-010` at `304 > 210` for short-but-deep vs long-but-shallow successful relocations; `jnh10` and `jnh1` stayed low-volume learnt-large guardrails with just `19` and `62` learnt-large relocations total
- `python tools/codex_verify.py`
- passed while `perf-025` was active: the repo compiled, the queue check passed, all 75 tests passed, and both default wrapper smoke paths remained green
- `python tools/agent_queue_check.py`
- passed after the final control-plane sync: the queue now resolves deterministically to `current_or_next_task='perf-026'`
- `python tools/codex_verify.py`
- passed after the final control-plane sync: the repo recompiled, the queue check passed, all 75 tests passed, and both default wrapper smoke paths remained green
- `git diff --check`
- passed after the final control-plane sync

### Outcome

- Closed `perf-025` as a measurement-only profiling run with no solver change.
- Added profiler-only learnt-large success bucket counters and tests in `tools/profile_solver.py` plus `tests/test_profile_solver.py` so the queue can now separate long-but-shallow, overlap, neither, and short-but-deep learnt-large successful relocations instead of inferring them from separate marginals.
- The queue question is now answered: after the overlap-only reject, the surviving non-overlap lane is the short-but-deep sub-10-literal step-3+ family, not the long-but-shallow `len10+` step-1/2 family. The target trio (`uuf125-010`, `uf125-01`, `uf125-010`) all favored short-but-deep, while `jnh10` and `jnh1` remained problem-large guardrails rather than primary learnt-large targets.
- The queue therefore advances to `perf-026`, a bounded solver-core experiment that should touch only the short-but-deep learnt-large success path before re-running the usual focused and supplemental gates.

### Remaining risks

- The new counters explain which non-overlap lane survived `perf-023`, but they do not guarantee that a short-but-deep rewrite will win the primary seven-case gate. The next task still has to stay narrow and revalidate both the focused and supplemental slices before earning a full repeat-aware exact-CLI suite run.

## 2026-03-22 `perf-024-long-and-deep-learnt-large-success-path`

- Status: completed
- Task family: native-only learnt-large propagation bookkeeping experiment
- Branch/worktree: current checkout
- Prompt summary: continue the next deterministic queue task, `perf-024`, by testing one narrower learnt-large successful-probe bookkeeping candidate that only touches the overlapping `len10+` and step-3+ success-path subset on the supplemental `uuf125-010` and `uf*` family
- Assumptions:
  - `perf-023` already showed the learnt-large success-path lane is real, but the broader `len10+ or step-3+` rule was too wide for the dense anchors.
  - The smallest faithful narrowing is to keep the direct watched-slot rewrite only for learnt clauses that satisfy both filters at once: long (`len10+`) and deep (step-3+ successful probe).
  - A retained-noop outcome is valid if the primary seven-case gate still rejects the narrower rule before the repeat-aware full suite.
- Escalations: none

### Plan

- [x] Mark `perf-024` in progress in the control plane and record the active long-and-deep experiment in `PLANS.md`.
- [x] Implement and benchmark one narrowed learnt-large successful-probe bookkeeping candidate against the focused seven-case and supplemental `satlib_more` slices.
- [x] Keep or revert the candidate based on same-day evidence, then sync the control plane, verify, and commit.

### Verification

- `python tools/codex_verify.py`
- passed on the temporary candidate before the performance gates: the candidate compiled, passed the queue check, passed all 73 tests, and stayed checker-valid on both default wrapper smoke paths
- `python tools/hotspot_compare.py --baseline-cli-script /tmp/perf024_longdeep_baseline.vA1sej/satsolver.py --candidate-cli-script satsolver.py large/test_6.cnf special/hard.cnf large/test_10.cnf medium/test_4.cnf medium/test_3.cnf satlib_more/uuf150-01.cnf large/test_8.cnf`
- candidate rejected on the primary early gate: the focused seven-case two-order average regressed from `26.2060s` to `26.2748s`, with the largest stable damage on `special/hard.cnf` and `medium/test_4.cnf`
- `python tools/hotspot_compare.py --baseline-cli-script /tmp/perf024_longdeep_baseline.vA1sej/satsolver.py --candidate-cli-script satsolver.py satlib_more/uuf125-010.cnf satlib_more/uf125-01.cnf satlib_more/uf125-010.cnf satlib_more/jnh10.cnf satlib_more/jnh1.cnf`
- candidate rejected on the supplemental slice too: the two-order average regressed from `0.3201s` to `0.3316s`, including a clear `satlib_more/uuf125-010.cnf` loss in both orders
- `python tools/agent_queue_check.py`
- passed after reverting the candidate and syncing the control plane: the queue now resolves deterministically to `current_or_next_task='perf-025'`
- `python tools/codex_verify.py`
- passed after reverting the candidate and syncing the control plane: the repo compiled, the queue check passed, all 73 tests passed, and both default wrapper smoke paths remained green
- `git diff --check`
- passed after the final control-plane sync

### Outcome

- Tested one narrower learnt-large successful-probe bookkeeping candidate by using the direct watched-slot rewrite only on learnt clauses that were both `len10+` and step-3+ successful probes.
- Rejected the candidate and retained no solver change. Unlike `perf-023`, this overlap-only lane did not even preserve the targeted supplemental win: it regressed both the primary seven-case gate and the supplemental slice, which means the earlier `perf-023` improvement did not come from the true long-and-deep overlap.
- The durable lesson is that the next follow-up should profile the remaining non-overlap learnt-large success buckets before another solver-core edit. The meaningful split is now between long-but-shallow and short-but-deep successes, not between broad vs overlap rewrites.

### Remaining risks

- The learnt-large success-path lane is not dead yet, but it is no longer safe to guess which sub-bucket matters. The next task should reintroduce measurement before another solver-core change so we do not keep oscillating between rejected rewrites.

## 2026-03-22 `perf-023-sat-heavy-learnt-large-success-path`

- Status: completed
- Task family: native-only learnt-large propagation bookkeeping experiment
- Branch/worktree: current checkout
- Prompt summary: continue the next deterministic queue task, `perf-023`, by testing one bounded learnt-large successful-probe bookkeeping candidate on the `uuf125-010` and `uf*` supplemental family while keeping `jnh10` and `jnh1` as problem-large guardrails
- Assumptions:
  - `perf-022` already split the supplemental slice into a real learnt-large family and separate problem-large guardrails, so this run should target the learnt-large family directly instead of another homogeneous slice-wide tweak.
  - The most plausible bounded lane is a selective successful-probe bookkeeping cleanup on deeper learnt-large probes, not another failure-tail branch reorder or a broad relocation rewrite.
  - A retained-noop outcome is valid if the early gates reject the candidate before the repeat-aware full suite.
- Escalations: none

### Plan

- [x] Mark `perf-023` in progress in the control plane and record the active successful-probe experiment in `PLANS.md`.
- [x] Implement and benchmark one narrowly targeted SAT-heavy learnt-large successful-probe bookkeeping candidate against the focused seven-case and supplemental `satlib_more` slices.
- [x] Keep or revert the candidate based on same-day evidence, then sync the control plane, verify, and commit.

### Verification

- `python tools/codex_verify.py`
- passed on the temporary candidate before the performance gates: the candidate compiled, passed the queue check, passed all 73 tests, and stayed checker-valid on both default wrapper smoke paths
- `python tools/hotspot_compare.py --baseline-cli-script /tmp/perf023_deepprobe_baseline.LEc9o4/satsolver.py --candidate-cli-script satsolver.py large/test_6.cnf special/hard.cnf large/test_10.cnf medium/test_4.cnf medium/test_3.cnf satlib_more/uuf150-01.cnf large/test_8.cnf`
- candidate rejected on the primary early gate: the focused seven-case two-order average regressed from `34.9357s` to `35.1656s`, led by stable losses on `large/test_6.cnf`, `medium/test_4.cnf`, and `large/test_8.cnf`
- `python tools/hotspot_compare.py --baseline-cli-script /tmp/perf023_deepprobe_baseline.LEc9o4/satsolver.py --candidate-cli-script satsolver.py satlib_more/uuf125-010.cnf satlib_more/uf125-01.cnf satlib_more/uf125-010.cnf satlib_more/jnh10.cnf satlib_more/jnh1.cnf`
- mixed result: the targeted supplemental slice improved overall from `0.4030s` to `0.3883s`, driven mainly by `satlib_more/uuf125-010.cnf`, but `satlib_more/jnh1.cnf` still regressed in both orders and `satlib_more/uf125-010.cnf` split direction
- `python tools/agent_queue_check.py`
- passed after reverting the candidate and syncing the control plane: the queue now resolves deterministically to `current_or_next_task='perf-024'`
- `python tools/codex_verify.py`
- passed after reverting the candidate and syncing the control plane: the repo compiled, the queue check passed, all 73 tests passed, and both default wrapper smoke paths remained green
- `git diff --check`
- passed after the final control-plane sync

### Outcome

- Tested one bounded learnt-large successful-probe bookkeeping candidate by using the direct watched-slot rewrite only on learnt clauses that were either `len10+` or reached step-3+ successful probes.
- Rejected the candidate and retained no solver change. The rewrite did help the targeted supplemental slice overall, which is good evidence that the learnt-large success-path lane is still live, but it still lost the primary seven-case gate and therefore did not earn the repeat-aware full-suite run.
- The durable lesson is that the broader OR-gated rewrite is still too wide for the dense anchors. The next task should narrow further to the true long-and-deep overlap (`len10+` and step-3+ successful probes) instead of applying the direct rewrite to every long or every deep learnt-large success.

### Remaining risks

- This run preserved forward motion on the learnt-large success-path lane, but it did not prove that the narrower long-and-deep subset will be enough; the next candidate still has to satisfy the primary seven-case gate before it is worth a full-suite keep attempt.

## 2026-03-22 `perf-022-supplemental-learnt-large-profile`

- Status: completed
- Task family: native-only learnt-large profiling refresh
- Branch/worktree: current checkout
- Prompt summary: continue the next deterministic queue task, `perf-022`, by profiling the supplemental `satlib_more` learnt-large guard slice before choosing the next bounded solver-core candidate
- Assumptions:
  - This run is measurement-only unless the queue evidence proves stale enough to require a control-plane correction; no solver-core edit is expected.
  - The most useful output is a direct profile of the supplemental `satlib_more` cases so the next learnt-large candidate targets the case family that actually regressed in `perf-021`.
  - A completed profiling run is valid if it narrows the next task deterministically and leaves the repo and queue synchronized.
- Escalations: none

### Plan

- [x] Mark `perf-022` in progress in the control plane and record the active profiling task in `PLANS.md`.
- [x] Run `tools/profile_solver.py` on the supplemental `satlib_more` guard slice and summarize the dominant learnt-large outcomes, clause-shape buckets, and any meaningful SAT/UNSAT split.
- [x] Update the control plane with the refreshed evidence, verify the final state, and commit.

### Verification

- `python tools/profile_solver.py satlib_more/uuf125-010.cnf satlib_more/jnh10.cnf satlib_more/uf125-01.cnf satlib_more/uf125-010.cnf satlib_more/jnh1.cnf`
- passed: the slice split into two profiler families instead of one shared learnt-large lane. `satlib_more/jnh10.cnf` and `satlib_more/jnh1.cnf` were dominated by problem-large relocation (`81.32%` and `87.22%` problem-large relocation pop share, with only `1.19%` and `3.20%` learnt-large relocation pop share), while `satlib_more/uuf125-010.cnf`, `satlib_more/uf125-01.cnf`, and `satlib_more/uf125-010.cnf` carried the real learnt-large traffic (`24.11%`, `6.33%`, and `17.49%` learnt-large relocation pop share)
- `python tools/codex_verify.py`
- passed while `perf-022` was active: the repo compiled, the queue check passed, all 73 tests passed, and both default wrapper smoke paths remained green
- `python tools/agent_queue_check.py`
- passed after the final control-plane sync: the queue now resolves deterministically to `current_or_next_task='perf-023'`
- `python tools/codex_verify.py`
- passed after the final control-plane sync: the repo compiled, the queue check passed, all 73 tests passed, and both default wrapper smoke paths remained green
- `git diff --check`
- passed after the final control-plane sync

### Outcome

- Closed `perf-022` as a measurement-only profiling run with no solver change.
- The supplemental `satlib_more` guard slice is heterogeneous. The `jnh*` cases are mostly problem-large relocation with step-1/2 successful probes and very little learnt-large pressure, so they should be treated as guardrails rather than as the main learnt-large target family.
- The real supplemental learnt-large cases are `satlib_more/uuf125-010.cnf`, `satlib_more/uf125-01.cnf`, and `satlib_more/uf125-010.cnf`. Among those, the SAT-side `uf*` pair puts much more weight on `len10+` clauses and deeper successful probes than the dense UNSAT anchors: `uf125-01` was `45.05%` `len10+` with `66.29%` of successful probes at step `3+`, and `uf125-010` was `36.10%` `len10+` with `46.01%` of successful probes at step `3+`.
- The queue therefore advances to `perf-023`, a bounded successful-probe bookkeeping task that should target the `uuf125-010` and `uf*` learnt-large family while keeping `jnh10` and `jnh1` as problem-large guardrails.

### Remaining risks

- The supplemental slice is now better understood, but any next solver-core keep still has to satisfy the existing focused seven-case gate and the full repeat-aware exact-CLI suite, not just the reprofiled supplemental cases.

## 2026-03-22 `perf-021-learnt-large-unit-first-tail`

- Status: completed
- Task family: native-only learnt-large propagation experiment
- Branch/worktree: current checkout
- Prompt summary: continue the next deterministic queue task, `perf-021`, by testing one bounded learnt-large large-clause tail candidate against the focused seven-case slice, the supplemental `satlib_more` slice, and the repeat-aware full suite
- Assumptions:
  - The large-clause no-replacement tail is still a valid learnt-large lane because active large-clause traffic is entirely learnt-clause work on the dense anchors, and failed large scans still overwhelmingly end in units rather than conflicts.
  - A branch-order-only large-tail candidate can still be same-search if the dense hard-case decision and conflict counters remain unchanged.
  - A retained-noop outcome is valid if the focused or supplemental guard slices already reject the candidate before the full suite.
- Escalations: none

### Plan

- [x] Mark `perf-021` in progress in the control plane and record the active learnt-large tail experiment in `PLANS.md`.
- [x] Implement and benchmark one bounded learnt-large unit-first tail candidate against the focused seven-case and supplemental `satlib_more` guard slices.
- [x] Keep or revert the candidate based on same-day evidence, then sync the control plane, verify, and commit.

### Verification

- `python tools/codex_verify.py`
- passed on the temporary candidate before the performance gates: the candidate compiled, passed the queue check, passed all 73 tests, and stayed checker-valid on both default wrapper smoke paths
- `python tools/hotspot_compare.py --baseline-cli-script /tmp/perf021_largeunit_baseline.fb3ecr/satsolver.py --candidate-cli-script satsolver.py large/test_6.cnf special/hard.cnf large/test_10.cnf medium/test_4.cnf medium/test_3.cnf satlib_more/uuf150-01.cnf large/test_8.cnf`
- candidate rejected: the focused seven-case two-order average regressed from `27.5844s` to `27.6377s`, with the largest stable damage on forward `large/test_6.cnf` and smaller givebacks on `medium/test_3.cnf` and `satlib_more/uuf150-01.cnf`
- `python tools/hotspot_compare.py --baseline-cli-script /tmp/perf021_largeunit_baseline.fb3ecr/satsolver.py --candidate-cli-script satsolver.py satlib_more/uuf125-010.cnf satlib_more/jnh10.cnf satlib_more/uf125-01.cnf satlib_more/uf125-010.cnf satlib_more/jnh1.cnf`
- candidate rejected again: the supplemental `satlib_more` slice also regressed from `0.3721s` to `0.3774s`, mainly because `uf125-010` and `jnh1` lost more than the UNSAT-side wins recovered
- `python tools/profile_solver.py large/test_6.cnf special/hard.cnf`
- passed: the dense hard-case search counters stayed unchanged at `72,886/59,201` decisions/conflicts on `large/test_6.cnf` and `54,245/44,619` on `special/hard.cnf`, so this still looked like same-search bookkeeping
- `python tools/agent_queue_check.py`
- passed after reverting the candidate and syncing the control plane: the queue now resolves deterministically to `current_or_next_task='perf-022'`
- `python tools/codex_verify.py`
- passed after the final control-plane sync: the repo compiles, the queue check passes, all 73 tests pass, and both default wrapper smoke paths remain green
- `git diff --check`
- passed after the final control-plane sync

### Outcome

- Tested one bounded learnt-large failure-tail candidate by reordering the no-replacement large-clause tail to favor the overwhelmingly common unit-or-satisfied path over the rarer conflict return, mirroring the earlier kept ternary tail style.
- Rejected the candidate and retained no solver change. Even though the dense hard-case decision/conflict counters stayed unchanged, the candidate still regressed both the focused seven-case slice (`27.5844s -> 27.6377s`) and the supplemental `satlib_more` slice (`0.3721s -> 0.3774s`), so it did not earn the full repeat-aware suite.
- The durable lesson is that future learnt-large work should move away from failure-tail branch-order changes and instead profile the supplemental `satlib_more` guard cases directly before picking the next bounded candidate.

### Remaining risks

- The next learnt-large candidate still needs to explain the SAT-heavy supplemental regressions, not just the dense UNSAT anchors, before another solver-core edit is worth attempting.

## 2026-03-22 `perf-020-learnt-large-guard-slice-refresh`

- Status: completed
- Task family: native-only learnt-large benchmark guard refresh
- Branch/worktree: current checkout
- Prompt summary: continue the next deterministic queue task, `perf-020`, by using the `perf-019` broad-suite reject to refresh the exact-CLI guard slice that future learnt-large relocation experiments must satisfy before another solver-core keep attempt
- Assumptions:
  - This run is measurement-only unless the queue evidence itself proves stale; no solver-core edit is expected.
  - The most useful deliverable is a compact supplemental guard slice and a corrected lesson in the queue, not another candidate implementation.
  - If the broad-suite mismatch turns out to come mainly from repeat-aware instability on already-focused cases, the queue should say that explicitly instead of pretending the problem is purely outside the existing hotspot slice.
- Escalations: none

### Plan

- [x] Mark `perf-020` in progress in the control plane and record the active guard-refresh task in `PLANS.md`.
- [x] Reconcile the `perf-019` full-suite regression against the focused seven-case slice, rerun the required measurement commands, and derive the supplemental learnt-large guard cases.
- [x] Update the control plane with the refreshed guard-slice guidance, verify the final state, and commit.

### Verification

- `python - <<'PY'` (parse `/tmp/perf019_baseline_cli_repeat2.txt` vs `/tmp/sat-codex-benchmark-6_2z0guq.txt`)
- passed: the `perf-019` full-suite regression came almost entirely from the existing focused seven-case slice (`+0.4541s`), while all non-focused cases netted to only `-0.0026s`; the largest gross non-focused regressions were `satlib_more/uuf125-010.cnf` (`+0.0325s`), `satlib_more/jnh10.cnf` (`+0.0188s`), `satlib_more/uf125-01.cnf` (`+0.0122s`), `satlib_more/uf125-010.cnf` (`+0.0097s`), and `satlib_more/jnh1.cnf` (`+0.0083s`)
- `python tools/profile_solver.py large/test_6.cnf special/hard.cnf`
- passed: the retained solver still shows unchanged dense hard-case search counters (`72,886/59,201` on `large/test_6.cnf`, `54,245/44,619` on `special/hard.cnf`) and unchanged learnt-large shares (`26.12%` pop share on `large/test_6.cnf`, `38.33%` on `special/hard.cnf`)
- `python tools/codex_verify.py --benchmark-mode cli --repeat 2`
- passed: the retained solver stayed `59/59` correct on a fresh repeat-aware exact-CLI rerun (`30.3111s` representative / `60.6223s` measured); the absolute total drifted noisily relative to the `perf-019` frozen baseline, but the slow-case ordering stayed the same and still centered on the existing focused anchors plus `satlib_more/uuf125-010.cnf`
- `python tools/agent_queue_check.py`
- passed after the control-plane sync: the queue now resolves deterministically to `current_or_next_task='perf-021'`
- `python tools/codex_verify.py`
- passed after the final control-plane sync: the repo compiles, the queue check passes, all 73 tests pass, and both default wrapper smoke paths remain green
- `git diff --check`
- passed after the final control-plane sync

### Outcome

- Closed `perf-020` as a measurement-only guard-refresh run; no solver code changed.
- The key correction is that `perf-019` did not really uncover a wholly different non-hotspot failure family. The broad-suite reject was dominated by repeat-aware reversals inside the existing seven-case slice, especially `special/hard.cnf`, while non-focused cases netted out almost flat.
- Future learnt-large relocation work should therefore keep the existing seven-case slice as the primary early gate, but add one compact supplemental satlib-more guard slice to catch the main secondary gross regressions earlier: `satlib_more/uuf125-010.cnf`, `satlib_more/jnh10.cnf`, `satlib_more/uf125-01.cnf`, `satlib_more/uf125-010.cnf`, and `satlib_more/jnh1.cnf`.
- The queue now advances to `perf-021`, which should test the next bounded learnt-large relocation idea against the focused seven-case slice, the supplemental satlib-more slice, and the full repeat-aware exact-CLI suite before any keep.

### Remaining risks

- The supplemental satlib-more slice is only an early warning for this lane; `python tools/codex_verify.py --benchmark-mode cli --repeat 2` remains the final keep gate because the absolute timings are still noisy.

## 2026-03-22 `perf-019-learnt-large-relocation-bookkeeping`

- Status: completed
- Task family: native-only learnt-large propagation bookkeeping experiment
- Branch/worktree: current checkout
- Prompt summary: continue the next deterministic queue task, `perf-019`, by testing one bounded learnt-large relocation bookkeeping deletion on the refreshed dense-UNSAT hotspot slice after the retained `perf-017` keep and the `perf-018` profile refresh
- Assumptions:
  - `perf-018` already narrowed the next lane to the secondary learnt-large relocation bucket, so this run should stay on that exact surface instead of reopening broader watcher-layout or reduction-policy experiments.
  - The dominant successful learnt-large relocation path is still the step-1/2 probe case, so the best first candidate is a same-search bookkeeping deletion rather than new scan-head branching.
  - A retained-noop outcome is valid if the candidate still loses on the repeat-aware exact-CLI suite even after the focused hotspot and structural gates look positive.
- Escalations: none

### Plan

- [x] Mark `perf-019` in progress in the control plane and record the active learnt-large relocation bookkeeping experiment in `PLANS.md`.
- [x] Implement and evaluate one narrowly scoped learnt-large relocation bookkeeping candidate against the hotspot and structural guardrail slices.
- [x] Keep or revert the candidate based on same-day evidence, then sync the control plane, verify, and commit.

### Verification

- `python tools/codex_verify.py`
- passed on the temporary candidate before the performance gates: the candidate compiled, passed the queue check, passed all 73 tests, and stayed checker-valid on both default wrapper smoke paths
- `python tools/hotspot_compare.py --baseline-cli-script /tmp/perf019_largebook_baseline.9uppKV/satsolver.py --candidate-cli-script satsolver.py large/test_6.cnf special/hard.cnf large/test_10.cnf medium/test_4.cnf medium/test_3.cnf satlib_more/uuf150-01.cnf large/test_8.cnf`
- passed: the focused seven-case two-order exact-CLI hotspot average improved from `26.4626s` to `25.8086s`, led by a solid `large/test_6.cnf` win
- `python tools/hotspot_compare.py --baseline-cli-script /tmp/perf019_largebook_baseline.9uppKV/satsolver.py --candidate-cli-script satsolver.py special/pigeonhole.cnf special/tseitin.cnf`
- passed: the structural fast-exit guardrail also improved overall (`0.0657s -> 0.0564s`)
- `python tools/profile_solver.py large/test_6.cnf special/hard.cnf`
- passed: the dense hard-case search counters stayed unchanged at `72,886/59,201` decisions/conflicts on `large/test_6.cnf` and `54,245/44,619` on `special/hard.cnf`, so the candidate still looked like same-search bookkeeping
- `python benchmark_suite.py satsolver /tmp/perf019_baseline_cli_repeat2.txt small medium large special satlib_subset satlib_more --bruteforce-var-limit 16 --cli-script /tmp/perf019_largebook_baseline.9uppKV/satsolver.py --python-executable /usr/bin/python --repeat 2`
- passed: the frozen same-day baseline stayed `59/59` correct at `28.8865s` representative / `57.7730s` measured
- `python tools/codex_verify.py --benchmark-mode cli --repeat 2`
- passed as a correctness run but rejected as a keep gate: the candidate stayed `59/59` correct yet regressed the repeat-aware exact-CLI suite to `29.3380s` representative / `58.6760s` measured, so the solver change was reverted
- `python tools/agent_queue_check.py`
- passed after reverting the candidate and syncing the control plane: the queue now resolves deterministically to `current_or_next_task='perf-020'`
- `python tools/codex_verify.py`
- passed after reverting the candidate and syncing the control plane: the repo compiles, the queue check passes, all 73 tests pass, and both default wrapper smoke paths remain green
- `git diff --check`
- passed after the final control-plane sync

### Outcome

- Tested one bounded learnt-large relocation bookkeeping deletion by rewriting the successful large-clause relocation swap to use the already-known `candidate_literal` directly, mirroring the earlier retained ternary relocation style.
- Rejected the candidate and retained no solver change. Even though the focused seven-case hotspot and structural guardrail both improved and the dense hard-case search counters stayed unchanged, the stronger repeat-aware 59-case exact-CLI suite regressed from `28.8865s` to `29.3380s`.
- The durable lesson is that the current seven-case slice is not sufficient by itself for learnt-large relocation work. Future experiments on this lane need a refreshed broader exact-CLI guard before another keep attempt.

### Remaining risks

- Focused learnt-large wins can still lose on the broader exact-CLI suite even when dense hard-case counters remain unchanged, so future tasks on this lane should widen their guard slices before retaining solver-core edits.

## 2026-03-22 `perf-018-post-keep-propagation-profile-refresh`

- Status: completed
- Task family: native-only dense-UNSAT propagation profiling refresh
- Branch/worktree: current checkout
- Prompt summary: continue the next deterministic queue task, `perf-018`, by refreshing the dense-UNSAT propagation profile after the retained `perf-017` relocation-bookkeeping keep and use that evidence to choose the next bounded experiment
- Assumptions:
  - `perf-017` changed only hot-path relocation bookkeeping and kept the dense hard-case decision/conflict counters unchanged, so this run should re-measure the retained solver before stacking another propagation edit on top of it.
  - The right deliverable for this run is refreshed propagation evidence plus a narrower next task, not another speculative patch bundled into the same turn.
  - A measurement-only outcome is valid as long as the repo state, plan log, and queue all move forward deterministically.
- Escalations: none

### Plan

- [x] Mark `perf-018` in progress in the control plane and record the active profiling task in `PLANS.md`.
- [x] Run the required dense-UNSAT profiling commands on the retained solver and summarize the new dominant propagation surfaces after `perf-017`.
- [x] Update the control plane with the refreshed profiling evidence, queue the next bounded experiment, verify the final state, and commit.

### Verification

- `python -m cProfile -s tottime satsolver.py large/test_6.cnf /tmp/perf018_profile_large6.txt | head -n 45`
- passed: the retained post-`perf-017` solver still ranks `propagate()` first by a wide margin (`17.087s` on this run), with `analyze()` (`2.799s`) and `_minimize_learnt_and_prepare()` (`1.160s`) still secondary and list churn (`append` `2.492s`, `pop` `1.428s`) still concentrated in the same propagation-heavy path; the absolute times are noisier than the repeat-aware exact-CLI suite, but the hotspot ordering is unchanged
- `python tools/profile_solver.py large/test_6.cnf special/hard.cnf`
- passed: the retained solver still shows unchanged dense hard-case search counters (`72,886/59,201` on `large/test_6.cnf`, `54,245/44,619` on `special/hard.cnf`), unchanged original problem-ternary shares (`61.01%` relocation / `38.31%` unit / `0.68%` conflict, `53.91%` / `45.21%` / `0.88%`), and the same watcher-pop split where original problem-ternary relocation remains primary while learnt-large relocation is still the next secondary bucket (`26.12%` on `large/test_6.cnf`, `38.33%` on `special/hard.cnf`)
- `python tools/codex_verify.py`
- passed: the measurement-only control-plane updates compile, pass the queue check, pass all 73 tests, and clear both default wrapper smoke paths

### Outcome

- Refreshed the dense-UNSAT propagation profile on the retained post-`perf-017` solver and used it to choose the next bounded experiment from current repo evidence instead of intuition.
- The `perf-017` keep did what it was supposed to do: the dense hard-case decision/conflict counters stayed unchanged, `propagate()` is still the dominant runtime center, and original problem-ternary relocation remains the largest remaining surface within the non-satisfied original-ternary path. But the next distinct secondary watcher-churn bucket is now also clearer: learnt-large relocation still accounts for a meaningful share of pops on both dense anchors, especially `special/hard.cnf`.
- The queue therefore advances to `perf-019`, a bounded propagation task that should test one concrete learnt-large relocation bookkeeping deletion on the dominant step-1/2 successful probe path without reopening the already-rejected scan-head unroll, reduction-policy, physical split-list, or extra side-state lanes.

### Remaining risks

- The profiling commands are useful for surface ranking and counter stability, but their absolute runtimes are noisier than the repeat-aware exact-CLI suite, so future keep/reject decisions still need the normal exact-CLI gates.
- Original problem-ternary relocation is still the single biggest bucket, so `perf-019` should only move to learnt-large relocation because the recent original-ternary lane has already yielded both keeps and strong local boundaries, not because that primary bucket is “solved.”

## 2026-03-22 `perf-017-problem-ternary-relocation-bookkeeping`

- Status: completed
- Task family: native-only dense-UNSAT propagation experiment
- Branch/worktree: current checkout
- Prompt summary: continue the next deterministic queue task, `perf-017`, by testing one bounded original problem-ternary relocation bookkeeping change after the retained `perf-016` same-search branch-shape reject
- Assumptions:
  - `perf-016` preserved dense hard-case decisions and conflicts, so the next relocation candidate should only be considered if it deletes concrete hot-path bookkeeping rather than just changing candidate-state branch structure.
  - Previously rejected lazy normalization, watcher-pop rewrites, watch-position side arrays, family hoists, true-candidate hold behavior, and physical split lists still rule out broader traversal-layout changes here.
  - A retained-noop outcome is valid if the narrower bookkeeping deletion still loses on the same-day exact-CLI hotspot gate.
- Escalations: none

### Plan

- [x] Mark `perf-017` in progress in the control plane and record the active relocation bookkeeping experiment in `PLANS.md`.
- [x] Implement and evaluate one narrowly scoped original problem-ternary relocation bookkeeping candidate against the hotspot and structural guardrail slices.
- [x] Keep or revert the candidate based on same-day evidence, then sync the control plane, verify, and commit.

### Verification

- `python -m cProfile -s tottime satsolver.py large/test_6.cnf /tmp/perf017_profile_large6.txt | head -n 45`
- passed on the retained baseline before editing: `large/test_6.cnf` still ranked `propagate()` first (`13.621s`) with list churn (`append` `2.059s`, `pop` `1.218s`) concentrated in the same propagation-heavy path that `perf-017` is targeting
- `python tools/codex_verify.py`
- passed on the temporary candidate before the performance gates: the relocation-bookkeeping candidate compiled, passed the queue check, passed all 73 tests, and stayed checker-valid on both default wrapper smoke paths
- `python tools/hotspot_compare.py --baseline-cli-script /tmp/perf017_relocbook_baseline.gYxgu4/satsolver.py --candidate-cli-script satsolver.py large/test_6.cnf special/hard.cnf large/test_10.cnf medium/test_4.cnf medium/test_3.cnf satlib_more/uuf150-01.cnf large/test_8.cnf`
- passed: the refreshed seven-case two-order exact-CLI hotspot average improved from `28.4207s` to `27.8720s`; both dense anchors improved overall, the main giveback was only forward `large/test_8.cnf`, and the total win was large enough to justify the broader suite
- `python tools/hotspot_compare.py --baseline-cli-script /tmp/perf017_relocbook_baseline.gYxgu4/satsolver.py --candidate-cli-script satsolver.py special/pigeonhole.cnf special/tseitin.cnf`
- passed: the structural fast-exit guardrail also improved overall (`0.0810s -> 0.0639s`)
- `python benchmark_suite.py satsolver /tmp/perf017_baseline_cli_repeat2.txt small medium large special satlib_subset satlib_more --bruteforce-var-limit 16 --cli-script /tmp/perf017_relocbook_baseline.gYxgu4/satsolver.py --python-executable /usr/bin/python --repeat 2`
- passed: the frozen same-day baseline stayed `59/59` correct at `31.5160s` representative / `63.0320s` measured
- `python tools/codex_verify.py --benchmark-mode cli --repeat 2`
- passed: the retained candidate stayed `59/59` correct and improved the repeat-aware exact-CLI 59-case suite to `29.7607s` representative / `59.5215s` measured
- `python tools/profile_solver.py large/test_6.cnf special/hard.cnf`
- passed: the dense hard-case search counters stayed unchanged at `72,886/59,201` decisions/conflicts on `large/test_6.cnf` and `54,245/44,619` on `special/hard.cnf`, which supports treating this as a same-search propagation bookkeeping win

### Outcome

- Kept one narrowly scoped original problem-ternary relocation bookkeeping change: ternary relocation now uses the already-known `candidate_literal` directly when rewriting the watched slot and selecting the destination watch list, instead of re-reading the swapped slot after the write.
- The keep is strong enough to retain. The refreshed seven-case exact-CLI hotspot improved from `28.4207s` to `27.8720s`, the structural fast-exit guardrail improved from `0.0810s` to `0.0639s`, and the same-day repeat-aware exact-CLI 59-case suite improved from `31.5160s` to `29.7607s`, all still `59/59` correct.
- The profiler made the keep safer: the dense hard-case decision and conflict counts stayed unchanged on both `large/test_6.cnf` and `special/hard.cnf`, so this looks like deleted original-ternary relocation bookkeeping rather than a heuristic shift.
- Completed `perf-017` as a kept propagation change, updated the durable benchmark narrative, and advanced the queue to `perf-018`, which should refresh the dense-UNSAT propagation profile after this keep before choosing the next bounded experiment.

### Remaining risks

- The keep is broader than the recent micro-wins, but `propagate()` is still the dominant runtime center, so the next run should re-profile before stacking another relocation or unit-path change on top of it.
- `large/test_8.cnf` still split direction on the focused hotspot gate, so future propagation work should keep that SAT-like case as an explicit guardrail even when the broad suite is positive.

## 2026-03-22 `perf-016-problem-ternary-relocation-path`

- Status: completed
- Task family: native-only dense-UNSAT propagation experiment
- Branch/worktree: current checkout
- Prompt summary: continue the next deterministic queue task, `perf-016`, by testing one bounded same-search propagation change on the dominant original problem-ternary relocation path after the retained `perf-014` unit-first keep and the `perf-015` profile refresh
- Assumptions:
  - `perf-015` confirmed that the bigger remaining propagation surface is still original problem-ternary relocation, especially the ordinary `candidate=UNASSIGNED` plus `other=UNASSIGNED` case, not the already-improved unit tail.
  - Previously rejected family hoists, watched-position side arrays, lazy normalization, true-candidate hold behavior, and physical watch-list splits still rule out broader layout changes here, so this run should stay inside the current watch traversal shape.
  - A retained-noop outcome is valid if the bounded relocation-path branch shaping still loses on the same-day exact-CLI hotspot gate.
- Escalations: none

### Plan

- [x] Mark `perf-016` in progress in the control plane and record the active relocation experiment in `PLANS.md`.
- [x] Implement and evaluate one narrowly scoped original problem-ternary relocation candidate against the hotspot and structural guardrail slices.
- [x] Keep or revert the candidate based on same-day evidence, then sync the control plane, verify, and commit.

### Verification

- `python tools/codex_verify.py`
- passed on the temporary candidate before the performance gates: the branch-shaped relocation candidate compiled, passed the queue check, passed all 73 tests, and stayed checker-valid on both default wrapper smoke paths
- `python tools/hotspot_compare.py --baseline-cli-script /tmp/perf016_relocsplit_baseline.wgX5tL/satsolver.py --candidate-cli-script satsolver.py large/test_6.cnf special/hard.cnf large/test_10.cnf medium/test_4.cnf medium/test_3.cnf satlib_more/uuf150-01.cnf large/test_8.cnf`
- candidate rejected: the seven-case two-order exact-CLI hotspot average regressed from `28.2700s` to `29.2099s`; `large/test_6.cnf` lost in both orders, `special/hard.cnf` split directions, and the overall result was not close enough to justify broader retention work
- `python tools/hotspot_compare.py --baseline-cli-script /tmp/perf016_relocsplit_baseline.wgX5tL/satsolver.py --candidate-cli-script satsolver.py special/pigeonhole.cnf special/tseitin.cnf`
- passed: the structural fast-exit guardrail stayed slightly positive overall (`0.0652s -> 0.0645s`), so the loss is not coming from those families
- `python tools/profile_solver.py large/test_6.cnf special/hard.cnf`
- passed on the temporary candidate: the dense hard-case search counters stayed unchanged at `72,886/59,201` decisions/conflicts on `large/test_6.cnf` and `54,245/44,619` on `special/hard.cnf`, which points to pure branch-overhead loss rather than a beneficial search-path change

### Outcome

- Tested one bounded original problem-ternary relocation candidate that split the dominant `candidate=UNASSIGNED` relocation path away from the rarer `candidate=TRUE` relocation path while preserving the current watch layout and the `candidate=FALSE` unit-first tail from `perf-014`.
- Rejected the candidate and retained no solver code change. The real gate regressed clearly on the seven-case exact-CLI slice, and the profiler showed unchanged dense hard-case decisions and conflicts, so the branch split deleted no search work and only added cost on the retained baseline path.
- Completed `perf-016` as a retained no-op, updated the durable queue state, and advanced the next task to `perf-017`, which should target concrete relocation bookkeeping removal on the dominant `candidate=UNASSIGNED` path instead of more candidate-state branch shaping.

### Remaining risks

- The relocation surface is still the right lane, but `perf-016` shows that simply teasing apart `UNASSIGNED` versus `TRUE` relocation branches is negative when it does not also remove real bookkeeping work.
- The next experiment still needs full hotspot and structural guardrail coverage because even apparently same-search propagation micro-changes can move by nearly a second on the seven-case slice.

## 2026-03-22 `perf-015-post-keep-propagation-profile-refresh`

- Status: completed
- Task family: native-only dense-UNSAT propagation profiling refresh
- Branch/worktree: current checkout
- Prompt summary: continue the next deterministic queue task, `perf-015`, by refreshing the dense-UNSAT propagation profile after the retained `perf-014` unit-first ternary-tail keep and use that evidence to choose the next bounded experiment
- Assumptions:
  - `perf-014` changed only a narrow ternary `candidate=FALSE` tail and kept the dense hard-case decision/conflict counters unchanged, so this run should re-measure the retained solver before stacking another propagation change on top.
  - The right deliverable for this run is refreshed propagation evidence plus a narrower next task, not another speculative patch bundled into the same turn.
  - A measurement-only outcome is valid as long as the repo state, plan log, and queue all move forward deterministically.
- Escalations: none

### Plan

- [x] Mark `perf-015` in progress in the control plane and record the active profiling task in `PLANS.md`.
- [x] Run the required dense-UNSAT profiling commands on the retained solver and summarize the new dominant propagation surfaces.
- [x] Update the control plane with the refreshed profiling evidence, queue the next bounded experiment, verify the final state, and commit.

### Verification

- `python -m cProfile -s tottime satsolver.py large/test_6.cnf /tmp/perf015_profile_large6.txt | head -n 45`
- passed: after the `perf-014` keep, the retained `large/test_6.cnf` profile still ranks `propagate()` first (`16.142s`), then `analyze()` (`2.665s`), then `_minimize_learnt_and_prepare()` (`1.109s`); list churn is still concentrated in the propagation-heavy path (`append` `2.357s`, `pop` `1.345s`) rather than in a newly dominant side path
- `python tools/profile_solver.py large/test_6.cnf special/hard.cnf`
- passed: the retained solver still shows original problem-ternary relocation as the larger remaining non-satisfied path on both dense hotspots (`61.01%` relocation / `38.31%` unit / `0.68%` conflict on `large/test_6.cnf`, `53.91%` / `45.21%` / `0.88%` on `special/hard.cnf`), with the bulk of relocation still on the ordinary `candidate=UNASSIGNED` plus `other=UNASSIGNED` path and the dense hard-case decisions/conflicts still unchanged at `72,886/59,201` and `54,245/44,619`
- `python tools/codex_verify.py`
- passed: the measurement-only control-plane updates compile, pass the queue check, pass all 73 tests, and clear both default wrapper smoke paths

### Outcome

- Refreshed the dense-UNSAT propagation profile on the retained post-`perf-014` solver and used it to reset the next optimization target from repo evidence instead of intuition.
- The `perf-014` unit-first keep did what it was supposed to do: the dense hard-case search counters stayed unchanged and `propagate()` dropped materially in `cProfile`, but the bigger balance is now even clearer. `propagate()` is still the dominant end-to-end cost by a wide margin, and within the original problem-ternary non-satisfied path the larger remaining surface is still relocation, not units or conflicts.
- The profiler also narrows the next lane cleanly: the dominant relocation path is still the ordinary `candidate=UNASSIGNED` plus `other=UNASSIGNED` case, while true-candidate relocation, rescue-tail `other=FALSE` cases, family hoists, watched-position side arrays, lazy normalization, and physical watch-list splits are already rejected. The queue therefore advances to `perf-016`, a bounded same-search propagation task that should target original problem-ternary relocation on the current watch traversal shape without reopening those dead ends.

### Remaining risks

- The refreshed evidence still points to propagation, but earlier broad problem-ternary rewrites and watch-layout changes were unstable, so the next task still needs to stay narrowly scoped and benchmark-gated.
- This measurement run did not itself change solver code, so the retained repeat-aware exact-CLI baseline remains `31.8378s` until `perf-016` proves another concrete improvement.

## 2026-03-22 `perf-014-problem-ternary-unit-first`

- Status: completed
- Task family: native-only dense-UNSAT propagation experiment
- Branch/worktree: current checkout
- Prompt summary: continue the next deterministic queue task, `perf-014`, by testing one bounded propagation change on the original problem-ternary relocation or unit path using the refreshed post-`perf-012`/`perf-013` profiler evidence
- Assumptions:
  - `perf-013` confirmed that `propagate()` is still the dominant cost and that original problem-ternary relocation plus unit handling remains the largest concentrated surface on `large/test_6.cnf` and `special/hard.cnf`.
  - Previous family hoists, physical watch splits, true-candidate hold behavior, and extra watched-position side-state have already failed, so this run should stay inside the current watch traversal shape.
  - Within the `candidate_value == FALSE` original-ternary tail, units dominate conflicts heavily on the dense hotspots, so making the unit path the direct fallthrough is a bounded same-search candidate worth testing before another broader propagation rewrite.
- Escalations: none

### Plan

- [x] Mark `perf-014` in progress in the control plane and record the active propagation experiment in `PLANS.md`.
- [x] Implement one narrowly scoped original problem-ternary propagation candidate and evaluate it on the hotspot and structural guardrail slices.
- [x] Keep or revert the candidate based on same-day evidence, then sync the control plane, verify, and commit.

### Verification

- `python tools/codex_verify.py`
- passed on the temporary candidate before the performance gates: the patched solver compiled, passed all 73 tests, and stayed checker-valid on both default wrapper smoke paths
- `python tools/hotspot_compare.py --baseline-cli-script /tmp/perf014_unitfirst_baseline/satsolver.py --candidate-cli-script satsolver.py large/test_6.cnf special/hard.cnf large/test_10.cnf medium/test_4.cnf medium/test_3.cnf satlib_more/uuf150-01.cnf large/test_8.cnf`
- passed: the seven-case two-order exact-CLI hotspot average improved from `29.5292s` to `28.8116s`; the candidate won both directions overall, helped `large/test_6.cnf`, `special/hard.cnf`, `medium/test_3.cnf`, and `large/test_8.cnf` in both orders, and only gave back a small amount on `medium/test_4.cnf` forward plus `large/test_10.cnf` reverse
- `python tools/hotspot_compare.py --baseline-cli-script /tmp/perf014_unitfirst_baseline/satsolver.py --candidate-cli-script satsolver.py special/pigeonhole.cnf special/tseitin.cnf`
- passed: the structural fast-exit guardrail stayed slightly positive overall (`0.0671s -> 0.0658s`) even though `special/tseitin.cnf` individually regressed while `special/pigeonhole.cnf` improved more strongly
- `python tools/codex_verify.py --benchmark-mode cli --repeat 2`
- passed: the retained candidate stayed `59/59` correct and produced a fresh repeat-aware exact-CLI 59-case total of `31.8378s` representative / `63.6755s` measured
- `python benchmark_suite.py satsolver /tmp/perf014_baseline_cli_repeat2.txt small medium large special satlib_subset satlib_more --bruteforce-var-limit 16 --cli-script /tmp/perf014_unitfirst_baseline/satsolver.py --python-executable /usr/bin/python --repeat 2`
- passed: the frozen same-day baseline stayed `59/59` correct at `32.5124s` representative / `65.0247s` measured, so the retained candidate improved the broad exact-CLI suite by `0.6746s`
- `python tools/profile_solver.py large/test_6.cnf special/hard.cnf`
- passed: the retained candidate kept the dense hard-case search counters unchanged at `72,886` decisions / `59,201` conflicts on `large/test_6.cnf` and `54,245` decisions / `44,619` conflicts on `special/hard.cnf`, while the original problem-ternary relocation-plus-unit profile shape remained dominant

### Outcome

- Kept one narrowly scoped same-search propagation change in `satsolver_core.py`: after a ternary clause already knows its candidate literal is `FALSE`, `propagate()` now takes the overwhelmingly common unit path directly and leaves the rare conflict return as the final fallthrough instead of checking the conflict tail first.
- The win is broad enough to retain. The refreshed seven-case exact-CLI hotspot improved from `29.5292s` to `28.8116s`, the structural fast-exit guardrail stayed slightly positive (`0.0671s -> 0.0658s`), and the same-day repeat-aware exact-CLI 59-case suite improved from `32.5124s` to `31.8378s`, all still `59/59` correct.
- The profiler made the keep much safer: the dense hard-case decision and conflict counts stayed unchanged on both `large/test_6.cnf` and `special/hard.cnf`, so this looks like a genuine same-search propagation bookkeeping win rather than another heuristic drift.
- Completed `perf-014` as a kept propagation change, mirrored the retained branch order in `tools/profile_solver.py`, updated the durable benchmark narrative, and advanced the queue to `perf-015`, which should refresh the dense-UNSAT propagation profile after this keep before choosing the next bounded relocation-focused experiment.

### Remaining risks

- The keep is real but still modest, so nearby propagation micro-changes should continue to require the full same-day baseline-vs-candidate exact-CLI suite instead of trusting the hotspot slice alone.
- This change only shortens the candidate-false ternary tail; the larger original problem-ternary relocation path is still the dominant remaining propagation surface and needs fresh post-keep profiling before another experiment.

## 2026-03-22 `perf-013-post-keep-conflict-profile-refresh`

- Status: completed
- Task family: native-only dense-UNSAT profiling refresh
- Branch/worktree: current checkout
- Prompt summary: continue the next deterministic queue task, `perf-013`, by refreshing the dense-UNSAT conflict-analysis profile after the retained `perf-012` metadata-boundary keep and use that evidence to choose the next bounded experiment
- Assumptions:
  - `perf-012` changed the analyze-to-finalization boundary but kept dense hard-case decisions and conflicts unchanged, so this run should re-measure the retained solver before stacking another solver-core change.
  - The right deliverable for this run is profiling evidence plus a narrower next task, not another speculative patch bundled into the same turn.
  - A measurement-only outcome is valid as long as the repo state, plan log, and queue all move forward deterministically.
- Escalations: none

### Plan

- [x] Mark `perf-013` in progress in the control plane and record the active profiling task in `PLANS.md`.
- [x] Run the required dense-UNSAT profiling commands on the retained solver and summarize the new dominant surfaces.
- [x] Update the control plane with the refreshed profiling evidence, queue the next bounded experiment, verify the final state, and commit.

### Verification

- `python -m cProfile -s tottime satsolver.py large/test_6.cnf /tmp/perf013_profile_large6.txt | head -n 45`
- passed: after the `perf-012` keep, the retained large/test_6 profile still ranks `propagate()` first (`18.759s`), then `analyze()` (`2.992s`), then `_minimize_learnt_and_prepare()` (`1.247s`); list churn (`append` `2.615s`, `pop` `1.465s`) remains concentrated in the propagation-heavy path rather than in another standalone finalization pass
- `python tools/profile_solver.py large/test_6.cnf special/hard.cnf`
- passed: the retained solver still shows overwhelmingly original-clause ternary reason traffic inside conflict analysis (`analyze_reason_3=930,068 / 1,057,846` on `large/test_6.cnf`, `657,031 / 770,039` on `special/hard.cnf`), but the much larger runtime center is still propagation-side original-ternary relocation plus units (`61.01%`/`38.31%` of problem-ternary outcomes on `large/test_6.cnf`, `53.91%`/`45.21%` on `special/hard.cnf`) with mixed problem-ternary watch batches still high (`0.6193`, `0.7078`)
- `python tools/codex_verify.py`
- passed: the measurement-only control-plane updates compile, pass the queue check, pass all 73 tests, and clear both default wrapper smoke paths

### Outcome

- Refreshed the dense-UNSAT profile on the retained post-`perf-012` solver and used it to reset the next optimization target from repo evidence instead of intuition.
- The merged conflict-analysis boundary keep did what it was supposed to do: there is no longer a separate `prepare_learnt_clause()` hotspot, and the remaining conflict-analysis cost is concentrated in `analyze()` plus `_minimize_learnt_and_prepare()`. But the larger balance is now even clearer: `propagate()` is still the dominant end-to-end cost by a wide margin, and the main concentrated propagation work remains original problem-ternary relocation plus unit handling rather than rare conflict tails or deleted-watch cleanup.
- Because previous narrow ternary `analyze()` unrolls, `prepare_learnt_clause()` rewrites, family flags, watcher splits, and side-state schemes have already failed, the queue now advances to `perf-014`, a bounded propagation task that targets original problem-ternary relocation or unit work without reviving the already-rejected watcher-family-order or extra side-state lanes.

### Remaining risks

- The refreshed evidence points back to propagation, but earlier broad problem-ternary rewrites and physical family splits were unstable, so the next task still needs to stay narrowly scoped and benchmark-gated.
- This measurement run did not itself change solver code, so the retained baseline remains `31.9532s` until `perf-014` proves another concrete improvement.

## 2026-03-22 `perf-012-post-minimization-learnt-metadata`

- Status: completed
- Task family: native-only dense-UNSAT learnt-metadata bookkeeping experiment
- Branch/worktree: current checkout
- Prompt summary: continue the next deterministic queue task, `perf-012`, by testing one bounded same-clause-content bookkeeping change at the post-minimization analyze-to-finalization boundary on the dense UNSAT hotspot slice
- Assumptions:
  - `perf-011` closed the pure `prepare_learnt_clause()` loop-shape lane for now, so this run should carry metadata across the boundary rather than trying another isolated final-pass rewrite.
  - The retained baseline profile still shows both `minimize_learnt()` and `prepare_learnt_clause()` as visible conflict-analysis costs on `large/test_6.cnf`, which makes a pass-elimination candidate more plausible than another primitive substitution.
  - A retained-noop outcome is acceptable if folding learnt metadata into the minimization compaction still loses on the seven-case exact-CLI gate.
- Escalations: none

### Plan

- [x] Mark `perf-012` in progress in the control plane and record the active experiment in `PLANS.md` before editing.
- [x] Test one bounded same-content candidate that computes post-minimization backtrack and LBD metadata during compaction instead of in a separate final pass.
- [x] Run the default verifier plus the seven-case hotspot gate, then keep or revert the candidate based on same-day evidence.
- [x] Update the control plane with the verified outcome and queue the next sensible follow-up.

### Verification

- `python -m cProfile -s tottime satsolver.py large/test_6.cnf /tmp/perf012_profile_large6.txt | head -n 50`
- passed: the retained baseline still showed `analyze()` (`2.206s`), `minimize_learnt()` (`0.674s`), and `prepare_learnt_clause()` (`0.246s`) as the current post-minimization bookkeeping surface on `large/test_6.cnf`
- `python tools/codex_verify.py`
- passed on the temporary candidate before the performance gates
- `python tools/hotspot_compare.py --baseline-cli-script /tmp/perf012_metadata_baseline/satsolver.py --candidate-cli-script satsolver.py large/test_6.cnf special/hard.cnf large/test_10.cnf medium/test_4.cnf medium/test_3.cnf satlib_more/uuf150-01.cnf large/test_8.cnf`
- passed: the seven-case two-order average improved from `30.2756s` to `29.8805s`; the main gain was forward `large/test_6.cnf` (`17.1869s -> 15.0066s`), while reverse `large/test_6.cnf` still regressed and kept this branch in the “promising but needs broader validation” bucket
- `python tools/hotspot_compare.py --baseline-cli-script /tmp/perf012_metadata_baseline/satsolver.py --candidate-cli-script satsolver.py special/pigeonhole.cnf special/tseitin.cnf`
- passed: the structural fast-exit guardrail stayed healthy and improved slightly overall (`0.0748s -> 0.0725s`)
- `python tools/codex_verify.py --benchmark-mode cli --repeat 2`
- passed: the repeat-aware exact-CLI 59-case suite stayed `59/59` correct and improved the retained same-day representative total from `32.2896s` to `31.9532s` (`64.5793s -> 63.9064s` measured)
- `python tools/profile_solver.py large/test_6.cnf special/hard.cnf`
- passed: the dense hard-case search counters stayed unchanged at `72,886` decisions / `59,201` conflicts on `large/test_6.cnf` and `54,245` decisions / `44,619` conflicts on `special/hard.cnf`, which supports treating this as a same-search bookkeeping win instead of heuristic drift

### Outcome

- Kept one same-clause-content post-minimization boundary change: `analyze()` now uses the learnt-clause compaction pass itself to finalize best backtrack level and LBD metadata, removing the separate `prepare_learnt_clause()` pass while preserving the resulting learnt clause contents.
- The focused seven-case gate improved modestly but credibly (`30.2756s -> 29.8805s`), and the broader repeat-aware exact-CLI 59-case suite also improved on the retained same-day baseline (`32.2896s -> 31.9532s`) with `59/59` correct outputs.
- The profiler strengthened the keep decision: `large/test_6.cnf` and `special/hard.cnf` kept the same decision and conflict counts as the retained baseline, so this looks like deleted bookkeeping work at the analyze-to-finalization boundary rather than a changed search path.
- Completed `perf-012` as a kept solver-core win, updated the retained benchmark narrative, and advanced the queue to `perf-013`, which should refresh the dense-UNSAT conflict-analysis profile after this new boundary keep before choosing the next bounded experiment.

### Remaining risks

- The focused hotspot improvement is still somewhat uneven because reverse-order `large/test_6.cnf` remained slower, so future work should not assume every nearby boundary rewrite will inherit this win automatically.
- The next task should refresh the dense-UNSAT profile and exact surfaces after this keep instead of immediately stacking another speculative metadata change on top of it.

## 2026-03-22 `perf-011-learnt-finalization-bookkeeping`

- Status: completed
- Task family: native-only dense-UNSAT learnt-finalization bookkeeping experiment
- Branch/worktree: current checkout
- Prompt summary: continue the next deterministic queue task, `perf-011`, by testing one bounded same-clause-content bookkeeping optimization in `prepare_learnt_clause()` or adjacent learnt finalization on the dense UNSAT hotspot slice
- Assumptions:
  - `perf-010` closed the `minimize_learnt()` reason-size branch-order lane for now, so this run should move to adjacent learnt-finalization bookkeeping instead of retrying the same selector surface.
  - `prepare_learnt_clause()` is still visible enough in the retained baseline profile to justify one bounded loop-shape cleanup before moving elsewhere.
  - A retained-noop outcome is acceptable if this narrower finalization cleanup still loses on the seven-case exact-CLI gate.
- Escalations: none

### Plan

- [x] Keep `perf-011` aligned with the queue and record the active experiment in `PLANS.md` before editing.
- [x] Test one bounded `prepare_learnt_clause()` bookkeeping candidate that preserves learnt clause contents while reducing per-literal loop work.
- [x] Run the default verifier plus the seven-case hotspot gate, then keep or revert the candidate based on same-day evidence.
- [x] Update the control plane with the verified outcome and queue the next sensible follow-up.

### Verification

- `python tools/codex_verify.py`
- passed on the temporary candidate before the performance gate
- `python tools/hotspot_compare.py --baseline-cli-script /tmp/perf011_prepare_baseline/satsolver.py --candidate-cli-script satsolver.py large/test_6.cnf special/hard.cnf large/test_10.cnf medium/test_4.cnf medium/test_3.cnf satlib_more/uuf150-01.cnf large/test_8.cnf`
- candidate rejected: the seven-case two-order average regressed from `29.3900s` to `30.4121s`; `large/test_6.cnf` lost badly in forward order (`13.5296s -> 14.9891s`), `special/hard.cnf` and `medium/test_4.cnf` also lost overall, and the small forward gains on `large/test_10.cnf` plus `satlib_more/uuf150-01.cnf` were not enough to compensate
- `python tools/agent_queue_check.py`
- passed: the final queue state resolves cleanly to `current_or_next_task='perf-012'`
- `python tools/codex_verify.py`
- passed: the reverted retained baseline plus final control-plane edits compile, pass the queue check, pass all 73 tests, and clear both default wrapper smoke paths
- `git diff --check`
- passed

### Outcome

- Tested one intentionally tiny learnt-finalization bookkeeping candidate in `prepare_learnt_clause()`: peel the first two learnt literals out of the main loop so the loop only handles indices `2+`, eliminating the per-iteration `index != 0` branch while preserving the resulting learnt clause contents.
- Rejected the candidate after the seven-case exact-CLI hotspot gate still regressed overall. The main failure was `large/test_6.cnf`, which lost `1.46s` in forward order, while the reverse order only barely improved that same case and still regressed `special/hard.cnf`, `satlib_more/uuf150-01.cnf`, and the overall two-order average.
- No solver code was retained. The durable lesson is that `prepare_learnt_clause()` loop-shape cleanup alone is too weak or too unstable to justify keeping, so the queue now advances to `perf-012` and should target a different post-minimization learnt-metadata surface.

### Remaining risks

- This reject only closes the specific “peel the first two literals” loop-shape cleanup inside `prepare_learnt_clause()`; it does not prove that all learnt-finalization bookkeeping work is exhausted.
- The next task should stay same-clause-content but move away from pure loop-shape cleanup and toward a different post-minimization learnt-metadata or analyze-to-finalization boundary surface.

## 2026-03-22 `perf-010-conflict-analysis-bookkeeping`

- Status: completed
- Task family: native-only dense-UNSAT conflict-analysis bookkeeping experiment
- Branch/worktree: current checkout
- Prompt summary: continue the next deterministic queue task, `perf-010`, by testing one same-clause-content conflict-analysis bookkeeping optimization on the dense UNSAT hotspot slice without reopening the minimization-relaxation lane
- Assumptions:
  - `perf-009` closed the relaxed-minimization selector lane for now, so this run should preserve learnt clause contents and search behavior as much as possible.
  - The freshest reason-bucket evidence still says the dominant minimization fast path should be ternary-first, with binary reasons comparatively rare on the dense UNSAT bottlenecks.
  - A retained-noop outcome is acceptable if even this narrower same-search bookkeeping change loses on the seven-case exact-CLI gate.
- Escalations: none

### Plan

- [x] Mark `perf-010` in progress in the control plane and keep repo state aligned before coding.
- [x] Test one bounded same-content candidate in `minimize_learnt()` by making the dominant ternary path the first size check.
- [x] Run the default verifier plus the seven-case hotspot gate, then keep or revert the candidate based on same-day evidence.
- [x] Update the control plane with the verified outcome and queue the next sensible follow-up.

### Verification

- `python -m cProfile -s tottime satsolver.py large/test_6.cnf /tmp/perf010_profile_large6.txt | head -n 45`
- passed: the retained baseline still showed `analyze()` (`3.045s`) plus `minimize_learnt()` (`0.949s`) as the current conflict-analysis bookkeeping surface, with `prepare_learnt_clause()` smaller but still visible at `0.347s`
- `python tools/codex_verify.py`
- passed on the temporary candidate before the performance gate
- `python tools/hotspot_compare.py --baseline-cli-script /tmp/perf010_ternaryfirst_baseline/satsolver.py --candidate-cli-script satsolver.py large/test_6.cnf special/hard.cnf large/test_10.cnf medium/test_4.cnf medium/test_3.cnf satlib_more/uuf150-01.cnf large/test_8.cnf`
- candidate rejected: the seven-case two-order average regressed from `30.6097s` to `32.9908s`; `special/hard.cnf` improved in forward order, but `large/test_6.cnf` regressed in both orders and the reverse half also lost on `special/hard.cnf`, `large/test_10.cnf`, `medium/test_4.cnf`, `medium/test_3.cnf`, `satlib_more/uuf150-01.cnf`, and `large/test_8.cnf`
- `python tools/agent_queue_check.py`
- passed: the final queue state resolves cleanly to `current_or_next_task='perf-011'`
- `python tools/codex_verify.py`
- passed: the reverted retained baseline plus final control-plane edits compile, pass the queue check, pass all 73 tests, and clear both default wrapper smoke paths
- `git diff --check`
- passed

### Outcome

- Tested one intentionally tiny same-clause-content bookkeeping candidate: reorder `minimize_learnt()` so the dominant ternary reason path is checked before the rarer binary path, without changing the resulting learnt clause contents.
- Rejected the candidate after the seven-case exact-CLI hotspot gate still moved the wrong way overall. The main failure was `large/test_6.cnf`, which regressed in both orders (`14.5023s -> 17.8421s`, `14.8687s -> 15.8587s`), and the reverse order broad losses outweighed the forward wins on `special/hard.cnf` and `large/test_10.cnf`.
- No solver code was retained. The durable lesson is that even same-content reason-size branch-order cleanups inside `minimize_learnt()` are too weak or too unstable to trust on this solver, so the queue now advances to `perf-011` and should move to a different conflict-analysis bookkeeping surface.

### Remaining risks

- This reject closes the `minimize_learnt()` reason-size branch-order lane only for now; it does not prove that all same-search conflict-analysis bookkeeping work is exhausted.
- The next task should avoid more reason-size ordering tweaks and instead probe post-minimization learnt finalization or another bookkeeping surface with a clearer structural payoff.

## 2026-03-22 `perf-009-dense-unsat-conflict-analysis`

- Status: completed
- Task family: native-only dense-UNSAT conflict-analysis experiment
- Branch/worktree: current checkout
- Prompt summary: continue the next deterministic queue task, `perf-009`, by using the refreshed dense-UNSAT reason counters to test one bounded conflict-analysis or learnt-minimization change without weakening the structural fast-exit cases
- Assumptions:
  - The watch-family lane is closed for now after `perf-008`, so this run should stay inside conflict analysis rather than revisiting propagation layout.
  - The strongest fresh selector signal is inside `minimize_learnt()`: learnt-only `10+`-literal reasons are expensive to scan but remove very few literals on `large/test_6.cnf` and `special/hard.cnf`.
  - A retained-noop outcome is acceptable if this narrow selector still loses on the seven-case exact-CLI gate.
- Escalations: none

### Plan

- [x] Mark `perf-009` in progress in the control plane and keep repo state aligned before coding.
- [x] Test one bounded candidate in `minimize_learnt()` aimed only at learnt `10+`-literal reasons, keeping the rest of the conflict-analysis path unchanged.
- [x] Run the default verifier plus the seven-case hotspot and structural fast-exit comparisons, then keep or revert the candidate based on same-day evidence.
- [x] Update the control plane with the verified outcome and queue the next sensible follow-up.

### Verification

- `python - <<'PY' ... MeasureSolver selector probe over large/test_6.cnf and special/hard.cnf ... PY`
- passed: the fresh bucket split showed that problem-side minimization checks are entirely ternary on both cases, while the only low-yield bucket is learnt `10+` reasons (`36,846` checks / `4,012` removals on `large/test_6.cnf`, `21,289` checks / `1,885` removals on `special/hard.cnf`)
- `python tools/codex_verify.py`
- passed on the temporary candidate before the performance gate
- `python tools/hotspot_compare.py --baseline-cli-script /tmp/perf009_minlearn10_baseline/satsolver.py --candidate-cli-script satsolver.py large/test_6.cnf special/hard.cnf large/test_10.cnf medium/test_4.cnf medium/test_3.cnf satlib_more/uuf150-01.cnf large/test_8.cnf`
- candidate rejected: the seven-case two-order average regressed from `35.7221s` to `51.1322s`; the worst damage hit the SAT guardrail `large/test_8.cnf` (`0.3848s -> 5.0747s` average), with dense UNSAT regressions on `large/test_6.cnf` (`18.2279s -> 23.3683s`) and `special/hard.cnf` (`10.9885s -> 16.0478s`)
- `python tools/agent_queue_check.py`
- passed: the final queue state resolves cleanly to `current_or_next_task='perf-010'`
- `python tools/codex_verify.py`
- passed: the reverted retained baseline plus final control-plane edits compile, pass the queue check, pass all 73 tests, and clear both default wrapper smoke paths
- `git diff --check`
- passed

### Outcome

- Measured the current dense-UNSAT minimization selector mix directly and used that fresh evidence to test exactly one narrow candidate: skip full redundancy scans only for learnt `10+`-literal reason clauses inside `minimize_learnt()`.
- Rejected the candidate decisively. Even though those long learnt reasons rarely remove literals on the dense UNSAT cases, keeping them unminimized still destabilized the search badly enough to hurt both the dense hotspot slice and the SAT guardrail.
- The strongest failure signal was `large/test_8.cnf`, which rose from about `0.38s` to about `5.07s`, but the candidate also regressed `large/test_6.cnf`, `special/hard.cnf`, `large/test_10.cnf`, and `satlib_more/uuf150-01.cnf`. No solver code was retained.
- Completed `perf-009` as a retained-noop conclusion and advanced the queue to `perf-010`, which now narrows the conflict-analysis lane to same-clause-content bookkeeping instead of more minimization-relaxation rules.

### Remaining risks

- This reject closes the relaxed-minimization selector lane only for now; it does not prove that all conflict-analysis work is exhausted.
- `large/test_8.cnf` remains highly sensitive to even narrow minimization relaxations, so future conflict-analysis tasks should treat it as an early guardrail, not just a final check.

## 2026-03-22 `perf-008-watch-family-split`

- Status: completed
- Task family: native-only dense-UNSAT propagation layout experiment
- Branch/worktree: current checkout
- Prompt summary: continue the next deterministic queue task, `perf-008`, by testing one true split between problem-ternary watchers and the remaining watched-clause traffic, keeping it only if same-day exact-CLI evidence wins without weakening the SAT guardrail or structural fast-exit families
- Assumptions:
  - The freshest PySAT gap analysis and dense-UNSAT profiler counters both point at mixed watched-clause traversal, not wrapper overhead, as the next meaningful native-only lane.
  - A real watcher-family split is different enough from prior branch-shape and payload micro-optimizations to justify one bounded experiment.
  - A retained-noop outcome is acceptable if the split loses on the exact-CLI gates, even if the profiler looks cleaner.
- Escalations: none

### Plan

- [x] Add a dedicated problem-ternary watcher lane in `satsolver_core.py` and mirror it in `tools/profile_solver.py`.
- [x] Add a focused regression that proves problem ternary clauses attach to the dedicated watcher lane without changing solver correctness semantics.
- [x] Run the default verifier plus the seven-case hotspot and structural fast-exit exact-CLI comparisons, then keep or revert the candidate based on same-day evidence.
- [x] Update the control plane with the verified outcome and queue the next sensible follow-up.

### Verification

- `python tools/codex_verify.py`
- passed: the temporary watch-family split compiled, passed the queue check, passed all 74 tests, and stayed valid on the main plus alternate-wrapper smoke paths before the performance gate
- `python tools/hotspot_compare.py --baseline-cli-script /tmp/perf008_watchsplit_baseline/satsolver.py --candidate-cli-script satsolver.py large/test_6.cnf special/hard.cnf large/test_10.cnf medium/test_4.cnf medium/test_3.cnf satlib_more/uuf150-01.cnf large/test_8.cnf`
- candidate rejected: the seven-case two-order average regressed from `24.6075s` to `28.1011s`; `special/hard.cnf`, `large/test_10.cnf`, and `large/test_8.cnf` improved, but `large/test_6.cnf` worsened sharply in both orders (`12.0426s -> 16.2226s`, `11.9371s -> 16.8653s`)
- `python tools/hotspot_compare.py --baseline-cli-script /tmp/perf008_watchsplit_baseline/satsolver.py --candidate-cli-script satsolver.py special/pigeonhole.cnf special/tseitin.cnf`
- passed: the structural fast-exit slice stayed healthy and even improved slightly (`0.0757s -> 0.0604s` two-order average), which narrowed the failure to the dense CDCL path instead of the presolver families
- `python tools/profile_solver.py large/test_6.cnf special/hard.cnf`
- passed: the watch-family split eliminated mixed problem-ternary batches as intended (`problem_ternary_mixed_batch_share=0.0000`), but it also changed the dense search path: `large/test_6.cnf` jumped from the prior `59,201` conflicts to `81,161`, while `special/hard.cnf` improved from `44,619` to `39,511`
- `python tools/agent_queue_check.py`
- passed: the reverted retained baseline plus final control-plane edits resolve cleanly to `current_or_next_task='perf-009'`
- `python tools/codex_verify.py`
- passed: the reverted retained baseline plus final control-plane edits compile, pass the queue check, pass all 73 tests, and clear both default wrapper smoke paths
- `git diff --check`
- passed

### Outcome

- Tested one real watch-family split by moving problem ternary clauses onto their own watcher lists while leaving the remaining watched clauses on the existing lane, then mirrored that layout in the profiler and added a routing regression.
- Rejected the candidate even though the profiler looked cleaner on the narrow metric it targeted. The dedicated lane removed mixed problem-ternary batches and preserved the structural fast-exit families, but the main dense exact-CLI gate still regressed decisively because `large/test_6.cnf` got much worse.
- The profiler explains why this is a clean no-op conclusion instead of a “same search but slower” case: the split changed propagation order enough to change the search itself, inflating `large/test_6.cnf` from `72,886` decisions / `59,201` conflicts to `99,880` decisions / `81,161` conflicts even while helping `special/hard.cnf`.
- Completed `perf-008` as a retained-noop conclusion and advanced the queue to `perf-009`, which now becomes the next deterministic dense-UNSAT lane.

### Remaining risks

- This reject does not prove that all watcher-family work is dead forever, but it does show that a true split is not “just layout” in this solver: changing which family runs first can materially perturb the search, especially on `large/test_6.cnf`.
- The next native-only experiment should therefore move to the already-queued conflict-analysis lane instead of trying another watcher-family rearrangement immediately.

## 2026-03-22 `perf-007-external-gap-targets`

- Status: completed
- Task family: external-reference performance gap analysis
- Branch/worktree: current checkout
- Prompt summary: continue the next deterministic queue task, `perf-007`, by using optional external solver references to sharpen the next native-only optimization target without retaining any non-standard-library dependency
- Assumptions:
  - The repo already has one suitable short-lived external reference path in `satsolver_pysat.py` backed by `.venv-external-sat`, so the highest-signal comparison is to remeasure that path on the refreshed hotspot slice instead of inventing a new adapter.
  - The current seven-case exact-CLI hotspot slice remains the right first gate for dense search-heavy gap analysis, but one or two structural-presolver cases should also be checked so the next native-only task does not blindly chase an area where the current solver already has unique strengths.
  - This task is primarily research and queue refinement, so a retained-noop on solver code is acceptable as long as the next native-only task is narrowed from same-day evidence.
- Escalations: none

### Plan

- [x] Revalidate the optional PySAT comparison path on small SAT and UNSAT smoke cases in the external environment.
- [x] Run a same-day external-reference comparison on the refreshed hotspot slice and targeted structural-presolver cases.
- [x] Translate the observed gap into one concrete next native-only task, then update the control plane and verification log.

### Verification

- `.venv-external-sat/bin/python satsolver_pysat.py small/test_1.cnf /tmp/perf007_pysat_small_sat.txt && python tools/checker.py small/test_1.cnf /tmp/perf007_pysat_small_sat.txt`
- passed: the optional external wrapper still produced a valid SAT model on the shared DIMACS/output path
- `.venv-external-sat/bin/python satsolver_pysat.py special/tseitin.cnf /tmp/perf007_pysat_small_unsat.txt && python tools/checker.py special/tseitin.cnf /tmp/perf007_pysat_small_unsat.txt --bruteforce-var-limit 0`
- passed: the external wrapper still produced a valid UNSAT result in the external environment
- `python - <<'PY' ... backend sweep across minisat22, glucose4, cadical195, mergesat3, kissat404 on large/test_6.cnf and special/hard.cnf ... PY`
- passed: `minisat22` remained the strongest local PySAT backend on the two heaviest dense UNSAT cases (`0.5813s` total versus `1.0239s` for `glucose4`, `1.1116s` for `kissat404`, `1.1983s` for `cadical195`, and `2.4508s` for `mergesat3`)
- `SATSOLVER_PYSAT_BACKEND=minisat22 python tools/hotspot_compare.py --baseline-cli-script satsolver.py --candidate-cli-script satsolver_pysat.py --candidate-python-executable .venv-external-sat/bin/python large/test_6.cnf special/hard.cnf large/test_10.cnf medium/test_4.cnf medium/test_3.cnf satlib_more/uuf150-01.cnf large/test_8.cnf`
- passed: the refreshed seven-case exact-CLI comparison stayed fully checker-valid and showed a huge dense-UNSAT ceiling gap, with the retained solver at `24.6944s` versus PySAT at `1.2486s` on the two-order average; the current solver only kept the SAT guardrail edge on `large/test_8.cnf` (about `0.2841s` versus `0.3218s`)
- `SATSOLVER_PYSAT_BACKEND=minisat22 python tools/hotspot_compare.py --baseline-cli-script satsolver.py --candidate-cli-script satsolver_pysat.py --candidate-python-executable .venv-external-sat/bin/python special/pigeonhole.cnf special/tseitin.cnf`
- passed: the structural fast-exit slice confirmed the opposite side of the story, with the retained solver at `0.0702s` versus PySAT at `3.4322s` on the two-order average
- `python tools/profile_solver.py large/test_6.cnf special/hard.cnf`
- passed: dense UNSAT profiling still shows massive mixed watch-family traffic on the hard cases, including `problem_ternary_mixed_batch_share=0.6193` on `large/test_6.cnf` and `0.7078` on `special/hard.cnf`, plus millions of problem-ternary visits and high learnt-large coexistence inside those batches
- `python tools/agent_queue_check.py`
- passed: final queue edits resolve cleanly to `current_or_next_task='perf-008'`
- `python tools/codex_verify.py`
- passed: the retained native-only solver plus control-plane updates still compile, pass the queue check, pass all 73 tests, and clear both default wrapper smoke paths
- `git diff --check`
- passed

### Outcome

- Revalidated the optional PySAT comparison path and confirmed that `minisat22` is still the strongest local external backend worth using as a speed ceiling in this repo.
- Fresh same-day exact-CLI evidence shows that the retained native-only solver still trails a mature external backend badly on dense search-heavy UNSAT families: the refreshed seven-case slice fell from `24.6944s` to `1.2486s` under PySAT, with the biggest gaps on `large/test_6.cnf` (`11.9414s` average versus `0.3395s`) and `special/hard.cnf` (`8.0909s` versus `0.2627s`).
- The same evidence also reconfirmed that the current repo-specific structural presolvers are real strengths, not dead weight: the retained solver crushed PySAT on `special/pigeonhole.cnf` and `special/tseitin.cnf` (`0.0702s` versus `3.4322s` two-order average).
- Combined with the refreshed profiler counters, that points the next native-only task away from more wrapper work or structural fast-exit changes and toward the dense UNSAT CDCL core, specifically the mixed watch-family traversal where problem ternary traffic and learnt-large watchers are still heavily interleaved.
- Completed `perf-007` as a research-only queue-refinement task with no retained solver-code change, and added `perf-008` as the next concrete native-only experiment: test a true watch-family split on the dense UNSAT hotspot slice while preserving the SAT guardrail and structural fast-exit families.

### Remaining risks

- PySAT is only a ceiling reference, not a search-trace oracle, so the next native-only task still needs to validate its candidate directly on the repo's exact-CLI slices instead of cargo-culting external-solver behavior.
- The profiler strongly suggests a watch-family split lane, but previous lighter-weight propagation micro-optimizations have often lost on `large/test_8.cnf`, so the new structural and SAT guardrail slices must remain part of the next experiment's gate.

## 2026-03-22 `perf-006-wrapper-startup-overhead`

- Status: completed
- Task family: native-only wrapper and startup measurement
- Branch/worktree: current checkout
- Prompt summary: continue the next deterministic queue task, `perf-006`, by measuring remaining wrapper and startup overhead on the refreshed exact-CLI path and keeping only a clearly justified native-only win
- Assumptions:
  - The remaining exact-CLI wrapper lane is narrow because the repo has already kept CLI-mode import gating, runtime-`typing` cleanup, and targeted CLI-local aliasing while rejecting many broader wrapper-surface trims.
  - A retained-noop conclusion is acceptable if fresh measurement shows the remaining repo-local wrapper cost is too small or too exhausted to justify another low-confidence patch.
  - The startup-sensitive tiny SAT/UNSAT cases are still the right place to estimate wrapper overhead, while the seven-case hotspot slice remains the guardrail against weakening the real exact-CLI path.
- Escalations: none

### Plan

- [x] Re-read the wrapper/startup keep/reject history and inspect the current exact-CLI wrapper shape for any non-duplicate candidate.
- [x] Measure the current exact-CLI startup floor directly and compare interpreter-only, import-only, and tiny full-CLI timings.
- [x] Conclude the task with either one bounded wrapper candidate or a retained-noop result grounded in the fresh measurements.
- [x] Update the control plane with the verified outcome.

### Verification

- `python - <<'PY' ... repeated tiny exact-CLI timings for small/test_1.cnf, special/tseitin.cnf, and large/test_8.cnf ... PY`
- passed: current exact-CLI means were about `0.0532s` on `small/test_1.cnf`, `0.0382s` on `special/tseitin.cnf`, and `0.4148s` on `large/test_8.cnf`, confirming that the startup-sensitive cases are still well below the dense UNSAT bottlenecks
- `python -X importtime -c 'import satsolver' 2>&1 | tail -n 40`
- passed: retained wrapper import time was only about `4.0ms` on top of Python/site startup, with `satsolver_core` around `3.4ms` cumulative and `satsolver_io` around `0.2ms`
- `python - <<'PY' ... repeated subprocess timings for python -c pass, python -c 'import satsolver', and python satsolver.py small/test_1.cnf /tmp/_probe.txt ... PY`
- passed: `python -c pass` averaged about `27.5ms`, `python -c 'import satsolver'` about `31.2ms`, and the full small SAT CLI about `36.0ms`, leaving only a few milliseconds of repo-local wrapper plus solve-path overhead beyond interpreter startup and import
- `python tools/agent_queue_check.py`
- passed: the final queue state resolves cleanly to `current_or_next_task='perf-007'`
- `python tools/codex_verify.py`
- passed: retained solver baseline plus final control-plane edits compile, pass the queue check, pass all 73 tests, and clear both wrapper smoke paths
- `git diff --check`
- passed

### Outcome

- Re-read the current wrapper/startup history and confirmed that the repo has already exhausted the most plausible exact-CLI surface trims: CLI-mode import gating, runtime-`typing` cleanup, targeted CLI-local aliasing, and no-root-pure wrapper selection are already kept, while broader alias, import-surface, parse-summary, and output-path rewrites are already rejected.
- Measured the current startup floor directly and found that most of the smallest exact-CLI runtime is now outside meaningful repo-local control on this machine: Python process startup alone is about `27.5ms`, `import satsolver` adds only about `3.7ms`, and the full `small/test_1.cnf` CLI path averages only about `36.0ms`.
- Completed `perf-006` as a retained-noop conclusion because the remaining repo-local wrapper overhead is too small, too noisy, and too exhaustively mined to justify another low-confidence patch.
- Advanced the queue to `perf-007`, where any further speed gains are more likely to come from external-reference gap analysis than from more exact-CLI wrapper trimming.

### Remaining risks

- The retained measurements are machine-specific, so a future environment with materially different Python startup cost or filesystem behavior could reopen a wrapper lane. On the current machine, though, the remaining exact-CLI floor is dominated by interpreter startup rather than repo-local wrapper logic.

## 2026-03-22 `perf-005-branching-restart-heuristics`

- Status: completed
- Task family: native-only branching and restart heuristic experiment
- Branch/worktree: current checkout
- Prompt summary: continue the next deterministic queue task, `perf-005`, by testing one bounded branching or restart heuristic change against the refreshed seven-case exact-CLI hotspot slice
- Assumptions:
  - The next viable heuristic experiment should avoid already-rejected branch-frontier, heap, and simple parameter-sweep lanes.
  - A retained-noop conclusion is acceptable if the bounded heuristic candidate loses cleanly on same-day exact-CLI evidence.
  - The refreshed seven-case slice remains the right first gate before any broader exact-CLI rerun.
- Escalations: none

### Plan

- [x] Inspect current branching and restart behavior plus recent keep/reject history to choose one non-duplicate heuristic candidate.
- [x] Implement or stage the candidate, validate correctness locally, and run the refreshed seven-case hotspot A/B.
- [x] If the hotspot signal is promising, run the broader exact-CLI repeat-aware gate; otherwise revert to a retained-noop conclusion.
- [x] Update the control plane with the verified outcome.

### Verification

- `python tools/codex_verify.py`
- passed: the temporary candidate compiled, passed the queue check, passed all 73 tests, and stayed valid on the main plus alternate-wrapper smoke cases
- `python tools/hotspot_compare.py --baseline-cli-script /tmp/perf005_restart_baseline.c4riuk/satsolver.py --candidate-cli-script satsolver.py large/test_6.cnf special/hard.cnf large/test_10.cnf medium/test_4.cnf medium/test_3.cnf satlib_more/uuf150-01.cnf large/test_8.cnf`
- candidate rejected: the low-LBD early-restart trigger regressed the seven-case two-order average from `34.7641s` to `56.2904s`, made every hotspot case slower, and still inflated `large/test_8.cnf` from about `0.35s` to about `7.5s`
- `python tools/agent_queue_check.py`
- passed: the final queue state resolves cleanly to `current_or_next_task='perf-006'`
- `python tools/codex_verify.py`
- passed: the retained solver baseline plus final control-plane edits compile, pass the queue check, pass all 73 tests, and clear both wrapper smoke paths after the revert
- `git diff --check`
- passed

### Outcome

- Chose a bounded restart-policy experiment instead of revisiting already-rejected branch-frontier or heap schemes: trigger an early root restart only when a conflict learns an `LBD <= 3` clause after at least half of the current Luby window has elapsed.
- Rejected that heuristic immediately after the refreshed seven-case exact-CLI gate regressed decisively on every measured case, including a fresh SAT-side blow-up on `large/test_8.cnf`.
- Retained no solver code from `perf-005` and advanced the queue to `perf-006`, which now becomes the next deterministic wrapper/startup lane.

### Remaining risks

- The branching/restart lane still lacks a winning classifier-based change, and `large/test_8.cnf` remains highly sensitive to restart-policy drift even when a candidate is aimed at dense UNSAT cases.

## 2026-03-22 `perf-004-propagation-clause-storage`

- Status: completed
- Task family: native-only propagation and clause-database experiment
- Branch/worktree: current checkout
- Prompt summary: continue the next deterministic queue task, `perf-004`, by testing one bounded propagation or clause-storage micro-optimization against the refreshed seven-case exact-CLI hotspot slice
- Assumptions:
  - The best candidate should come from the current `propagate()` or `reduce_database()` shape plus the latest keep/reject history, not from stale generic SAT heuristics.
  - A retained-noop conclusion is acceptable if the bounded candidate loses cleanly on same-day exact-CLI evidence.
  - The refreshed seven-case slice is the right focused A/B gate before any broader exact-CLI rerun.
- Escalations: none

### Plan

- [x] Inspect the current propagation and clause-database hot paths plus recent experiment history to choose one non-redundant bounded candidate.
- [x] Implement or stage the candidate, validate correctness locally, and run the refreshed seven-case hotspot A/B.
- [x] If the hotspot signal is promising, run the broader exact-CLI repeat-aware gate; otherwise revert to a retained-noop conclusion.
- [x] Update the control plane with the verified outcome.

### Verification

- `python tools/profile_solver.py large/test_6.cnf special/hard.cnf medium/test_4.cnf large/test_8.cnf`
- passed: the current retained baseline still shows `reduce_database()` operating on only a few hundred candidates per reduction, while learnt-large watch traffic remains real but secondary to original ternary propagation
- `python -m cProfile -s tottime satsolver.py medium/test_4.cnf /tmp/perf004_profile_medium4.txt | head -n 40`
- passed: `reduce_database()` stayed tiny (`0.021s` tottime, `0.052s` cumtime) versus `propagate()` (`2.145s` tottime), so the only justified clause-storage experiment was a retention-policy classifier change rather than reduction bookkeeping cleanup
- `python tools/codex_verify.py`
- passed: the temporary candidate compiled, passed the queue check, passed all 73 tests, and stayed valid on the main plus alternate-wrapper smoke cases
- `python tools/hotspot_compare.py --baseline-cli-script /tmp/perf004_lenbucket_baseline.TE0c9p/satsolver.py --candidate-cli-script satsolver.py large/test_6.cnf special/hard.cnf large/test_10.cnf medium/test_4.cnf medium/test_3.cnf satlib_more/uuf150-01.cnf large/test_8.cnf`
- candidate rejected: the coarse `10+`-literal learnt-clause penalty regressed the seven-case two-order average from `30.0666s` to `72.6652s`, roughly doubled `large/test_6.cnf`, and exploded `large/test_8.cnf` from about `0.31s` to `25s..27s`
- `python tools/agent_queue_check.py`
- passed: the final queue state resolves cleanly to `current_or_next_task='perf-005'`
- `python tools/codex_verify.py`
- passed: the retained solver baseline plus final control-plane edits compile, pass the queue check, pass all 73 tests, and clear both wrapper smoke paths after the revert
- `git diff --check`
- passed

### Outcome

- Profiled the refreshed hotspot baseline before changing code and confirmed that direct `reduce_database()` bookkeeping remains too small to justify another locked-set or schedule cleanup branch on its own.
- Tested one bounded clause-storage classifier: within each LBD bucket, demote `10+`-literal learnt clauses behind shorter candidates while keeping the existing top-half retention schedule unchanged.
- Rejected that candidate immediately after the refreshed seven-case exact-CLI gate regressed catastrophically, especially on `large/test_8.cnf`, so no solver code was retained.
- Completed `perf-004` as a retained-noop conclusion and advanced the queue to `perf-005`, which now becomes the next deterministic heuristic lane.

### Remaining risks

- The clause-database lane still lacks a winning native-only classifier, and `large/test_8.cnf` is highly sensitive to extra learnt-clause load. Future storage experiments should use the SAT-like guardrail early rather than trusting UNSAT-only wins.

## 2026-03-22 `perf-003-native-cli-baseline-refresh`

- Status: completed
- Task family: benchmark-driven native-only baseline refresh
- Branch/worktree: current checkout
- Prompt summary: continue the next deterministic queue task, `perf-003`, by refreshing the same-day exact-CLI native-only baseline, selecting the current hotspot slice, and grounding the next optimization targets in fresh evidence
- Assumptions:
  - The most useful first step is a same-day repeat-aware exact-CLI benchmark on the retained standard-library solver across the default benchmark folders.
  - The hotspot slice should be chosen from representative exact-CLI time contribution, not from stale historical notes alone.
  - This task is primarily measurement and planning, so the retained solver code may stay unchanged if the refreshed evidence is the only durable outcome.
- Escalations: none

### Plan

- [x] Run a same-day repeat-aware exact-CLI benchmark for the retained solver and capture a machine-readable report.
- [x] Summarize the heaviest representative cases and choose a refreshed hotspot slice with rationale.
- [x] Translate the fresh baseline into concrete next native-only optimization recommendations and update the control plane.
- [x] Run the required verification gates and record the final outcome.

### Verification

- `python tools/codex_verify.py --benchmark-mode cli --repeat 2 --benchmark-output /tmp/perf003_cli_benchmark.txt`
- passed: exact-CLI report landed at `/tmp/perf003_cli_benchmark.txt`, with `59/59` correct, `32.2896s` representative total, `64.5793s` measured total, and `64.8235s` wall clock
- `python tools/agent_queue_check.py`
- passed: final control-plane edits still resolve to `current_or_next_task='perf-004'`
- `python tools/codex_verify.py`
- passed: compile, queue check, 73 tests, and both main plus alternate-wrapper smoke paths stayed green after the hotspot-slice sync
- `git diff --check`
- passed

### Outcome

- Refreshed the same-day repeat-aware exact-CLI baseline for the retained native-only solver and confirmed that runtime is now heavily concentrated in a small UNSAT-dominant slice.
- The top two cases, `large/test_6.cnf` (`14.1187s`) and `special/hard.cnf` (`9.4353s`), account for `72.95%` of the exact-CLI total by themselves, while the top five cases reach `88.24%`.
- Chose a refreshed seven-case hotspot slice of `large/test_6.cnf`, `special/hard.cnf`, `large/test_10.cnf`, `medium/test_4.cnf`, `medium/test_3.cnf`, `satlib_more/uuf150-01.cnf`, and `large/test_8.cnf`, which together cover `90.82%` of the exact-CLI total while still preserving a SAT-like guardrail via `large/test_8.cnf`.
- Synced that seven-case slice into the future hotspot-compare verification commands for `perf-004`, `perf-005`, and `perf-006`, and pointed the next run at `perf-004` because the current baseline still argues for propagation or clause-database work before branching-policy exploration.

### Remaining risks

- The refreshed slice is still benchmark-only evidence; the next run needs a concrete bounded solver candidate before we can tell whether propagation or clause-database changes actually beat the retained baseline.

## 2026-03-22 `perf-002-native-optimization-queue`

- Status: completed
- Task family: queue seeding for native-only performance research
- Branch/worktree: current checkout
- Prompt summary: create a long-running SAT-solver optimization direction that may use external libraries during research while keeping the final retained solver standard-library only
- Assumptions:
  - The control plane should not encode this as one endless vague task because queued work in this repo must stay bounded and verifiable.
  - External libraries or solvers are acceptable only as short-lived comparison references; retained code and default verification must remain native-only.
  - The best single-run slice is to reopen the queue with a deterministic performance program and leave the first concrete benchmark task ready for the next run.
- Escalations: none

### Plan

- [x] Reframe the open-ended optimization goal as a rolling queue of bounded performance tasks.
- [x] Sync the native-only policy and external-reference rule into the durable repo guidance.
- [x] Reopen the queue, point the next run at the first exact-CLI baseline refresh task, and verify the control plane.

### Verification

- `python tools/agent_queue_check.py`
- passed: the refreshed queue, state, and next-task hint are consistent
- `python tools/codex_verify.py`
- passed: compile, queue check, unit tests, and standard smoke checks all remained green after the queue refresh
- `git diff --check`
- passed

### Outcome

- Reopened the autonomous queue with a rolling native-only optimization program instead of leaving the repo without queued work.
- Added concrete benchmark-driven tasks for baseline refresh, propagation experiments, heuristic experiments, wrapper-overhead work, and optional external-reference research.
- Clarified in the durable docs that external libraries are allowed only as short-lived research references and that only native-only wins may be retained in the submission path.

### Remaining risks

- The new optimization lane still needs same-day baseline refresh work in `perf-003` before any specific solver-change experiment should be attempted.

## 2026-03-22 `perf-001-portfolio-gate-revalidation`

- Status: completed
- Task family: benchmark-driven portfolio-threshold revalidation
- Branch/worktree: current checkout
- Prompt summary: continue the next deterministic queue task, `perf-001`, by revalidating the current portfolio gating thresholds against same-day evidence and either keeping a threshold change or recording a retained-noop conclusion with rationale
- Assumptions:
  - The current gate still appears to collapse to a single live benchmark case, so the first bounded revalidation should test whether a nearby threshold broadening earns enough same-day hotspot improvement to justify a broader exact-CLI run.
  - Temporary scratch candidates in `/tmp` are acceptable for rejected performance probes as long as the retained repo is restored cleanly and the durable outcome is recorded here.
  - `python tools/codex_verify.py` remains the retained-code verification gate, while `tools/hotspot_compare.py` and exact-CLI repeat runs provide the same-day performance evidence for keep/reject decisions.
- Escalations: none

### Plan

- [x] Mark `perf-001` active in the queue state and capture the current portfolio-gate shape from the live corpus.
- [x] Build a bounded scratch candidate that broadens the portfolio gate in one plausible way and compare it against the retained solver on a same-day hotspot slice.
- [x] If the hotspot signal is promising, run the broader exact-CLI repeat-aware gate; otherwise keep a retained-noop conclusion and document why the current thresholds remain.
- [x] Run retained-code verification and record the final outcome.

### Verification

- `python - <<'PY' ... corpus scan for current portfolio hits and near-miss all-ternary cases ... PY`
- passed: current retained gate still matches only `large/test_8.cnf`; the nearest dense miss is `special/hard.cnf` at density `4.25`, while low-density near misses are `large/test_1.cnf`, `large/test_7.cnf`, and `large/test_9.cnf`
- `python -m py_compile /tmp/scratch_satsolver_portfolio_minclauses800.py`
- passed
- `python /tmp/scratch_satsolver_portfolio_minclauses800.py small/test_1.cnf /tmp/perf001_sat.txt`
- `python tools/checker.py small/test_1.cnf /tmp/perf001_sat.txt`
- passed
- `python /tmp/scratch_satsolver_portfolio_minclauses800.py special/tseitin.cnf /tmp/perf001_unsat.txt`
- `python tools/checker.py special/tseitin.cnf /tmp/perf001_unsat.txt --bruteforce-var-limit 0`
- passed
- `python tools/hotspot_compare.py --baseline-cli-script satsolver.py --candidate-cli-script /tmp/scratch_satsolver_portfolio_minclauses800.py --repeat 2 large/test_1.cnf large/test_7.cnf large/test_8.cnf large/test_9.cnf`
- passed: candidate regressed the two-order average from `0.4872s` to `0.6538s`, with the newly admitted cases roughly doubling in runtime and `large/test_8.cnf` also slightly worse
- `python tools/codex_verify.py`
- passed: retained solver still compiles, passes 73 tests, and clears both `satsolver.py` and `satsolver_fast.py` smoke checks

### Outcome

- Revalidated the live portfolio gate against today’s corpus and confirmed that the retained thresholds still narrow the portfolio path to exactly one benchmark case: `large/test_8.cnf`.
- Tested one bounded threshold broadening by lowering only the clause-count gate from `1000` to `800`, which admitted `large/test_1.cnf`, `large/test_7.cnf`, and `large/test_9.cnf`.
- Rejected that broadened candidate immediately because the same-day exact-CLI hotspot slice regressed decisively, so the retained solver keeps the current portfolio thresholds unchanged.

### Remaining risks

- This revalidation only ruled out the most plausible low-clause broadening; if future solver-core changes materially alter process-launch or portfolio-worker cost, the threshold space may deserve another focused rescan.

## 2026-03-22 `tool-001-wrapper-verification`

- Status: completed
- Task family: verification tooling
- Branch/worktree: current checkout
- Prompt summary: continue the next deterministic queue task, `tool-001`, by expanding routine verification coverage for the alternate standard-library wrapper path after the shared `satsolver_io.py` extraction
- Assumptions:
  - The smallest useful slice is to make `python tools/codex_verify.py` smoke-test `satsolver_fast.py` in addition to the main submission CLI.
  - `satsolver_pysat.py` should remain outside the default gate because it depends on an optional external environment.
  - This is primarily a tooling-and-wiring task, so `python tools/codex_verify.py` remains the primary verification gate.
- Escalations: none

### Plan

- [x] Mark `tool-001` active in the queue state and inspect the existing verification helper flow.
- [x] Extend `tools/codex_verify.py` to cover the alternate standard-library wrapper smoke path.
- [x] Add regression coverage for the new verification flow and update durable docs if needed.
- [x] Run verification and record the final outcome.

### Verification

- `python -m unittest discover -s tests -p 'test_codex_verify.py' -q`
- passed: 7 tests
- `python tools/codex_verify.py`
- passed: compile, queue check, 73 tests, submission smoke checks, and `satsolver_fast.py` smoke checks all completed successfully

### Outcome

- Expanded `tools/codex_verify.py` so the routine verification gate now smoke-tests `satsolver_fast.py` alongside the main submission CLI.
- Added regression coverage for the alternate-wrapper step generation in `tests/test_codex_verify.py`.
- Updated repo docs and contracts so the default verification scope explicitly includes the standard-library alternate wrapper path.

### Remaining risks

- The default verification gate still excludes `satsolver_pysat.py` because that wrapper depends on an optional external environment.

## 2026-03-22 `sat-001-shared-io-helper`

- Status: completed
- Task family: solver maintainability refactor
- Branch/worktree: current checkout
- Prompt summary: continue the next deterministic queue task, `sat-001`, by deduplicating shared DIMACS parsing and result-writing helpers across `satsolver.py` and `satsolver_fast.py`
- Assumptions:
  - A dedicated standard-library helper module for parsing and output formatting is the smallest reversible slice that removes the duplication without changing solver behavior.
  - `satsolver_blaze.py` can stay untouched because its parser is separate legacy comparison code, while `satsolver_pysat.py` can safely use the same helper to avoid indirect dependence on `satsolver.py`.
  - `python tools/codex_verify.py` remains the right verification gate because this is a behavior-preserving shared-code refactor.
- Escalations: none

### Plan

- [x] Extract shared DIMACS parsing and result-writing helpers into a dedicated module.
- [x] Update `satsolver.py`, `satsolver_fast.py`, and any overlapping wrapper call sites to use the shared helper without changing public APIs.
- [x] Add targeted regression coverage for the shared helper path.
- [x] Run verification and record the final outcome.

### Verification

- `python tools/agent_queue_check.py`
- passed: live `.agent/STATE.yaml` and `.agent/TASK_QUEUE.yaml` remained consistent during the refactor
- `python -m unittest discover -s tests -q`
- passed: 70 tests
- `python tools/codex_verify.py`
- passed: compile, queue check, 70 tests, SAT smoke, and UNSAT smoke all completed successfully

### Outcome

- Added `satsolver_io.py` as the shared DIMACS parsing and result-writing helper for the thin wrapper modules.
- Updated `satsolver.py`, `satsolver_fast.py`, and `satsolver_pysat.py` to use the shared helper without changing their public APIs.
- Added regression coverage in `tests/test_solver_io.py` and refreshed the repo map in `AGENT.md`, `AGENTS.md`, and `README.md`.

### Remaining risks

- `satsolver_blaze.py` still carries its own legacy parser and output path, so future unification work should treat it as a separate comparison-solver task instead of silently folding it into the new helper.

## 2026-03-22 `cp-003-queue-consistency-checker`

- Status: completed
- Task family: autonomous queue control-plane hardening
- Branch/worktree: current checkout
- Prompt summary: continue from the queue control plane and implement the next deterministic task, `cp-003`, by adding a standard-library consistency checker for `.agent/STATE.yaml` and `.agent/TASK_QUEUE.yaml`
- Assumptions:
  - Wiring the new checker into `python tools/codex_verify.py` is the most reliable way to make stale queue state fail fast in routine autonomous verification.
  - A small repo-specific YAML subset parser is acceptable because the control-plane files are intentionally simple and standard-library only.
  - This task should stay in the tooling-and-docs lane, so `python tools/codex_verify.py` remains the primary verification gate.
- Escalations: none

### Plan

- [x] Inspect the current verification helper and define the queue invariants to enforce.
- [x] Implement `tools/agent_queue_check.py` plus focused regression tests.
- [x] Wire the checker into the routine verification flow and update the durable docs if needed.
- [x] Run verification and record the final outcome.

### Verification

- `python tools/agent_queue_check.py`
- passed: live `.agent/STATE.yaml` and `.agent/TASK_QUEUE.yaml` are consistent
- `python -m unittest discover -s tests -q`
- passed: 67 tests
- `python tools/codex_verify.py`
- passed: compile, queue check, 67 tests, SAT smoke, and UNSAT smoke all completed successfully

### Outcome

- Added `tools/agent_queue_check.py`, a standard-library validator for the repo’s YAML control-plane subset plus queue-selection and state/queue consistency checks.
- Added focused regression coverage for the validator and updated `tools/codex_verify.py` so routine verification now fails fast on stale queue state.
- Documented the standalone queue-check command in repo docs and test gates.

### Remaining risks

- The YAML parser is intentionally narrow and repo-specific; if future control-plane files adopt more complex YAML features, the checker will need to expand with them.

## 2026-03-22 `queue-control-plane-bootstrap`

- Status: completed
- Task family: repo-local autonomous queue control plane bootstrap
- Branch/worktree: current checkout
- Prompt summary: create a deterministic repo-local queue system, seed it from repo reality, and complete the first tightly coupled doc-sync task so repeated identical prompts can continue without human task management
- Assumptions:
  - The existing `AGENTS.md` plus `PLANS.md` flow is useful context but not deterministic enough to be the only control plane.
  - `python tools/codex_verify.py` is the right default gate for control-plane and documentation changes in this repo.
  - Syncing legacy docs and agent instructions is tightly coupled with the control-plane bootstrap and can share the same verification.
- Escalations: none

### Plan

- [x] Inspect the repo, current docs, verification tools, and solver layout to infer the real project shape.
- [x] Create `AGENT.md`, `.agent/*`, and `QUEUE_PROMPT.md` with repo-specific queue rules.
- [x] Seed an initial phased task queue and honest repo state snapshot.
- [x] Complete the tightly coupled follow-up task of aligning legacy workflow docs and agent instructions with the new queue model.
- [x] Run verification and record the outcome.

### Verification

- `python tools/codex_verify.py`
- passed: compile, unit tests, SAT smoke, and UNSAT smoke all completed successfully

### Outcome

- Added a deterministic repo-local control plane rooted in `AGENT.md` and `.agent/*`, plus a stable repeated prompt in `QUEUE_PROMPT.md`.
- Synced `AGENTS.md`, `README.md`, and the Codex operator docs so future runs read one queue-driven workflow instead of split guidance.
- Seeded the next concrete task as `cp-003`, a control-plane consistency checker.

### Remaining risks

- Queue consistency is still enforced by process and manual review until `cp-003` adds a machine-checkable validator.

## 2026-03-22 `codex-autonomous-workflow-bootstrap`

- Status: completed
- Task family: autonomous SAT solver maintenance
- Branch/worktree: current checkout
- Prompt summary: bootstrap a repo-native Codex workflow for future queued tasks with minimal human steering
- Assumptions:
  - The missing task-family placeholder should default to benchmark-driven SAT solver maintenance for this repo.
  - Existing benchmark and experiment files remain the durable history for future solver work.
- Escalations: none

### Plan

- [x] Inspect repo structure, commands, and current benchmark conventions.
- [x] Create durable repo instructions in `AGENTS.md`.
- [x] Add a reusable skill, operator guide, and queued-task template.
- [x] Add a small verification helper and test coverage for it.
- [x] Run verification and capture outcomes here.

### Verification

- `python -m unittest discover -s tests -q`
- `python tools/codex_verify.py`
- `python tools/codex_verify.py --benchmark-mode cli --benchmark-folders small special`

### Outcome

- Added a repo-native Codex workflow layer that routes autonomous runs through `AGENTS.md`, this plan file, a local skill, a reusable verification helper, and operator-facing docs.
- Kept the workflow bounded: default checks are fast, benchmark verification is opt-in, and existing repo tools remain the underlying validation surface.

### Remaining risks

- Worktree creation is documented rather than scripted.
- Performance experiments still require judgment about how much benchmark evidence is enough for a keep or revert decision.
