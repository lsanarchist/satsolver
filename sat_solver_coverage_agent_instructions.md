# Інструкція для агента: додати coverage / stress-тести для SAT solver-а

## Мета

Не міняти SAT-solving алгоритм, якщо немає явного failure. Поточна версія solver-а вже виглядає фінальною: CDCL + watched literals + clause learning + VSIDS-like activity + global restart tuning + phase-diversified portfolio + structural detectors. Завдання агента — **підняти впевненість у correctness / robustness / submission readiness**, а не ще раз тюнити евристики.

Основний ризик зараз не в тому, що solver повільний на відомих наборах, а в тому, що спеціальні detectors або portfolio можуть мати приховані edge-case bugs:

- false `UNSAT` від Mycielski graph-coloring detector-а;
- некоректна SAT model output;
- зависання або zombie-processes від multiprocessing portfolio;
- поламаний single-file submission;
- неправильна поведінка parser-а на DIMACS edge cases;
- regressions біля межі `500 vars / 2000 clauses`.

## Поточний baseline, який не можна погіршити

Перед змінами зафіксувати baseline:

```text
formulae:
  35/35 solved
  0 errors
  avg5 total ≈ 10.02s

course_cnf_tests with Mycielski:
  279/279 solved
  0 errors
  avg5 total ≈ 26.44s

highlight:
  cnf_training_complex__complex_cnf_hard__mycielski_iter4_color5_unsat.cnf
  UNSAT
  vars=235
  clauses=1697
  avg5≈0.037s
```

Ці числа не треба відтворювати побітово, бо є шум CPU/process startup, але correctness має лишитись `100%`, timeout-ів не має з’явитися, а total time не має суттєво погіршитись.

## Головне правило

**Не додавати нові алгоритмічні optimizations у цьому завданні.**

Дозволено:

- додавати tests;
- додавати generators для synthetic CNF;
- додавати checker / validation utilities;
- додавати benchmark harness;
- додавати smoke scripts;
- додавати packaging verification.

Не дозволено без окремої причини:

- міняти `GLOBAL_RESTART_BASE`;
- міняти `GLOBAL_VAR_DECAY`;
- міняти `GLOBAL_CLAUSE_DECAY`;
- міняти `GLOBAL_INITIAL_NEXT_REDUCE`;
- міняти `PORTFOLIO_MAX_DENSITY`;
- міняти `PHASE_PORTFOLIO_MODES`;
- переписувати CDCL core;
- розширювати Mycielski detector так, щоб він став менш строгим;
- додавати filename-based detection типу `"mycielski" in path`.

## Бажана структура файлів

Створи або доповни:

```text
tests/
  generated/
    mycielski/
    graph_coloring/
    random_near_limit/
    portfolio_density/
    parser_edge_cases/
  scripts/
    generate_regression_cases.py
    run_regression_smoke.py
    validate_output.py
    check_single_file_submission.py
    stress_portfolio_cleanup.py
  must_pass/
    README.md
```

Якщо в repo вже є інша структура, адаптуйся до неї, але тримай логіку розділеною.

---

# 1. Mycielski detector false-positive coverage

## Чому це найважливіше

Mycielski detector повертає `UNSAT` структурно. Якщо він помилиться, solver може видати `UNSAT` для SAT-формули. Це гірше за timeout.

## Додати SAT guard-cases

Згенерувати або додати CNF:

```text
mycielski_iter2_color4_sat.cnf
mycielski_iter3_color5_sat.cnf
mycielski_iter4_color6_sat.cnf
```

Очікування:

```text
solver output: SAT
model valid: yes
detector must NOT return structural UNSAT
```

Особливо важливий `iter4_color6_sat`, бо він близький до hard case:

```text
iter4_color5 -> UNSAT
iter4_color6 -> SAT
```

## Додати UNSAT cases

```text
mycielski_iter2_color3_unsat.cnf
mycielski_iter3_color4_unsat.cnf
mycielski_iter4_color5_unsat.cnf
```

Очікування:

```text
solver output: UNSAT
runtime should be tiny, ideally <0.2s per CLI run on normal machine
```

## Acceptance criteria

```text
All Mycielski SAT cases -> SAT with valid model
All Mycielski UNSAT under-coloring cases -> UNSAT
No Mycielski SAT case may be solved by returning structural UNSAT
```

Якщо є internal flag/log для detector-а, перевірити:

```text
detector=True only for valid under-coloring UNSAT Mycielski cases
detector=False for SAT Mycielski cases
```

Якщо такого flag/log нема — не додавати production debug output. Можна викликати detector напряму в unit-test path, якщо він доступний як функція.

---

# 2. Mutated Mycielski / graph-coloring CNF

## Мета

Переконатися, що detector не матчить “майже Mycielski”.

Зробити мутовані копії hard CNF:

```text
remove_one_edge_clause.cnf
add_one_extra_edge_clause.cnf
remove_one_vertex_color_clause.cnf
duplicate_some_clauses.cnf
add_tautology_clause.cnf
renumber_variables_permutation.cnf
shuffle_clauses.cnf
change_one_color_block.cnf
add_unused_variable.cnf
```

## Очікування

Для кожної mutation треба явно записати expected behavior.

Рекомендовано:

```text
shuffle_clauses:
  expected same as original
  detector may still detect

renumber_variables_permutation:
  expected same as original
  detector may detect only if detector supports arbitrary renumbering
  if detector assumes block encoding, it must safely fall back to CDCL, not false UNSAT

duplicate_some_clauses:
  expected same as original
  detector may accept or reject, але output must be correct

add_tautology_clause:
  expected same satisfiability
  detector should usually reject strict structure and fall back safely

remove_one_edge_clause:
  satisfiability may change
  detector must NOT blindly return UNSAT unless it can re-prove exact Mycielski lower bound

add_one_extra_edge_clause:
  formula remains at least as constrained
  detector must be conservative; if exact structure broken, fall back

remove_one_vertex_color_clause:
  encoding no longer standard graph-coloring
  detector must reject

change_one_color_block:
  detector must reject
```

## Acceptance criteria

```text
No mutated SAT formula may return UNSAT incorrectly.
If expected status is unknown, validate with brute-force only for small mutations.
For large mutations with unknown status, only assert: detector must reject or solver must not crash.
```

Не створювати великий suite з unknown expected statuses, який потім важко інтерпретувати.

---

# 3. General graph-coloring coverage

## Мета

Перевірити, що Mycielski detector не лізе в ordinary graph coloring, якщо це не exact Mycielski under-coloring.

Згенерувати стандартні graph-coloring CNF:

```text
K4_color3_unsat.cnf
K4_color4_sat.cnf
K5_color4_unsat.cnf
C5_color2_unsat.cnf
C5_color3_sat.cnf
bipartite_20_color2_sat.cnf
random_graph_v20_k3_sat.cnf
random_graph_v20_k2_unsat.cnf
```

Encoding:

```text
x_v_1 x_v_2 ... x_v_k 0       # each vertex has at least one color
-x_v_i -x_v_j 0               # vertex has at most one color
-x_u_c -x_v_c 0               # adjacent vertices cannot share color c
```

## Acceptance criteria

```text
All SAT graph-coloring cases -> SAT with valid model.
All UNSAT graph-coloring cases -> UNSAT.
Mycielski structural detector must not false-positive on non-Mycielski graphs.
```

Для малих графів можна додати brute-force graph-coloring oracle, незалежний від SAT solver-а.

---

# 4. Near-limit CNF coverage

Assignment limit: up to roughly:

```text
vars <= 500
clauses <= 2000
timeout <= 60s
```

Згенерувати stress cases near limit:

```text
random3sat_n500_m2000_seed1.cnf
random3sat_n500_m2000_seed2.cnf
planted3sat_n450_m1900_seed1.cnf
planted3sat_n450_m1900_seed2.cnf
xor_sparse_unsat_n240_eq330_w3_4_seed1.cnf
tseitin_deg3_v240_unsat.cnf
pigeonhole_php_22_into_21_or_near_limit.cnf
```

Для random3sat без known oracle не використовувати як correctness-only test, якщо expected status невідомий. Краще:

- для SAT: planted assignment generator, expected `SAT`;
- для UNSAT: use known constructions: pigeonhole, XOR inconsistent system, Tseitin parity contradiction.

## Acceptance criteria

```text
No crash.
No invalid model.
No output format violation.
No runtime > 60s on target machine.
SAT planted cases produce valid model.
Known UNSAT structural cases produce UNSAT.
```

---

# 5. Phase portfolio boundary coverage

## Мета

Portfolio gate біля density threshold був важливим tradeoff-ом. Треба мати tests, які ловлять regression біля межі.

Згенерувати planted/random 3-CNF з density:

```text
4.20
4.25
4.30
4.35
4.40
4.50
```

Для кожної density:

```text
n=260, 320, 400
seed=1..5
SAT planted cases
UNSAT/random or known-hard samples only if expected status known
```

## Що вимірювати

Для кожного case:

```text
result status
model validity if SAT
runtime
whether portfolio path is used, якщо є internal test hook
```

Не додавати production logs. Якщо треба перевірити portfolio decision, зробити окремий unit helper:

```python
should_use_parallel_portfolio(num_vars, clauses)
```

і тестувати його напряму.

## Acceptance criteria

```text
All planted SAT cases are valid SAT.
No density-boundary case exceeds 60s.
No systematic regression >20% vs current baseline without explicit reason.
large/test_8.cnf remains fast; target around <=0.3s avg on normal local runs.
```

---

# 6. SAT model validation

## Мета

Гарантувати, що кожен SAT output не просто пише `SAT`, а дає коректну повну model.

Validator має перевіряти:

```text
first line exactly SAT or UNSAT
for SAT:
  second line exists
  literals are integers
  ends with 0
  every variable 1..num_vars appears exactly once
  no variable outside 1..num_vars
  no duplicate variable with conflicting sign
  all clauses satisfied
for UNSAT:
  no model required
  optional extra whitespace allowed
```

Для small formulas `num_vars <= 16` додати brute-force oracle:

```text
solver says SAT  -> brute-force says SAT
solver says UNSAT -> brute-force says UNSAT
```

## Acceptance criteria

```text
All SAT outputs in formulae + course_cnf_tests + generated SAT cases pass model validation.
All small generated cases match brute-force oracle.
```

---

# 7. Parser / malformed DIMACS coverage

Додати valid edge cases:

```text
empty_formula_n0.cnf
empty_formula_n5.cnf
empty_clause_unsat.cnf
unit_conflict_unsat.cnf
duplicate_literals_sat.cnf
tautology_only_sat.cnf
tautology_plus_empty_unsat.cnf
comments_before_header.cnf
comments_after_header.cnf
blank_lines.cnf
multiple_clauses_on_one_line.cnf
unmentioned_variables_sat.cnf
```

Додати invalid cases:

```text
missing_header.cnf
bad_header_token.cnf
wrong_clause_count.cnf
literal_out_of_range.cnf
unterminated_clause_no_zero.cnf
non_integer_literal.cnf
negative_var_index_invalid_token.cnf
```

## Acceptance criteria

Valid DIMACS:

```text
return code 0
output file created
output format valid
```

Invalid DIMACS:

```text
return code nonzero
no misleading SAT/UNSAT output
clear error message on stderr or stdout
```

Не треба робити invalid-input behavior складним; головне — не silent wrong answer.

---

# 8. Single-file packaging test

## Чому це важливо

Submission може очікувати саме:

```bash
python satsolver.py input.cnf output.txt
```

Якщо фінальний `satsolver.py` імпортує `satsolver_core.py` / `satsolver_io.py`, а grader бере тільки один файл, буде `ModuleNotFoundError`.

## Test

Створити script:

```bash
tmpdir=$(mktemp -d)
cp satsolver.py "$tmpdir/"
cp tests/generated/parser_edge_cases/unit_sat.cnf "$tmpdir/input.cnf"
cd "$tmpdir"
python satsolver.py input.cnf output.txt
cat output.txt
```

## Acceptance criteria

Якщо submission має бути single-file:

```text
works with only satsolver.py copied
no ModuleNotFoundError
```

Якщо submission дозволяє multi-file:

```text
document exact files needed:
  satsolver.py
  satsolver_core.py
  satsolver_io.py
```

Але без confirmation від grader безпечніше зробити single-file.

---

# 9. Multiprocessing / portfolio cleanup tests

## Мета

Переконатися, що portfolio не лишає zombie processes і не зависає parent process.

Зробити stress script:

```text
Run large/test_8.cnf 50 times via CLI.
Run planted3sat_balanced_n260_m1108_seed1.cnf 20 times via CLI.
Run a mix of SAT/UNSAT cases 100 times.
After each batch, check:
  no hanging child processes
  no temporary output corruption
  return code is 0
```

Python варіант:

```python
import subprocess
import time

for i in range(100):
    proc = subprocess.run(
        [sys.executable, "satsolver.py", input_path, output_path],
        timeout=60,
        capture_output=True,
        text=True,
    )
    assert proc.returncode == 0
    validate_output(input_path, output_path)
```

Optional Unix check:

```bash
ps -o pid,ppid,cmd | grep satsolver
```

## Acceptance criteria

```text
No hangs.
No timeout on repeated portfolio cases.
No zombie child processes accumulating.
Output remains valid on every run.
```

---

# 10. Must-pass regression suite

Створити `tests/must_pass/README.md` зі списком файлів, які треба ганяти після будь-якої зміни:

```text
formulae/large/test_6.cnf                         UNSAT, hard CDCL
formulae/special/hard.cnf                         UNSAT, hard random
formulae/large/test_8.cnf                         SAT, phase portfolio
formulae/large/test_10.cnf                        UNSAT
formulae/medium/test_4.cnf                        UNSAT
formulae/special/dense.cnf                        UNSAT
formulae/special/pigeonhole.cnf                   UNSAT detector
formulae/special/tseitin.cnf                      UNSAT/XOR/Tseitin-like

course/mycielski_iter4_color5_unsat.cnf           UNSAT, structural detector
course/mycielski_iter4_color6_sat.cnf             SAT, false-positive guard
course/mycielski_iter3_color5_sat.cnf             SAT, false-positive guard
course/planted3sat_balanced_n260_m1108_seed1.cnf  SAT, hard planted
course/planted3sat_balanced_n200_m852_seed2.cnf   SAT, planted
course/ramsey_R3_4_n9_unsat.cnf                   UNSAT, Ramsey
course/ramsey_R3_4_n10_unsat.cnf                  UNSAT, Ramsey
course/xor_sparse_sat_n128_eq165_w3_4_seed3.cnf   SAT, XOR-ish
course/xor_sparse_unsat_n240_eq330_w3_4_seed1.cnf UNSAT, XOR-ish
```

Якщо exact filenames відрізняються — використовуй наявні matching files.

## Acceptance criteria

```text
must_pass suite:
  100% solved
  0 errors
  0 timeout
  all SAT models valid
```

---

# 11. Suggested commands

Адаптувати під repo, але бажано мати такі команди:

```bash
python -m py_compile satsolver.py satsolver_core.py satsolver_io.py

python tests/scripts/generate_regression_cases.py

python tests/scripts/run_regression_smoke.py \
  --solver ./satsolver.py \
  --suite tests/must_pass \
  --timeout 60

python tests/scripts/run_regression_smoke.py \
  --solver ./satsolver.py \
  --suite tests/generated \
  --timeout 60

python tests/scripts/check_single_file_submission.py \
  --solver ./satsolver.py

python benchmark_suite.py satsolver /tmp/formulae_avg5.txt formulae \
  --repeat 5 \
  --cli-script satsolver.py

python benchmark_suite.py satsolver /tmp/course279_avg5.txt course_cnf_tests \
  --repeat 5 \
  --cli-script satsolver.py
```

Якщо `benchmark_suite.py` має інший interface, не переписувати benchmark tool заради цієї інструкції; використати актуальні repo commands.

---

# 12. Final acceptance checklist

Завдання вважати виконаним тільки якщо:

```text
[ ] py_compile passes
[ ] formulae 35/35, 0 errors
[ ] course set including Mycielski 279/279, 0 errors
[ ] mycielski_iter4_color5_unsat -> UNSAT fast
[ ] mycielski_iter4_color6_sat -> SAT valid model
[ ] all Mycielski SAT false-positive guards pass
[ ] mutated Mycielski tests do not produce false UNSAT
[ ] graph-coloring SAT/UNSAT small tests pass
[ ] near-limit generated tests do not crash or timeout
[ ] portfolio boundary tests pass
[ ] parser valid/invalid edge cases behave as expected
[ ] SAT model validator passes on all SAT outputs
[ ] multiprocessing cleanup stress passes
[ ] single-file packaging test passes or multi-file submission requirement is explicitly documented
```

## Performance guardrails

Do not accept a change if:

```text
formulae avg5 total worsens by >10% without clear reason
course279 avg5 total worsens by >10% without clear reason
large/test_8.cnf becomes slow again, e.g. >0.5s avg locally
mycielski_iter4_color5_unsat stops being fast
any new timeout appears
any SAT model validation fails
any false UNSAT appears on SAT graph-coloring / Mycielski guard cases
```

## Reporting format

Generate a final report:

```text
coverage_report.md
```

It should include:

```text
- commands run
- environment: Python version, OS if available
- datasets tested
- number of generated tests
- pass/fail summary
- slowest 20 cases
- Mycielski detector guard summary
- portfolio boundary summary
- parser edge-case summary
- packaging result
- remaining known risks
```

Keep report factual. Do not claim hidden-test guarantees.

---

# Non-goals

Do not implement these unless separately requested:

```text
Ramsey-specific detector
Van der Waerden-specific detector
new branching heap
new watched-literal representation
new restart schedule
new clause minimization pass
DSATUR as production fallback
randomized nondeterministic search
external SAT solver comparison in submitted package
```

The solver is already strong enough on known workloads. The objective here is to make sure the final submission is robust, reproducible, and not vulnerable to structural false positives.
