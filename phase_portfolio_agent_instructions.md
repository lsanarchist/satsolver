# Інструкція для агента: Phase-Diversified Portfolio для `satsolver.py`

## Мета

Додати до SAT solver-а **phase-diversified portfolio**: паралельний запуск кількох копій того самого CDCL solver-а з різними початковими `phase`-стратегіями. Результат береться від першого worker-а, який повернув `SAT` або `UNSAT`, після чого інші процеси завершуються.

Цільова проблема: поточний solver уже добре прискорив важкі UNSAT-випадки, але має стабільний SAT-regression на великих 3-CNF, особливо `large/test_8.cnf`. Portfolio має зменшити ризик, що solver довго шукає модель через невдалий початковий напрям `True/False` для змінних.

## Контекст з benchmark-ів

Поточний solver правильний на видимих і broad-наборах, тому не треба переписувати CDCL-ядро.

Відомі факти:

- `formulae/`: `35/35` correct, `0` timeout.
- `course_cnf_tests`: `278/278` correct, `0` timeout, якщо виключити known hard Mycielski timeout-case.
- Поточний solver значно швидший за old solver на UNSAT-heavy випадках.
- Основний видимий regression: `large/test_8.cnf`, SAT, приблизно `0.29s -> 1.6-1.8s`.

Висновок: не чіпати глобальні CDCL restart/decay параметри. Додати тільки phase-diversity навколо вже наявного portfolio-механізму.

## Основна ідея

CDCL solver робить два типи вибору:

1. яку змінну branch-ити;
2. яке значення спробувати першим: `True` чи `False`.

Другий пункт — це `phase`.

Для UNSAT-випадків phase менш критичний, бо solver усе одно має довести неможливість. Для SAT-випадків phase дуже важливий: один початковий набір значень може швидко привести до моделі, інший — довго блукати по search tree.

Тому запускаємо кілька worker-ів:

```text
worker 1: default phase
worker 2: deterministic pseudo-random phase, lcg1
worker 3: negative phase bias
worker 4: positive phase bias, optional
```

Перший worker, який повернув коректний результат, виграє.

## Обмеження

Не ламати ці речі:

- CLI лишається таким самим:

```bash
python satsolver.py input.cnf output.txt
```

- Output format не міняти:

```text
UNSAT
```

або

```text
SAT
<l1> <l2> ... <ln> 0
```

- Не використовувати external SAT solvers, PySAT, Z3, MiniSAT, subprocess або non-stdlib packages.
- Не змінювати DIMACS parser.
- Не змінювати conflict analysis / watched literals / clause learning без окремої причини.
- Не міняти глобальні параметри restart/decay у цій задачі:

```python
GLOBAL_RESTART_BASE
GLOBAL_VAR_DECAY
GLOBAL_CLAUSE_DECAY
GLOBAL_INITIAL_NEXT_REDUCE
```

- Не вмикати portfolio для малих задач, бо multiprocessing overhead може зробити їх повільнішими.
- Не вмикати SAT-phase portfolio для щільних UNSAT 3-CNF, наприклад `large/test_6.cnf`.

## Де змінювати

Очікувані файли:

```text
satsolver_core.py
satsolver.py
```

У поточній архітектурі частина логіки дублюється в `satsolver.py` і `satsolver_core.py`. Якщо обидва файли містять `solve_cnf_serial`, `solve_cnf_portfolio`, `solve_cnf_fast_serial` або worker-функції, треба синхронно оновити обидва місця.

Якщо фінальна версія вже об'єднана в один `satsolver.py`, робити ті самі зміни тільки там.

## Крок 1 — додати phase mode constants

У модулі з core-налаштуваннями додати константи:

```python
PHASE_MODE_DEFAULT = "default"
PHASE_MODE_BIAS_POSITIVE = "bias_positive"
PHASE_MODE_BIAS_NEGATIVE = "bias_negative"
PHASE_MODE_LCG1 = "lcg1"

# Порядок важливий: якщо CPU мало, беремо перші N modes.
# lcg1 ставимо рано, бо він дає найбільшу диверсифікацію.
PHASE_PORTFOLIO_MODES = (
    PHASE_MODE_DEFAULT,
    PHASE_MODE_LCG1,
    PHASE_MODE_BIAS_NEGATIVE,
    PHASE_MODE_BIAS_POSITIVE,
)
```

Можна стартувати з 3 worker-ів:

```python
PHASE_PORTFOLIO_MODES = (
    PHASE_MODE_DEFAULT,
    PHASE_MODE_LCG1,
    PHASE_MODE_BIAS_NEGATIVE,
)
```

Це безпечніший перший варіант, бо менше multiprocessing overhead.

## Крок 2 — замінити `seed_saved_phases_from_bias()` на generalized mode

У класі `Solver` додати новий метод:

```python
def seed_saved_phases_mode(self, mode: str) -> None:
    if mode == PHASE_MODE_DEFAULT:
        return

    values = self.values
    saved_phase = self.saved_phase
    phase_bias = self.phase_bias

    if mode == PHASE_MODE_BIAS_POSITIVE:
        for variable in range(1, self.num_vars + 1):
            if values[variable] == UNASSIGNED:
                saved_phase[variable] = phase_bias[variable] >= 0
        return

    if mode == PHASE_MODE_BIAS_NEGATIVE:
        for variable in range(1, self.num_vars + 1):
            if values[variable] == UNASSIGNED:
                saved_phase[variable] = phase_bias[variable] < 0
        return

    if mode == PHASE_MODE_LCG1:
        for variable in range(1, self.num_vars + 1):
            if values[variable] == UNASSIGNED:
                saved_phase[variable] = (
                    ((variable * 2654435761) >> 17) & 1
                ) == 1
        return

    raise ValueError(f"unknown phase mode: {mode}")
```

Важливо:

- `default` нічого не змінює.
- `lcg1` має бути deterministic, без `random`, без time-based seed.
- Перевірка `values[variable] == UNASSIGNED` потрібна, щоб не перезаписати root-level assignments, наприклад pure literals.
- Старий метод `seed_saved_phases_from_bias()` можна залишити як wrapper для backward compatibility:

```python
def seed_saved_phases_from_bias(self) -> None:
    self.seed_saved_phases_mode(PHASE_MODE_BIAS_POSITIVE)
```

## Крок 3 — оновити serial solve API

Зараз може бути щось типу:

```python
def solve_cnf_serial(num_vars, clauses, *, seed_phase_bias=False):
    solver = Solver(num_vars)
    ...
    if seed_phase_bias:
        solver.seed_saved_phases_from_bias()
    return solver.solve()
```

Замінити на:

```python
def solve_cnf_serial(
    num_vars: int,
    clauses: list[list[int]],
    *,
    phase_mode: str = PHASE_MODE_DEFAULT,
) -> list[int] | None:
    solver = Solver(num_vars)

    # Залишити наявну root pure literal логіку, якщо вона тут є.
    root_pure_literals = find_iterative_root_pure_literals(num_vars, clauses)
    if len(root_pure_literals) >= ROOT_PURE_LITERAL_MIN_ASSIGNMENTS:
        for literal in root_pure_literals:
            if not solver.enqueue(literal, None):
                return None

    for clause in clauses:
        if not solver.add_problem_clause(clause):
            return None

    solver.seed_saved_phases_mode(phase_mode)
    return solver.solve()
```

Для fast serial path аналогічно:

```python
def solve_cnf_fast_serial(
    num_vars: int,
    clauses: list[list[int]],
    *,
    phase_mode: str = PHASE_MODE_DEFAULT,
) -> list[int] | None:
    solver = Solver(num_vars)

    for clause in clauses:
        if not solver.add_problem_clause(clause):
            return None

    solver.seed_saved_phases_mode(phase_mode)
    return solver.solve()
```

Якщо є зовнішні або тестові виклики зі старим `seed_phase_bias`, можна тимчасово підтримати обидва API, але внутрішній portfolio має перейти на `phase_mode`.

## Крок 4 — оновити portfolio worker

Було приблизно так:

```python
def solve_portfolio_worker(seed_phase_bias: bool, result_queue) -> None:
    model = solve_cnf_fast_serial(
        num_vars,
        clauses,
        seed_phase_bias=seed_phase_bias,
    )
    result_queue.put((True, model))
```

Має стати так:

```python
def solve_portfolio_worker(phase_mode: str, result_queue) -> None:
    try:
        model = solve_cnf_fast_serial(
            num_vars,
            clauses,
            phase_mode=phase_mode,
        )
        result_queue.put((True, phase_mode, model))
    except BaseException as exc:
        result_queue.put((False, phase_mode, f"{type(exc).__name__}: {exc}"))
```

Потім створювати processes по modes:

```python
cpu_count = os.cpu_count() or 1
modes = PHASE_PORTFOLIO_MODES[: max(2, min(cpu_count, len(PHASE_PORTFOLIO_MODES)))]

processes = [
    context.Process(target=solve_portfolio_worker, args=(mode, result_queue))
    for mode in modes
]
```

Якщо хочеш обмежити overhead, використовуй максимум 3 worker-и:

```python
max_workers = min(cpu_count, 3, len(PHASE_PORTFOLIO_MODES))
modes = PHASE_PORTFOLIO_MODES[:max_workers]
```

Рекомендований старт:

```python
max_workers = min(cpu_count, 3, len(PHASE_PORTFOLIO_MODES))
```

## Крок 5 — правильно обробити перший результат

Оновити queue loop:

```python
errors: list[str] = []

try:
    remaining = len(processes)
    while remaining > 0:
        ok, phase_mode, payload = result_queue.get()
        remaining -= 1

        if ok:
            return payload

        errors.append(f"{phase_mode}: {payload}")
finally:
    for process in processes:
        if process.is_alive():
            process.terminate()
    for process in processes:
        process.join()
    result_queue.close()
    result_queue.join_thread()

raise RuntimeError(f"Parallel portfolio failed: {'; '.join(errors)}")
```

Не друкувати debug output у stdout/stderr під час нормального запуску, бо grader може очікувати тільки output file.

## Крок 6 — не розширювати portfolio gate без потреби

Залишити наявну логіку приблизно такою:

```python
def should_use_parallel_portfolio(num_vars: int, clauses: list[list[int]]) -> bool:
    if os.environ.get(PORTFOLIO_DISABLE_ENV):
        return False
    if os.name != "posix":
        return False
    if (os.cpu_count() or 1) < 2:
        return False
    if num_vars < PORTFOLIO_MIN_VARS or len(clauses) < PORTFOLIO_MIN_CLAUSES:
        return False
    if not all(len(clause) == 3 for clause in clauses):
        return False
    return (len(clauses) / num_vars) <= PORTFOLIO_MAX_DENSITY
```

Не вмикати portfolio для всіх формул.

Причина:

- small/medium tasks часто розв'язуються за `0.02-0.05s`; multiprocessing overhead може бути більший за solve time.
- dense UNSAT 3-CNF, наприклад `large/test_6.cnf`, не виграє від SAT-phase diversification.
- portfolio найбільше корисне для великих SAT або near-threshold 3-CNF.

## Крок 7 — що робити з `PORTFOLIO_MAX_DENSITY`

Ця задача — про phase modes, не про density tuning.

Не міняй `PORTFOLIO_MAX_DENSITY` у цьому патчі, якщо окремо не попросили.

Якщо треба вибрати значення:

- `4.3` — консервативніше під видимий `formulae/` sample.
- `4.4` — краще за broad `278` benchmark і може краще generalize на hidden tests.

Але phase-diversified portfolio має працювати з будь-яким із цих значень.

## Очікуваний ефект

Очікується:

- `large/test_8.cnf` має стати швидшим або принаймні не гіршим.
- planted SAT cases біля density `4.2-4.4` можуть стати стабільнішими.
- важкі UNSAT cases, які не проходять portfolio gate, не мають змінитися.
- correctness не має змінитися взагалі.

Не очікується:

- значне прискорення small cases;
- прискорення pigeonhole/tseitin/dense UNSAT;
- покращення structural Mycielski timeout-case — для цього потрібен окремий graph-coloring/DSATUR detector.

## Acceptance criteria

Патч можна приймати тільки якщо виконуються всі умови:

1. Python файли компілюються:

```bash
python3 -m py_compile satsolver.py satsolver_core.py satsolver_io.py
```

Якщо фінальна версія single-file:

```bash
python3 -m py_compile satsolver.py
```

2. CLI працює без зміни формату:

```bash
python3 satsolver.py formulae/large/test_8.cnf /tmp/out.txt
cat /tmp/out.txt
```

3. Checker проходить для representative cases:

```bash
python3 tools/checker.py formulae/large/test_8.cnf /tmp/out.txt
```

4. Немає нових correctness failures:

```bash
python3 benchmark_suite.py satsolver /tmp/bench_formulae.txt formulae --repeat 2 --cli-script satsolver.py
```

Очікування: `35/35`, `0` timeout.

5. Broad benchmark не має нових timeout/correctness failures:

```bash
python3 benchmark_suite.py satsolver /tmp/bench_course.txt course_cnf_tests --repeat 2 --cli-script satsolver.py
```

Очікування: retained cases мають лишитися valid, без нових timeout.

6. Не merge-ити, якщо:

- `large/test_8.cnf` не покращився або став ще повільнішим;
- `large/test_6.cnf` або `special/hard.cnf` сильно регреснули;
- broad total time виріс більше ніж на приблизно `5%`;
- з'явився будь-який invalid output;
- з'явився будь-який новий timeout.

## Рекомендований micro-benchmark перед повним benchmark-ом

Спершу швидко перевірити тільки цільові cases:

```bash
python3 satsolver.py formulae/large/test_8.cnf /tmp/test8.out
python3 tools/checker.py formulae/large/test_8.cnf /tmp/test8.out

python3 satsolver.py formulae/large/test_6.cnf /tmp/test6.out
python3 tools/checker.py formulae/large/test_6.cnf /tmp/test6.out

python3 satsolver.py formulae/special/hard.cnf /tmp/hard.out
python3 tools/checker.py formulae/special/hard.cnf /tmp/hard.out

python3 satsolver.py formulae/large/test_10.cnf /tmp/test10.out
python3 tools/checker.py formulae/large/test_10.cnf /tmp/test10.out
```

Також порівняти serial path без portfolio:

```bash
SATSOLVER_DISABLE_PORTFOLIO=1 python3 satsolver.py formulae/large/test_8.cnf /tmp/test8_serial.out
python3 tools/checker.py formulae/large/test_8.cnf /tmp/test8_serial.out
```

## Debugging notes

Якщо `large/test_8.cnf` не прискорився:

1. Перевірити, чи взагалі спрацював `should_use_parallel_portfolio()`.
2. Перевірити density:

```text
large/test_8.cnf: vars=298, clauses=1210, density≈4.06
```

Він має проходити gate при `PORTFOLIO_MAX_DENSITY >= 4.2`.

3. Перевірити порядок modes. `lcg1` має бути серед перших worker-ів.
4. Якщо CPU count обмежений двома, бажаний порядок:

```python
PHASE_PORTFOLIO_MODES = (
    PHASE_MODE_DEFAULT,
    PHASE_MODE_LCG1,
    PHASE_MODE_BIAS_NEGATIVE,
    PHASE_MODE_BIAS_POSITIVE,
)
```

5. Тимчасово додати локальний debug тільки під env flag, але не залишати print-и у фінальній версії:

```python
if os.environ.get("SATSOLVER_DEBUG_PORTFOLIO"):
    print(f"portfolio modes: {modes}", file=sys.stderr)
```

## Ризики

Основний ризик — multiprocessing overhead.

Тому:

- не запускати portfolio на малих задачах;
- не запускати більше 3 worker-ів без benchmark-перевірки;
- не змінювати density threshold у тому самому патчі, якщо мета — ізолювати ефект phase modes;
- не додавати nondeterministic randomness.

## Короткий опис для commit message

```text
Add phase-diversified SAT portfolio modes

Replace boolean seed_phase_bias portfolio workers with deterministic phase modes:
default, lcg1, bias_negative, and optional bias_positive. Keep the existing
portfolio gate so the extra workers are used only for large low-density 3-CNF
instances. This targets SAT phase-sensitivity regressions such as large/test_8
without changing CDCL restart/decay parameters or dense UNSAT behavior.
```

## Definition of done

Зміна вважається завершеною, якщо:

- `phase_mode` повністю замінив boolean portfolio selection у worker-ах;
- `default`, `lcg1`, `bias_negative` реально запускаються як окремі worker-и;
- старий `seed_saved_phases_from_bias()` або видалений без поломок, або залишений як compatibility wrapper;
- `formulae` benchmark лишається `35/35` без timeout;
- broad benchmark не має нових invalid/timeouts;
- `large/test_8.cnf` показує помітне покращення або принаймні не є regression;
- у фінальному solver-i немає debug prints і немає зовнішніх залежностей.
