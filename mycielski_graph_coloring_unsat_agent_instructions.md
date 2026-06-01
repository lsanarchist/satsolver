# Інструкція для агента: Mycielski graph-coloring UNSAT detector

## Мета

Додати у SAT solver вузький структурний detector, який розпізнає CNF як **standard graph-coloring encoding** для **Mycielski graph**, доводить, що кількість доступних кольорів менша за нижню межу хроматичного числа, і миттєво повертає:

```text
UNSAT
```

Це потрібно для hard case типу:

```text
cnf_training_complex__complex_cnf_hard__mycielski_iter4_color5_unsat.cnf
```

Для такого файлу generic CDCL може зависати або йти до timeout, хоча формула має очевидну структурну причину UNSAT:

```text
Mycielski iter4 graph має chromatic number 6
CNF дозволяє тільки 5 colors
5 < 6  =>  UNSAT
```

Detector має бути **строгим** і **conservative**: якщо немає 100% впевненості, що це саме Mycielski graph-coloring UNSAT, він повинен повернути `False` / `UNKNOWN` і віддати формулу звичайному CDCL/portfolio solver-у.

---

## Важливе правило

Не робити shortcut по імені файлу.

Погано:

```python
if "mycielski" in filename:
    return None
```

Правильно:

```python
if graph_coloring_mycielski_unsat(num_vars, clauses):
    return None
```

Detector має аналізувати **тільки структуру CNF**, а не назву файлу.

---

## Де інтегрувати

Додати detector у core solving path перед дорогим CDCL/portfolio search.

Рекомендоване місце:

```python
def solve_cnf(num_vars: int, clauses: list[list[int]]) -> list[int] | None:
    if has_pigeonhole_core(clauses):
        return None

    if xor_system_unsat(num_vars, clauses):
        return None

    if graph_coloring_mycielski_unsat(num_vars, clauses):
        return None

    if should_use_parallel_portfolio(num_vars, clauses):
        return solve_cnf_portfolio(num_vars, clauses)

    return solve_cnf_fast_serial(num_vars, clauses)
```

Якщо проект modular:

```text
satsolver.py
satsolver_core.py
satsolver_io.py
```

то реалізацію краще покласти в `satsolver_core.py`, а з `satsolver.py` викликати через:

```python
base.graph_coloring_mycielski_unsat(num_vars, clauses)
```

Якщо фінальна здача single-file, тоді inline-нути detector прямо в `satsolver.py`.

---

## Очікувана поведінка функції

Сигнатура:

```python
def graph_coloring_mycielski_unsat(
    num_vars: int,
    clauses: list[list[int]],
) -> bool:
    ...
```

Повернення:

```text
True   => формула точно graph-coloring Mycielski UNSAT, можна повернути UNSAT
False  => не впевнені, не чіпати, нехай працює звичайний solver
```

Функція **ніколи не повинна повертати SAT model**. Вона тільки доводить окремий клас `UNSAT`.

---

## Частина 1: розпізнати graph-coloring CNF encoding

Стандартний graph coloring CNF має такі clauses.

### 1. At least one color per vertex

Для кожної вершини `v` є positive clause довжини `k`:

```text
x_v_1 x_v_2 ... x_v_k 0
```

Приклад для `k = 5`:

```text
1 2 3 4 5 0
6 7 8 9 10 0
11 12 13 14 15 0
```

Ці clauses задають групи змінних:

```text
vertex 0 -> colors [1, 2, 3, 4, 5]
vertex 1 -> colors [6, 7, 8, 9, 10]
vertex 2 -> colors [11, 12, 13, 14, 15]
```

### 2. At most one color per vertex

Для кожної вершини і кожної пари кольорів є binary negative clause:

```text
-x_v_i -x_v_j 0
```

Для `k = 5` на одну вершину має бути:

```text
C(5, 2) = 10
```

таких clauses.

### 3. Edge color conflicts

Для кожного edge `(u, v)` і кожного кольору `c` є binary negative clause:

```text
-x_u_c -x_v_c 0
```

Це означає: суміжні вершини не можуть мати однаковий color.

---

## Як парсити graph-coloring encoding

Створити helper:

```python
def parse_graph_coloring_encoding(
    num_vars: int,
    clauses: list[list[int]],
) -> tuple[int, list[set[int]]] | None:
    ...
```

Повернення:

```text
(k, adjacency)  => CNF схожа на exact graph-coloring encoding
None            => це не graph-coloring encoding, detector не застосовується
```

де:

```text
k          = кількість кольорів
adjacency  = undirected graph як list[set[int]]
```

### Алгоритм парсингу

1. Зібрати всі positive clauses:

```python
positive_clauses = [clause for clause in clauses if all(lit > 0 for lit in clause)]
```

2. Всі positive clauses мають мати однакову довжину `k`.

Reject якщо:

```text
немає positive clauses
k < 2
positive clauses різної довжини
```

3. Вважати кожну positive clause групою змінних одного vertex.

Нормалізувати:

```python
vertex_groups = [tuple(sorted(clause)) for clause in positive_clauses]
```

4. Перевірити, що групи disjoint і разом покривають усі змінні `1..num_vars`.

Reject якщо:

```text
змінна зустрілась у двох vertex groups
є змінні поза groups
num_vars != number_of_vertices * k
```

5. Побудувати lookup:

```python
var_to_vertex_color[var] = (vertex_id, color_id)
```

`color_id` береться з позиції змінної у sorted vertex group.

6. Обробити всі negative binary clauses:

```python
if len(clause) == 2 and clause[0] < 0 and clause[1] < 0:
    a = -clause[0]
    b = -clause[1]
```

Reject якщо clause не positive і не binary-negative.

7. Розділити binary-negative clauses на два типи.

#### Intra-vertex at-most-one

Якщо `a` і `b` належать одному vertex, але різним colors:

```python
va, ca = var_to_vertex_color[a]
vb, cb = var_to_vertex_color[b]

if va == vb and ca != cb:
    at_most_one_pairs.add((va, min(ca, cb), max(ca, cb)))
```

#### Inter-vertex edge constraint

Якщо `a` і `b` належать різним vertices, але одному color:

```python
if va != vb and ca == cb:
    edge_color_pairs.add((min(va, vb), max(va, vb), ca))
```

Reject якщо:

```text
va != vb, але ca != cb
va == vb, але ca == cb
literal не належить жодній vertex group
```

8. Перевірити completeness `at-most-one`:

Для кожного vertex `v` і кожної пари colors `(i, j)` має бути clause:

```python
for v in range(num_vertices):
    for i in range(k):
        for j in range(i + 1, k):
            required = (v, i, j)
            if required not in at_most_one_pairs:
                return None
```

9. Побудувати graph edges.

З `edge_color_pairs` треба згрупувати по `(u, v)`:

```python
edge_to_colors[(u, v)].add(color_id)
```

Для кожного `(u, v)` має бути рівно всі кольори:

```python
edge_to_colors[(u, v)] == set(range(k))
```

Reject якщо edge має неповний набір colors або зайві/дублікати, які не узгоджуються.

10. Побудувати adjacency:

```python
adjacency = [set() for _ in range(num_vertices)]
for (u, v), colors in edge_to_colors.items():
    if colors != all_colors:
        return None
    adjacency[u].add(v)
    adjacency[v].add(u)
```

11. Повернути:

```python
return k, adjacency
```

---

## Частина 2: розпізнати Mycielski graph

Mycielski construction `M(G)` будується так.

Для графа `G` з вершинами:

```text
x_1, x_2, ..., x_n
```

створюються:

```text
X = original vertices x_1..x_n
Y = duplicate vertices y_1..y_n
z = apex vertex
```

Edges у `M(G)`:

```text
1. original edges між X, як у G
2. якщо x_i -- x_j є edge у G, тоді x_i -- y_j і y_i -- x_j
3. z з'єднаний з усіма y_i
4. між Y немає edges
5. z не з'єднаний з X
```

Властивість:

```text
chi(M(G)) = chi(G) + 1
```

Якщо стартувати з `K2`, то:

```text
K2                    -> chi = 2, vertices = 2
M(K2)                 -> chi = 3, vertices = 5
M(M(K2))              -> chi = 4, vertices = 11
M^3(K2)               -> chi = 5, vertices = 23
M^4(K2)               -> chi = 6, vertices = 47
```

Тому formula з:

```text
47 vertices
5 colors
```

є UNSAT, якщо graph справді `M^4(K2)`.

---

## Mycielski lower-bound helper

Створити helper:

```python
def mycielski_chromatic_lower_bound(adjacency: list[set[int]]) -> int | None:
    ...
```

Повернення:

```text
integer >= 2  => graph розпізнаний як Mycielski tower, lower bound на chi
None          => graph не розпізнаний, detector не застосовується
```

### Base case

Розпізнати `K2`:

```python
def is_k2(adjacency):
    return (
        len(adjacency) == 2
        and adjacency[0] == {1}
        and adjacency[1] == {0}
    )
```

Якщо `K2`, повернути:

```python
return 2
```

Можна додатково підтримати complete graph `K_n`, але для Mycielski tower з course cases достатньо `K2`.

### Recursive Mycielski recognition

Для графа `H`, який може бути `M(G)`, кількість вершин має бути непарна:

```python
len(H) = 2 * n + 1
```

Тому:

```python
m = len(adjacency)
if m % 2 == 0:
    return None
n = (m - 1) // 2
```

Далі треба знайти apex `z`.

У Mycielski graph apex має такі властивості:

```text
degree(z) = n
neighbors(z) = Y
Y є independent set
X = all other vertices
|X| = n
z не має edges до X
```

Алгоритм:

```python
for z in range(m):
    y_set = set(adjacency[z])

    if len(y_set) != n:
        continue

    if not is_independent_set(y_set, adjacency):
        continue

    x_set = set(range(m)) - y_set - {z}
    if len(x_set) != n:
        continue

    # перевірити, що z не має сусідів у X
    if adjacency[z] & x_set:
        continue

    # спробувати побудувати child graph G на X
    ...
```

### Як перевірити відповідність Y до X

У Mycielski construction кожен duplicate `y_i` має neighbors у X, які дорівнюють neighbors original vertex `x_i` у child graph `G`.

Тому треба:

1. Побудувати induced subgraph на `X`.
2. Для кожного `x in X` взяти його neighborhood всередині `X`.
3. Для кожного `y in Y` взяти його neighborhood всередині `X`.
4. Перевірити, що multisets цих neighborhoods однакові.

Псевдокод:

```python
from collections import Counter

x_list = sorted(x_set)
x_index = {old_v: i for i, old_v in enumerate(x_list)}

def normalize_subset(vertices: set[int]) -> tuple[int, ...]:
    return tuple(sorted(x_index[v] for v in vertices))

x_neighborhoods = Counter()
for x in x_list:
    nx = adjacency[x] & x_set
    x_neighborhoods[normalize_subset(nx)] += 1

y_neighborhoods = Counter()
for y in y_set:
    ny = adjacency[y] & x_set
    y_neighborhoods[normalize_subset(ny)] += 1

if x_neighborhoods != y_neighborhoods:
    continue
```

Це conservative check: якщо duplicate neighborhoods не збігаються з original neighborhoods, це не Mycielski або encoding нестандартний.

### Рекурсія

Якщо candidate `z`, `X`, `Y` пройшли перевірку, побудувати child adjacency на `X`:

```python
child_adj = [set() for _ in range(n)]
for old_u in x_list:
    u = x_index[old_u]
    for old_v in adjacency[old_u] & x_set:
        v = x_index[old_v]
        child_adj[u].add(v)
```

Потім:

```python
child_lb = mycielski_chromatic_lower_bound(child_adj)
if child_lb is not None:
    return child_lb + 1
```

Якщо жоден `z` не підходить:

```python
return None
```

---

## Основна функція detector-а

Псевдокод:

```python
def graph_coloring_mycielski_unsat(
    num_vars: int,
    clauses: list[list[int]],
) -> bool:
    parsed = parse_graph_coloring_encoding(num_vars, clauses)
    if parsed is None:
        return False

    color_count, adjacency = parsed

    lower_bound = mycielski_chromatic_lower_bound(adjacency)
    if lower_bound is None:
        return False

    return lower_bound > color_count
```

Приклад:

```text
vars = 235
colors = 5
vertices = 47
Mycielski lower_bound = 6
6 > 5 => True => return UNSAT
```

---

## Guardrails проти false UNSAT

Це найважливіша частина.

Detector повинен повертати `True` тільки якщо виконано все:

```text
1. CNF повністю відповідає graph-coloring encoding.
2. Усі variables покриті vertex-color groups.
3. Усі at-least-one clauses однакової довжини k.
4. Усі at-most-one clauses присутні для кожної вершини.
5. Усі edge clauses повні: для edge (u, v) є всі k color conflict clauses.
6. Немає clauses незрозумілого типу.
7. Побудований graph structural-recognized як Mycielski tower.
8. Mycielski lower bound > available colors.
```

Якщо будь-який пункт не проходить:

```python
return False
```

Не можна робити approximate detection, бо false `UNSAT` зламає correctness.

---

## Очікуваний ефект

До detector-а:

```text
mycielski_iter4_color5_unsat.cnf -> timeout / дуже довго
```

Після detector-а:

```text
mycielski_iter4_color5_unsat.cnf -> UNSAT за мілісекунди
```

На інших формулах detector має майже не впливати, бо він швидко повертає `False`.

---

## Smoke tests після імплементації

Обов'язково прогнати:

```bash
python3 -m py_compile satsolver.py satsolver_core.py satsolver_io.py
```

Hard target:

```bash
python3 satsolver.py cnf_training_complex__complex_cnf_hard__mycielski_iter4_color5_unsat.cnf /tmp/myc.out
cat /tmp/myc.out
```

Expected:

```text
UNSAT
```

Regression checks:

```bash
python3 satsolver.py formulae/large/test_8.cnf /tmp/test8.out
python3 satsolver.py formulae/large/test_6.cnf /tmp/test6.out
python3 satsolver.py formulae/special/hard.cnf /tmp/hard.out
```

Expected:

```text
large/test_8.cnf    SAT
large/test_6.cnf    UNSAT
special/hard.cnf    UNSAT
```

Mycielski family checks, якщо ці файли є:

```bash
python3 satsolver.py cnf_training_complex__complex_cnf_moderate__mycielski_iter2_color3_unsat.cnf /tmp/m2u.out
python3 satsolver.py cnf_training_complex__complex_cnf_moderate__mycielski_iter2_color4_sat.cnf /tmp/m2s.out
python3 satsolver.py cnf_training_complex__complex_cnf_moderate__mycielski_iter3_color4_unsat.cnf /tmp/m3u.out
python3 satsolver.py cnf_training_complex__complex_cnf_moderate__mycielski_iter3_color5_sat.cnf /tmp/m3s.out
```

Expected:

```text
iter2 color3 -> UNSAT
iter2 color4 -> SAT
iter3 color4 -> UNSAT
iter3 color5 -> SAT
```

Important: SAT Mycielski cases should **not** be incorrectly classified as UNSAT. For them detector should either return `False`, or recognize lower bound but see:

```text
lower_bound <= available_colors
```

and therefore not force UNSAT.

---

## Benchmark checks

Після smoke tests прогнати retained benchmark-и:

```bash
python benchmark_suite.py satsolver /tmp/formulae_after_mycielski.txt formulae --repeat 2 --cli-script satsolver.py
python benchmark_suite.py satsolver /tmp/course278_after_mycielski.txt course_cnf_tests --repeat 2 --cli-script satsolver.py
```

Очікування:

```text
formulae: 35/35 valid, 0 errors
course retained: 278/278 valid, 0 errors
```

Якщо є можливість, прогнати `avg5`:

```bash
python benchmark_suite.py satsolver /tmp/formulae_after_mycielski_avg5.txt formulae --repeat 5 --cli-script satsolver.py
python benchmark_suite.py satsolver /tmp/course278_after_mycielski_avg5.txt course_cnf_tests --repeat 5 --cli-script satsolver.py
```

Detector не повинен суттєво змінити час на non-Mycielski formulas.

---

## Додатковий self-test без benchmark harness

Можна додати тимчасову debug-перевірку:

```python
parsed = parse_graph_coloring_encoding(num_vars, clauses)
if parsed is not None:
    k, adjacency = parsed
    lb = mycielski_chromatic_lower_bound(adjacency)
    print("graph-coloring", "colors", k, "vertices", len(adjacency), "mycielski_lb", lb)
```

Для target case має вийти приблизно:

```text
graph-coloring colors 5 vertices 47 mycielski_lb 6
```

Перед фінальною здачею debug prints прибрати.

---

## Типові помилки

### 1. Повернути UNSAT для будь-якого graph-coloring CNF

Неправильно. Не кожен graph-coloring CNF UNSAT.

Graph-coloring SAT cases у тестах існують, наприклад planted graph coloring.

### 2. Повернути UNSAT для будь-якого Mycielski graph

Неправильно. Mycielski graph з достатньою кількістю colors є SAT.

Правильно тільки:

```python
return lower_bound > color_count
```

### 3. Не перевірити completeness edge clauses

Якщо для edge `(u, v)` є тільки частина color-conflict clauses, це не стандартне coloring encoding. Треба reject.

### 4. Плутати `num_vars` і кількість graph vertices

У coloring CNF:

```text
num_vars = graph_vertices * colors
```

Для target:

```text
235 SAT variables = 47 graph vertices * 5 colors
```

### 5. Робити detector занадто загальним

Не треба пробувати повноцінний graph coloring solver тут. Мета — вузький structural UNSAT proof для Mycielski tower.

---

## Критерій готовності

Зміна готова, якщо:

```text
1. py_compile проходить.
2. mycielski_iter4_color5_unsat.cnf повертає UNSAT дуже швидко.
3. formulae/ залишається 35/35 valid.
4. course retained benchmark залишається 278/278 valid.
5. SAT Mycielski cases не стають false UNSAT.
6. Немає debug prints у фінальному output.
```

---

## Коротке формулювання для PDF/report

Можна описати так:

> Solver contains a conservative structural detector for graph-coloring encodings of Mycielski graphs. It reconstructs the graph from standard vertex-color clauses, recognizes recursive Mycielski construction, derives a chromatic-number lower bound, and returns UNSAT only when the available number of colors is smaller than this bound. Otherwise it falls back to the regular CDCL solver.

Українською:

> Solver має conservative structural detector для graph-coloring CNF формул на Mycielski graphs. Detector відновлює граф зі стандартного encoding-а, рекурсивно розпізнає Mycielski-конструкцію, обчислює нижню межу хроматичного числа і повертає UNSAT лише тоді, коли доступних кольорів менше за цю межу. В усіх інших випадках формула передається звичайному CDCL solver-у.
