#!/usr/bin/env bash
set -u

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PYTHON_BIN="${PYTHON:-python}"
SOLVER="$ROOT_DIR/satsolver.py"
CNF_DIR="$ROOT_DIR/cnf_tests/assignment_safe"
OUT_DIR="${1:-$ROOT_DIR/run_35_results}"
RESULT_DIR="$OUT_DIR/outputs"
REPORT="$OUT_DIR/timing_35.txt"

mkdir -p "$RESULT_DIR"

{
    echo "solver=$SOLVER"
    echo "python=$PYTHON_BIN"
    echo "cnf_dir=$CNF_DIR"
    echo "output_dir=$OUT_DIR"
    echo
    printf "%-42s %-6s %-8s %10s\n" "case" "status" "answer" "time_s"
    printf "%-42s %-6s %-8s %10s\n" "----" "------" "------" "------"
} > "$REPORT"

total_ns=0
count=0
ok_count=0
fail_count=0

run_case() {
    local group="$1"
    local name="$2"
    local input="$CNF_DIR/course_cnf_tests__${group}__${name}.cnf"
    local output="$RESULT_DIR/${group}__${name}.txt"
    local label="${group}/${name}.cnf"
    local start_ns
    local end_ns
    local elapsed_ns
    local elapsed_s
    local status
    local answer

    if [[ ! -f "$input" ]]; then
        printf "%-42s %-6s %-8s %10s\n" "$label" "FAIL" "missing" "-" | tee -a "$REPORT"
        fail_count=$((fail_count + 1))
        return
    fi

    start_ns="$(date +%s%N)"
    "$PYTHON_BIN" "$SOLVER" "$input" "$output" >/dev/null
    status=$?
    end_ns="$(date +%s%N)"

    elapsed_ns=$((end_ns - start_ns))
    elapsed_s="$(awk -v ns="$elapsed_ns" 'BEGIN { printf "%.4f", ns / 1000000000 }')"
    total_ns=$((total_ns + elapsed_ns))
    count=$((count + 1))

    if [[ $status -eq 0 ]]; then
        ok_count=$((ok_count + 1))
        answer="$(head -n 1 "$output" 2>/dev/null || true)"
        [[ -n "$answer" ]] || answer="empty"
        printf "%-42s %-6s %-8s %10s\n" "$label" "OK" "$answer" "$elapsed_s" | tee -a "$REPORT"
    else
        fail_count=$((fail_count + 1))
        printf "%-42s %-6s %-8s %10s\n" "$label" "FAIL" "error" "$elapsed_s" | tee -a "$REPORT"
    fi
}

for i in {1..10}; do
    run_case "small" "test_$i"
done

for i in {1..10}; do
    run_case "medium" "test_$i"
done

for i in {1..10}; do
    run_case "large" "test_$i"
done

for name in dense easy hard pigeonhole tseitin; do
    run_case "special" "$name"
done

total_s="$(awk -v ns="$total_ns" 'BEGIN { printf "%.4f", ns / 1000000000 }')"
avg_s="$(awk -v ns="$total_ns" -v n="$count" 'BEGIN { if (n > 0) printf "%.4f", ns / 1000000000 / n; else printf "0.0000" }')"

{
    echo
    echo "summary:"
    echo "cases=$count"
    echo "ok=$ok_count"
    echo "failed=$fail_count"
    echo "total_time_s=$total_s"
    echo "avg_time_s=$avg_s"
    echo "report=$REPORT"
    echo "outputs=$RESULT_DIR"
} | tee -a "$REPORT"

if [[ $fail_count -ne 0 ]]; then
    exit 1
fi
