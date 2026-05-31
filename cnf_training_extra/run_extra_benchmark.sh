#!/usr/bin/env bash
set -euo pipefail
python benchmark_suite.py satsolver /tmp/bench_extra.txt extra_cnf --bruteforce-var-limit 16 --cli-script satsolver.py
cat /tmp/bench_extra.txt
