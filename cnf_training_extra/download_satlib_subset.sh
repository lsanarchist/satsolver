#!/usr/bin/env bash
set -euo pipefail

# Run from the SAT solver repository root. Downloads a manageable SATLIB subset into satlib_downloaded/.
# Requires: curl, tar.

out_dir="${1:-satlib_downloaded}"
mkdir -p "$out_dir/_archives" "$out_dir"

urls=(
  "https://www.cs.ubc.ca/~hoos/SATLIB/Benchmarks/SAT/RND3SAT/uf20-91.tar.gz"
  "https://www.cs.ubc.ca/~hoos/SATLIB/Benchmarks/SAT/RND3SAT/uf50-218.tar.gz"
  "https://www.cs.ubc.ca/~hoos/SATLIB/Benchmarks/SAT/RND3SAT/uuf50-218.tar.gz"
  "https://www.cs.ubc.ca/~hoos/SATLIB/Benchmarks/SAT/GCP/flat30-60.tar.gz"
  "https://www.cs.ubc.ca/~hoos/SATLIB/Benchmarks/SAT/AIS/ais.tar.gz"
)

for url in "${urls[@]}"; do
  name="$(basename "$url")"
  echo "Downloading $name"
  curl -L --fail "$url" -o "$out_dir/_archives/$name"
  tmp="$(mktemp -d)"
  tar -xzf "$out_dir/_archives/$name" -C "$tmp"
  find "$tmp" -type f -name '*.cnf' -print0 | while IFS= read -r -d '' f; do
    cp "$f" "$out_dir/$(basename "$f")"
  done
  rm -rf "$tmp"
done

echo "Downloaded $(find "$out_dir" -maxdepth 1 -type f -name '*.cnf' | wc -l | tr -d ' ') CNF files into $out_dir"
echo "Benchmark with: python benchmark_suite.py satsolver /tmp/bench_satlib_downloaded.txt $out_dir --bruteforce-var-limit 16 --cli-script satsolver.py"
