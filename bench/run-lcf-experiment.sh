#!/usr/bin/env bash
set -euo pipefail

ROOT=$(cd "$(dirname "$0")/.." && pwd)
RUNS=${RUNS:-5}
WARMUPS=${WARMUPS:-1}
THEOREM_COUNT=${THEOREM_COUNT:-100}
TARGET=${1:-all}
STAMP=$(date +%Y%m%d-%H%M%S)
REV=$(git -C "$ROOT" rev-parse --short HEAD)
OUT=${OUT:-"$ROOT/target/lcf-benchmarks/$STAMP-$REV"}

mkdir -p "$OUT"

case "$TARGET" in
  all|transfinite|hol) ;;
  *) echo "Usage: $0 [all|transfinite|hol]" >&2; exit 2 ;;
esac

if [[ "$TARGET" == all || "$TARGET" == hol ]]; then
  : "${HOL_PREFIX:?Set HOL_PREFIX to the HOL export prefix (without .proofs/.theorems/.names)}"
  for suffix in proofs theorems names; do
    [[ -f "$HOL_PREFIX.$suffix" ]] || { echo "Missing $HOL_PREFIX.$suffix" >&2; exit 2; }
  done
fi

cat > "$OUT/environment.txt" <<EOF
revision=$REV
target=$TARGET
runs=$RUNS
warmups=$WARMUPS
theorem_count=$THEOREM_COUNT
hol_prefix=${HOL_PREFIX:-}
date=$(date --iso-8601=seconds)
uname=$(uname -a)
EOF
git -C "$ROOT" status --short >> "$OUT/environment.txt"
java -version 2>> "$OUT/environment.txt"
uptime >> "$OUT/environment.txt"
free -b >> "$OUT/environment.txt"

run_sbt() {
  sbt --client "$1"
}

summarize() {
  local samples=$1
  local sorted="$samples.sorted"
  sort -n "$samples" > "$sorted"
  awk '
    { values[NR] = $1; sum += $1 }
    END {
      if (NR % 2) median = values[(NR + 1) / 2]
      else median = (values[NR / 2] + values[NR / 2 + 1]) / 2
      printf "runs=%d min=%.3fs median=%.3fs mean=%.3fs max=%.3fs\n", NR, values[1], median, sum / NR, values[NR]
    }
  ' "$sorted"
}

benchmark() {
  local name=$1
  local command=$2
  local reject=${3:-}
  local samples="$OUT/$name.seconds"
  : > "$samples"

  for ((i = 1; i <= WARMUPS; i++)); do
    run_sbt "$command" > "$OUT/$name-warmup-$i.log" 2>&1
  done

  for ((i = 1; i <= RUNS; i++)); do
    local timing="$OUT/$name-$i.time"
    local log="$OUT/$name-$i.log"
    local state="$OUT/$name-$i.host"
    local started finished
    {
      date --iso-8601=ns
      cat /proc/loadavg
      free -b
    } > "$state"
    started=$(date +%s%N)
    sbt --client "$command" > "$log" 2>&1
    finished=$(date +%s%N)
    {
      date --iso-8601=ns
      cat /proc/loadavg
      free -b
    } >> "$state"
    awk -v started="$started" -v finished="$finished" 'BEGIN { printf "%.6f\n", (finished - started) / 1000000000 }' > "$timing"
    if [[ -n "$reject" ]] && grep -q "$reject" "$log"; then
      echo "$name run $i failed; see $log" >&2
      exit 1
    fi
    cat "$timing" >> "$samples"
  done

  printf '%s: ' "$name" | tee -a "$OUT/summary.txt"
  summarize "$samples" | tee -a "$OUT/summary.txt"
}

cd "$ROOT"

case "$TARGET" in
  all) run_sbt 'lisa-sets/compile; lisa-hol/compile' > "$OUT/compile.log" 2>&1 ;;
  transfinite) run_sbt 'lisa-sets/compile' > "$OUT/compile.log" 2>&1 ;;
  hol) run_sbt 'lisa-hol/compile' > "$OUT/compile.log" 2>&1 ;;
esac

if [[ "$TARGET" == all || "$TARGET" == transfinite ]]; then
  benchmark transfinite 'lisa-sets/runMain lisa.maths.SetTheory.Ordinals.TransfiniteRecursion'
fi

if [[ "$TARGET" == all || "$TARGET" == hol ]]; then
  benchmark hol-import-100 "lisa-hol/runMain lisa.hol.ImportBenchmark $HOL_PREFIX $THEOREM_COUNT" '\[ERROR\]'
fi

echo "Results: $OUT"
