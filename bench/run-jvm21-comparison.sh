#!/usr/bin/env bash
set -euo pipefail

ROOT=$(cd "$(dirname "$0")/.." && pwd)
JAR=${JAR:-"$ROOT/lisa-hol/target/scala-3.7.2/lisa-hol-assembly-0.9.3.jar"}
OPENJDK_JAVA=${OPENJDK_JAVA:-/usr/lib/jvm/java-21-openjdk/bin/java}
GRAALVM_JAVA=${GRAALVM_JAVA:-/usr/lib/jvm/java-21-graalvm/bin/java}
GRAALVM_EE_JAVA=${GRAALVM_EE_JAVA:-/usr/lib/jvm/java-21-graalvm-ee/bin/java}
RUNS=${RUNS:-5}
WARMUPS=${WARMUPS:-1}
HOL_SIZES=${HOL_SIZES:-"10 50 100"}
JVM_HEAP_MIN=${JVM_HEAP_MIN:-256m}
JVM_HEAP_MAX=${JVM_HEAP_MAX:-4g}
CLK_TCK=$(getconf CLK_TCK)
STAMP=$(date +%Y%m%d-%H%M%S)
REV=$(git -C "$ROOT" rev-parse --short HEAD)
OUT=${OUT:-"$ROOT/target/jvm21-benchmarks/$STAMP-$REV"}

: "${HOL_PREFIX:?Set HOL_PREFIX to the HOL export prefix (without .proofs/.theorems/.names)}"

RUNTIMES=(openjdk graalvm-ce graalvm-ee)

for path in "$JAR" "$OPENJDK_JAVA" "$GRAALVM_JAVA" "$GRAALVM_EE_JAVA"; do
  [[ -e "$path" ]] || { echo "Missing required path: $path" >&2; exit 2; }
done
for suffix in proofs theorems names; do
  [[ -f "$HOL_PREFIX.$suffix" ]] || { echo "Missing $HOL_PREFIX.$suffix" >&2; exit 2; }
done

mkdir -p "$OUT/logs" "$OUT/times"

{
  echo "revision=$REV"
  echo "jar=$JAR"
  echo "jar_sha256=$(sha256sum "$JAR" | cut -d ' ' -f 1)"
  echo "hol_prefix=$HOL_PREFIX"
  echo "hol_sizes=$HOL_SIZES"
  echo "runs=$RUNS"
  echo "warmups=$WARMUPS"
  echo "jvm_heap_min=$JVM_HEAP_MIN"
  echo "jvm_heap_max=$JVM_HEAP_MAX"
  echo "date=$(date --iso-8601=seconds)"
  echo "uname=$(uname -a)"
  echo "cpu=$(lscpu | awk -F: '/Model name/ { sub(/^[[:space:]]+/, "", $2); print $2; exit }')"
  echo "openjdk_java=$OPENJDK_JAVA"
  "$OPENJDK_JAVA" -version 2>&1
  echo "graalvm_java=$GRAALVM_JAVA"
  "$GRAALVM_JAVA" -version 2>&1
  echo "graalvm_ee_java=$GRAALVM_EE_JAVA"
  "$GRAALVM_EE_JAVA" -version 2>&1
  echo
  echo "worktree:"
  git -C "$ROOT" status --short
} > "$OUT/environment.txt"

echo "runtime,workload,size,run,wall_seconds,user_seconds,system_seconds,max_rss_kb" > "$OUT/results.csv"

java_for() {
  case "$1" in
    openjdk) echo "$OPENJDK_JAVA" ;;
    graalvm-ce) echo "$GRAALVM_JAVA" ;;
    graalvm-ee) echo "$GRAALVM_EE_JAVA" ;;
    *) echo "Unknown runtime: $1" >&2; exit 2 ;;
  esac
}

run_once() {
  local runtime=$1
  local workload=$2
  local size=$3
  local run=$4
  local measured=$5
  local java
  local main
  local label
  local args=()
  local timing
  local log
  local started
  local finished
  local pid
  local exit_code
  local peak_rss=0
  local user_ticks=0
  local system_ticks=0

  java=$(java_for "$runtime")
  if [[ "$workload" == "library" ]]; then
    main=lisa.maths.SetTheory.Ordinals.TransfiniteRecursion
    label="$runtime-library-$run"
  else
    main=lisa.hol.ImportBenchmark
    args=("$HOL_PREFIX" "$size")
    label="$runtime-hol-$size-$run"
  fi
  timing="$OUT/times/$label.time"
  log="$OUT/logs/$label.log"

  started=$(date +%s%N)
  "$java" "-Xms$JVM_HEAP_MIN" "-Xmx$JVM_HEAP_MAX" -cp "$JAR" "$main" "${args[@]}" \
    > "$log" 2>&1 &
  pid=$!

  while [[ -r "/proc/$pid/status" ]]; do
    local key value unit
    while read -r key value unit; do
      if [[ "$key" == "VmHWM:" ]] && ((value > peak_rss)); then peak_rss=$value; fi
    done < "/proc/$pid/status"

    if [[ -r "/proc/$pid/stat" ]]; then
      local stat
      read -r -a stat < "/proc/$pid/stat"
      user_ticks=${stat[13]}
      system_ticks=${stat[14]}
    fi
    sleep 0.05
  done

  set +e
  wait "$pid"
  exit_code=$?
  set -e
  finished=$(date +%s%N)

  if ((exit_code != 0)); then
    echo "$label exited with status $exit_code; see $log" >&2
    exit "$exit_code"
  fi

  local wall user system
  wall=$(awk -v started="$started" -v finished="$finished" 'BEGIN { printf "%.6f", (finished - started) / 1000000000 }')
  user=$(awk -v ticks="$user_ticks" -v hz="$CLK_TCK" 'BEGIN { printf "%.6f", ticks / hz }')
  system=$(awk -v ticks="$system_ticks" -v hz="$CLK_TCK" 'BEGIN { printf "%.6f", ticks / hz }')
  echo "$wall,$user,$system,$peak_rss" > "$timing"

  if grep -q '\[ERROR\]' "$log"; then
    echo "Import error in $label; see $log" >&2
    exit 1
  fi

  if [[ "$measured" == true ]]; then
    local rss
    IFS=, read -r wall user system rss < "$timing"
    echo "$runtime,$workload,$size,$run,$wall,$user,$system,$rss" >> "$OUT/results.csv"
  fi
}

precondition_workload() {
  local workload=$1
  local size=$2
  local warmup
  local runtime

  for ((warmup = 1; warmup <= WARMUPS; warmup++)); do
    for runtime in "${RUNTIMES[@]}"; do
      echo "Warmup: $runtime $workload ${size:+size=$size} ($warmup/$WARMUPS)"
      run_once "$runtime" "$workload" "$size" "warmup-$warmup" false
    done
  done
}

measure_workload() {
  local workload=$1
  local size=$2
  local run
  local position
  local runtime

  for ((run = 1; run <= RUNS; run++)); do
    for ((position = 0; position < ${#RUNTIMES[@]}; position++)); do
      runtime=${RUNTIMES[$(((run - 1 + position) % ${#RUNTIMES[@]}))]}
      echo "Measure: $runtime $workload ${size:+size=$size} ($run/$RUNS)"
      run_once "$runtime" "$workload" "$size" "$run" true
    done
  done
}

# Complete one or more unmeasured passes first, keeping measured runs out of the
# machine/cache/thermal warm-up phase.
precondition_workload library ""
for size in $HOL_SIZES; do
  precondition_workload hol "$size"
done

measure_workload library ""
for size in $HOL_SIZES; do
  measure_workload hol "$size"
done

{
  echo "runtime workload size runs min_s median_s mean_s max_s mean_rss_kb"
  tail -n +2 "$OUT/results.csv" |
    sort -t, -k1,1 -k2,2 -k3,3n |
    awk -F, '
      function flush(   i, middle, mean, rss_mean) {
        if (n == 0) return
        for (i = 1; i <= n; i++) sorted[i] = walls[i]
        for (i = 2; i <= n; i++) {
          value = sorted[i]
          j = i - 1
          while (j >= 1 && sorted[j] > value) { sorted[j + 1] = sorted[j]; j-- }
          sorted[j + 1] = value
        }
        if (n % 2) middle = sorted[(n + 1) / 2]
        else middle = (sorted[n / 2] + sorted[n / 2 + 1]) / 2
        mean = sum / n
        rss_mean = rss_sum / n
        printf "%s %s %s %d %.3f %.3f %.3f %.3f %.0f\n", runtime, workload, size, n, sorted[1], middle, mean, sorted[n], rss_mean
        delete walls
        delete sorted
        n = 0
        sum = 0
        rss_sum = 0
      }
      {
        key = $1 SUBSEP $2 SUBSEP $3
        if (previous != "" && key != previous) flush()
        runtime = $1
        workload = $2
        size = $3
        walls[++n] = $5
        sum += $5
        rss_sum += $8
        previous = key
      }
      END { flush() }
    '
} > "$OUT/summary.txt"

cat "$OUT/summary.txt"
echo "Results: $OUT"
