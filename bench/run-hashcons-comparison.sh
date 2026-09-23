#!/usr/bin/env bash
set -euo pipefail

ROOT=$(cd "$(dirname "$0")/.." && pwd)
JAR=${JAR:-"$ROOT/lisa-hol/target/scala-3.7.2/lisa-hol-assembly-0.9.3.jar"}
JAVA=${JAVA:-/usr/lib/jvm/java-21-openjdk/bin/java}
HOL_PREFIX=${HOL_PREFIX:-/home/sankalp/projects/lisa/jar-26/hol-light/ProofTrace/cleaned}
RUNS=${RUNS:-3}
WARMUPS=${WARMUPS:-1}
JVM_HEAP_MIN=${JVM_HEAP_MIN:-512m}
JVM_HEAP_MAX=${JVM_HEAP_MAX:-10g}
STAMP=$(date +%Y%m%d-%H%M%S)
REV=$(git -C "$ROOT" rev-parse --short HEAD)
OUT=${OUT:-"$ROOT/target/hashcons-benchmarks/$STAMP-$REV"}

MODES=(bounded-1g bounded-2g hybrid-2g)
WORKLOADS=(library hol-100 hol-200)

for path in "$JAR" "$JAVA"; do
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
  echo "java=$JAVA"
  "$JAVA" -version 2>&1
  echo "hol_prefix=$HOL_PREFIX"
  echo "runs=$RUNS"
  echo "warmups=$WARMUPS"
  echo "jvm_heap_min=$JVM_HEAP_MIN"
  echo "jvm_heap_max=$JVM_HEAP_MAX"
  echo "composite_entries_per_generation=1048576"
  echo "date=$(date --iso-8601=seconds)"
  echo "cpu=$(lscpu | awk -F: '/Model name/ { sub(/^[[:space:]]+/, "", $2); print $2; exit }')"
} > "$OUT/environment.txt"

echo "mode,workload,size,run,wall_seconds,user_seconds,system_seconds,max_rss_kb" > "$OUT/results.csv"

run_once() {
  local mode=$1
  local workload=$2
  local run=$3
  local measured=$4
  local size=""
  local main
  local label
  local log
  local timing
  local options=("-Xms$JVM_HEAP_MIN" "-Xmx$JVM_HEAP_MAX")
  local args=()

  case "$mode" in
    full) options+=("-Dlisa.hashcons.mode=bounded" "-Dlisa.hashcons.max=2147483647") ;;
    bounded|bounded-2g) options+=("-Dlisa.hashcons.mode=bounded" "-Dlisa.hashcons.max=1048576" "-Dlisa.hashcons.generations=2") ;;
    bounded-1g) options+=("-Dlisa.hashcons.mode=bounded" "-Dlisa.hashcons.max=1048576" "-Dlisa.hashcons.generations=1") ;;
    ids) options+=("-Dlisa.hashcons.mode=ids") ;;
    hybrid|hybrid-2g) options+=("-Dlisa.hashcons.mode=hybrid" "-Dlisa.hashcons.max=1048576" "-Dlisa.hashcons.generations=2") ;;
    hybrid-1g) options+=("-Dlisa.hashcons.mode=hybrid" "-Dlisa.hashcons.max=1048576" "-Dlisa.hashcons.generations=1") ;;
    off) options+=("-Dlisa.hashcons=false") ;;
    *) echo "Unknown mode: $mode" >&2; exit 2 ;;
  esac

  case "$workload" in
    library)
      main=lisa.maths.SetTheory.Ordinals.TransfiniteRecursion
      ;;
    hol-*)
      size=${workload#hol-}
      main=lisa.hol.ImportBenchmark
      args=("$HOL_PREFIX" "$size")
      ;;
    *) echo "Unknown workload: $workload" >&2; exit 2 ;;
  esac

  label="$mode-$workload-$run"
  log="$OUT/logs/$label.log"
  timing="$OUT/times/$label.csv"

  /usr/bin/time -f "$mode,$workload,$size,$run,%e,%U,%S,%M" -o "$timing" \
    "$JAVA" "${options[@]}" -cp "$JAR" "$main" "${args[@]}" > "$log" 2>&1

  if grep -Eq '\[ERROR\]|Exception|StepMismatch' "$log"; then
    echo "Proof error in $label; see $log" >&2
    exit 1
  fi

  if [[ "$measured" == true ]]; then
    cat "$timing" >> "$OUT/results.csv"
  fi
}

for workload in "${WORKLOADS[@]}"; do
  for ((warmup = 1; warmup <= WARMUPS; warmup++)); do
    for mode in "${MODES[@]}"; do
      echo "Warmup: $mode $workload ($warmup/$WARMUPS)"
      run_once "$mode" "$workload" "warmup-$warmup" false
    done
  done

  for ((run = 1; run <= RUNS; run++)); do
    for ((position = 0; position < ${#MODES[@]}; position++)); do
      mode=${MODES[$(((run - 1 + position) % ${#MODES[@]}))]}
      echo "Measure: $mode $workload ($run/$RUNS)"
      run_once "$mode" "$workload" "$run" true
    done
  done
done

{
  echo "mode,workload,runs,min_wall_seconds,median_wall_seconds,mean_wall_seconds,max_wall_seconds,mean_max_rss_kb"
  awk -F, '
    NR > 1 {
      key = $1 FS $2
      n[key]++
      wall[key, n[key]] = $5
      rss[key, n[key]] = $8
      sumWall[key] += $5
      sumRss[key] += $8
    }
    END {
      for (key in n) {
        count = n[key]
        for (i = 1; i <= count; i++) {
          for (j = i + 1; j <= count; j++) {
            if (wall[key, j] < wall[key, i]) {
              value = wall[key, i]; wall[key, i] = wall[key, j]; wall[key, j] = value
            }
          }
        }
        median = count % 2 ? wall[key, (count + 1) / 2] : (wall[key, count / 2] + wall[key, count / 2 + 1]) / 2
        split(key, fields, FS)
        printf "%s,%s,%d,%.3f,%.3f,%.3f,%.3f,%.0f\n", fields[1], fields[2], count, wall[key, 1], median, sumWall[key] / count, wall[key, count], sumRss[key] / count
      }
    }
  ' "$OUT/results.csv" | sort -t, -k2,2 -k1,1
} > "$OUT/summary.csv"

echo "Results: $OUT"
