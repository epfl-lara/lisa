#!/usr/bin/env bash
#
# CASC portfolio launcher for the Lisa superposition prover.
#
# Runs all eight strategies of `Strategy.portfolio` concurrently — one `java -jar casc-prover.jar --strategy <s>`
# process per core (separate processes, NOT threads: four strategies run orthologic normalisation through the
# kernel's non-thread-safe OL checker, so they must not share a JVM). The first worker to emit a definitive SZS
# status (Theorem / Unsatisfiable / Satisfiable / CounterSatisfiable) wins: its full output — status line and the
# CNFRefutation — is printed verbatim, the others are killed. If none succeeds within the budget, prints GaveUp.
#
# Usage:  casc-portfolio.sh [-t <seconds>] <problem.p>
#   -t   wall-clock budget in seconds (default 300). Each worker is given the budget minus a small margin; the
#        launcher also stops everything at the budget as a hard backstop.
# Env:
#   CASC_JAR   path to casc-prover.jar (default: next to this script, else the repo build output).
#   TPTP       TPTP root (needed for problems with include(...) directives); inherited by the workers.

set -u

STRATEGIES=(balanced weight-greedy age-fair occurrence equational unary-redundancy subsumption-light first-negative)

here="$(cd "$(dirname "$(readlink -f "$0")")" && pwd)"

# ---- locate the jar ----
JAR="${CASC_JAR:-}"
if [ -z "$JAR" ]; then
  for cand in "$here/casc-prover.jar" "$here"/../../../../../../target/scala-*/casc-prover.jar; do
    [ -f "$cand" ] && JAR="$cand" && break
  done
fi
if [ -z "$JAR" ] || [ ! -f "$JAR" ]; then
  echo "casc-portfolio: cannot find casc-prover.jar (set CASC_JAR)" >&2; exit 2
fi

# ---- parse args ----
limit=300
problem=""
while [ $# -gt 0 ]; do
  case "$1" in
    -t|--cpu-limit|--wc-limit) limit="$2"; shift 2 ;;
    *) problem="$1"; shift ;;
  esac
done
if [ -z "$problem" ]; then echo "usage: $(basename "$0") [-t <seconds>] <problem.p>" >&2; exit 2; fi

name="$(basename "$problem")"
ncores="$(nproc 2>/dev/null || echo 8)"
nworkers=${#STRATEGIES[@]}
wlimit=$(( limit > 5 ? limit - 3 : limit ))   # worker solve budget (leave margin for startup + output)
has_taskset=0; command -v taskset >/dev/null 2>&1 && has_taskset=1

# ---- per-worker heap cap ----
# The N workers are separate JVMs; without a cap each grabs the default max heap (~25% of RAM) and N of them OOM.
# Split ~80% of *currently-available* RAM across the workers (so it scales to the machine and coexists with other
# load), floored at 1G and capped at 12G. Override with CASC_XMX (e.g. CASC_XMX=4g).
xmx="${CASC_XMX:-}"
if [ -z "$xmx" ]; then
  avail_mb="$(free -m 2>/dev/null | awk 'NR==2{print $7}')"; [ -z "${avail_mb:-}" ] && avail_mb=8192
  per=$(( avail_mb * 80 / 100 / nworkers ))
  [ "$per" -lt 1024 ] && per=1024
  [ "$per" -gt 12288 ] && per=12288
  xmx="${per}m"
fi

tmp="$(mktemp -d)"
pids=()
cleanup() { for p in "${pids[@]:-}"; do kill "$p" 2>/dev/null; done; rm -rf "$tmp"; }
trap cleanup EXIT INT TERM

# ---- spawn one pinned worker per strategy ----
i=0
for strat in "${STRATEGIES[@]}"; do
  core=$(( i % ncores ))
  if [ "$has_taskset" -eq 1 ]; then
    taskset -c "$core" java -Xmx"$xmx" -jar "$JAR" --strategy "$strat" -t "$wlimit" "$problem" >"$tmp/out.$i" 2>/dev/null &
  else
    java -Xmx"$xmx" -jar "$JAR" --strategy "$strat" -t "$wlimit" "$problem" >"$tmp/out.$i" 2>/dev/null &
  fi
  pids+=($!)
  i=$(( i + 1 ))
done

# ---- poll for the first definitive answer, or until all workers exit / the budget elapses ----
winner=""
while :; do
  for j in "${!STRATEGIES[@]}"; do
    if grep -qE '^% SZS status (Theorem|Unsatisfiable|Satisfiable|CounterSatisfiable) ' "$tmp/out.$j" 2>/dev/null; then
      winner="$j"; break
    fi
  done
  [ -n "$winner" ] && break
  alive=0; for p in "${pids[@]}"; do kill -0 "$p" 2>/dev/null && { alive=1; break; }; done
  [ "$alive" -eq 0 ] && break
  [ "$SECONDS" -ge "$limit" ] && break
  sleep 0.1
done

# ---- resolve ----
if [ -n "$winner" ]; then
  wp="${pids[$winner]}"
  for j in "${!pids[@]}"; do [ "$j" != "$winner" ] && kill "${pids[$j]}" 2>/dev/null; done
  wait "$wp" 2>/dev/null   # let the winner finish writing its CNFRefutation
  cat "$tmp/out.$winner"
else
  echo "% SZS status GaveUp for $name"
fi
