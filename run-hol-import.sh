#!/usr/bin/env bash
set -euo pipefail

[[ $# == 1 ]] || { echo "Usage: $0 <count|all>" >&2; exit 2; }

ROOT=$(cd "$(dirname "$0")" && pwd)
PREFIX=${HOL_PREFIX:-/home/sankalp/projects/lisa/jar-26/hol-light/ProofTrace/cleaned}
COUNT=$1

for suffix in proofs theorems names; do
  [[ -f "$PREFIX.$suffix" ]] || { echo "Missing $PREFIX.$suffix" >&2; exit 2; }
done

if [[ "$COUNT" == all ]]; then
  COUNT=$(awk 'END { print NR }' "$PREFIX.names")
elif [[ ! "$COUNT" =~ ^[1-9][0-9]*$ ]]; then
  echo "Count must be a positive integer or 'all'." >&2
  exit 2
fi

cd "$ROOT"
exec sbt --client "lisa-hol/runMain lisa.hol.ImportBenchmark $PREFIX $COUNT"
