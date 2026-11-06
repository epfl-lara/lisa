#!/usr/bin/env bash
# Exercise the trace sorter on small fixtures, including external-sort spills.
set -euo pipefail

root=$(cd "$(dirname "$0")/.." && pwd)
work_dir=$(mktemp -d)
cleanup() {
  # Remove only this test's fresh temporary directory.
  rm -rf -- "$work_dir"
}
trap cleanup EXIT

prefix="$work_dir/input with spaces"
printf '%s\n' \
  '{"id": 9223372036854775807, "pr": {"text": "λ, : \\n"}}' \
  '{"id": 10, "pr": {}}' \
  '{"id": 2, "pr": {}}' \
  '{"id": 9007199254740993, "pr": {}}' \
  '{"id": 9007199254740992, "pr": {}}' > "$prefix.proofs"
printf '%s\n' \
  '{"id": 9007199254740992, "th": {}}' \
  '{"id": 2, "th": {}}' \
  '{"id": 10, "th": {}}' \
  '{"id": 9223372036854775807, "th": {}}' \
  '{"id": 9007199254740993, "th": {}}' > "$prefix.theorems"
printf '%s\n' \
  '{"id": 10, "nm": "ten"}' \
  '{"id": 2, "nm": "two"}' \
  '{"id": 2, "nm": "alias"}' > "$prefix.names"

before=$(sha256sum "$prefix.proofs" "$prefix.theorems" "$prefix.names")
bash "$root/sort-hol-traces.sh" "$prefix"
[[ "$before" == "$(sha256sum "$prefix.proofs" "$prefix.theorems" "$prefix.names")" ]]
{
  sed -n '3p' "$prefix.proofs"
  sed -n '2p' "$prefix.proofs"
  sed -n '5p' "$prefix.proofs"
  sed -n '4p' "$prefix.proofs"
  sed -n '1p' "$prefix.proofs"
} > "$work_dir/expected"
cmp "$work_dir/expected" "$prefix.sorted.proofs"
{ sed -n '2,3p' "$prefix.names"; sed -n '1p' "$prefix.names"; } > "$work_dir/expected"
cmp "$work_dir/expected" "$prefix.sorted.names"
if bash "$root/sort-hol-traces.sh" "$prefix"; then echo "Overwrote existing output" >&2; exit 1; fi

# Invalid or mismatched inputs must not publish any member of the output set.
for failure in duplicate mismatch invalid; do
  case "$failure" in
    duplicate) printf '%s\n' '{"id": 2, "pr": {}}' >> "$prefix.proofs" ;;
    mismatch) printf '%s\n' '{"id": 3, "pr": {}}' > "$prefix.proofs" ;;
    invalid) printf '%s\n' '{"id": -1, "pr": {}}' > "$prefix.proofs" ;;
  esac
  if bash "$root/sort-hol-traces.sh" "$prefix" "$work_dir/$failure"; then
    echo "Accepted $failure input" >&2; exit 1
  fi
  for suffix in proofs theorems names; do [[ ! -e "$work_dir/$failure.$suffix" ]]; done
done

for suffix in proofs theorems names; do : > "$prefix.$suffix"; done
bash "$root/sort-hol-traces.sh" "$prefix" "$work_dir/empty"
for suffix in proofs theorems names; do [[ ! -s "$work_dir/empty.$suffix" ]]; done

# Use a tiny sort buffer to exercise disk-backed runs.
awk 'BEGIN { for (i = 10000; i >= 0; i--) printf "{\"id\": %d, \"value\": \"record\"}\n", i }' > "$prefix.proofs"
cp -- "$prefix.proofs" "$prefix.theorems"
cp -- "$prefix.proofs" "$prefix.names"
mkdir "$work_dir/scratch"
SORT_BUFFER_SIZE=16K SORT_TMPDIR="$work_dir/scratch" bash "$root/sort-hol-traces.sh" "$prefix" "$work_dir/spilled"
awk -F '[:,]' '($2 + 0) != NR - 1 { exit 1 } END { if (NR != 10001) exit 1 }' "$work_dir/spilled.proofs"
echo "Trace sorter tests passed."
