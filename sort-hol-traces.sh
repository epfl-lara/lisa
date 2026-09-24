#!/usr/bin/env bash
set -euo pipefail
export LC_ALL=C

if (( $# < 1 || $# > 2 )); then
  echo "Usage: $0 <input-prefix> [output-prefix]" >&2
  echo "Default output: <input-prefix>.sorted.{proofs,theorems,names}" >&2
  echo "Options: SORT_BUFFER_SIZE=256M SORT_PARALLEL=1 SORT_TMPDIR=<directory>" >&2
  exit 2
fi

input=$1
output=${2:-$input.sorted}
suffixes=(proofs theorems names)

for suffix in "${suffixes[@]}"; do
  [[ -f "$input.$suffix" && -r "$input.$suffix" ]] || { echo "Cannot read $input.$suffix" >&2; exit 2; }
  [[ ! -e "$output.$suffix" && ! -L "$output.$suffix" ]] || { echo "Refusing to overwrite $output.$suffix" >&2; exit 2; }
done

# Stage all three outputs beside their destinations. GNU sort spills runs to disk.
mkdir -p -- "$(dirname -- "$output")"
work_dir=$(mktemp -d -- "$(dirname -- "$output")/.hol-sort.XXXXXXXX")
cleanup() {
  rm -f -- "$work_dir/proofs" "$work_dir/theorems" "$work_dir/names" \
    "$work_dir/proofs.ids" "$work_dir/theorems.ids" "$work_dir/names.ids"
  rmdir -- "$work_dir"
}
trap cleanup EXIT
trap 'exit 130' INT
trap 'exit 143' TERM

for suffix in "${suffixes[@]}"; do
  echo "Sorting $input.$suffix ..." >&2

  # Extract the key as text: do not round 64-bit IDs through floating point,
  # parse large term payloads, or change the original JSON representation.
  awk '
    !match($0, /^[[:space:]]*\{[[:space:]]*"id"[[:space:]]*:[[:space:]]*[0-9]+[[:space:]]*,/) {
      print "Expected an integer id as the first field at line " NR > "/dev/stderr"
      exit 1
    }
    {
      id = substr($0, 1, RLENGTH)
      sub(/^[^:]*:[[:space:]]*/, "", id)
      sub(/[[:space:]]*,$/, "", id)
      if (id !~ /^(0|[1-9][0-9]*)$/) {
        print "Invalid id at line " NR > "/dev/stderr"
        exit 1
      }
      printf "%s\t%s\n", id, $0
    }
  ' < "$input.$suffix" |
    sort --stable --field-separator=$'\t' --key=1,1n \
      --buffer-size="${SORT_BUFFER_SIZE:-256M}" --parallel="${SORT_PARALLEL:-1}" \
      --temporary-directory="${SORT_TMPDIR:-$work_dir}" |
    awk -v unique="$([[ "$suffix" == names ]] && echo 0 || echo 1)" -v ids="$work_dir/$suffix.ids" '
      {
        tab = index($0, "\t")
        id = substr($0, 1, tab - 1)
        if (unique && ("id:" id) == previous) {
          print "Duplicate id: " id > "/dev/stderr"
          exit 1
        }
        previous = "id:" id
        print id > ids
        print substr($0, tab + 1)
      }
    ' > "$work_dir/$suffix"
  # Ensure an empty trace also has an empty ID index.
  touch -- "$work_dir/$suffix.ids"
done

if ! cmp -s -- "$work_dir/proofs.ids" "$work_dir/theorems.ids"; then
  echo "Proof and theorem ID sequences differ; no outputs published." >&2
  exit 1
fi

# publish completed files without replacing
for suffix in "${suffixes[@]}"; do
  ln -- "$work_dir/$suffix" "$output.$suffix"
done
echo "Sorted traces: $output.{proofs,theorems,names}"
