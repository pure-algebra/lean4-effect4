#!/usr/bin/env bash
# Plants defects the trace gates must catch: a flipped answer in a golden, a
# removed mask row, a stale projection, and a flipped answer in a Flow-runner
# golden (the internal oracle). Each mutant is written to a temp directory;
# the committed projections are never edited.
set -euo pipefail
repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
tools="${EFFECT4_TOOLS:-$repo_root/../effect4-tools}"
tmp="$(mktemp -d "${TMPDIR:-/tmp}/effect4-trace-gate.XXXXXX")"
trap 'rm -rf -- "$tmp"' EXIT
cd "$repo_root"
traces="$repo_root/generated/traces"
here="$repo_root/harness/trace"
caught=0; total=4
expect() { # name, signal, command...
  local name="$1" signal="$2"; shift 2
  local log="$tmp/$name.log"
  if "$@" >"$log" 2>&1; then echo "FAIL mutant $name was accepted" >&2; cat "$log" >&2; return 1; fi
  if ! grep -Fq -- "$signal" "$log"; then echo "FAIL mutant $name rejected for an unrelated reason" >&2; cat "$log" >&2; return 1; fi
  echo "PASS mutant $name caught: $signal"; caught=$((caught + 1))
}
# 1. a flipped answer value in the incr golden must diverge on the host
sed 's/^answer\tget\t41$/answer\tget\t40/' "$traces/incr.empty.tsv" > "$tmp/flipped.tsv"
cmp -s "$tmp/flipped.tsv" "$traces/incr.empty.tsv" && { echo "FAIL flipped fixture did not mutate the golden" >&2; exit 1; }
expect flipped-answer "DIVERGES" env EFFECT4_PROGRAM=incr node "$tools/packages/harness/trace.mjs" "$here" --golden "$tmp/flipped.tsv" --masks "$traces/masks.tsv"
# 2. a mask table with no mask rows is drift
grep -v '^mask' "$traces/masks.tsv" > "$tmp/no-masks.tsv"
expect removed-masks "mask table drift" env EFFECT4_PROGRAM=incr node "$tools/packages/harness/trace.mjs" "$here" --golden "$traces/incr.empty.tsv" --masks "$tmp/no-masks.tsv"
# 3. a stale projection (edited pin row) fails the hermetic drift gate
mkdir -p "$tmp/stale" && cp -R "$traces"/. "$tmp/stale/"
sed -i '' 's/^pin\teffects\t.*/pin\teffects\tdeadbeef/' "$tmp/stale/incr.empty.tsv"
expect stale-projection "stale generated trace projection: incr.empty.tsv" "$repo_root/scripts/check-trace-goldens.sh" --dry-run "$tmp/stale"
# 4. a flipped answer in the Flow-runner golden is drift of the internal oracle
mkdir -p "$tmp/flow-flipped" && cp -R "$traces"/. "$tmp/flow-flipped/"
sed -i '' 's/^answer\tget\t41$/answer\tget\t40/' "$tmp/flow-flipped/flow/incr.empty.tsv"
cmp -s "$tmp/flow-flipped/flow/incr.empty.tsv" "$traces/flow/incr.empty.tsv" && { echo "FAIL flow fixture did not mutate the golden" >&2; exit 1; }
expect flow-flipped-answer "stale generated trace projection: flow/incr.empty.tsv" "$repo_root/scripts/check-trace-goldens.sh" --dry-run "$tmp/flow-flipped"
echo "PASS trace gates react to $caught/$total planted defects"
