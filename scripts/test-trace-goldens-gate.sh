#!/usr/bin/env bash
# Plants defects the trace gates must catch: a flipped answer in a golden, a
# removed mask row, a stale projection, a flipped answer in a Flow-runner
# golden (the internal oracle), and the four wire facts of packet M0 — a raw
# C0 control in a string answer, a natural above 2^53 - 1, a dying program,
# and a doubled frontier. Each mutant is written to a temp directory; the
# committed projections are never edited.
set -euo pipefail
repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
tools="${EFFECT4_TOOLS:-$repo_root/../effect4-tools}"
tmp="$(mktemp -d "${TMPDIR:-/tmp}/effect4-trace-gate.XXXXXX")"
trap 'rm -rf -- "$tmp"' EXIT
cd "$repo_root"
traces="$repo_root/generated/traces"
here="$repo_root/harness/trace"
caught=0; total=8
expect() { # name, signal, command...
  local name="$1" signal="$2"; shift 2
  local log="$tmp/$name.log"
  if "$@" >"$log" 2>&1; then echo "FAIL mutant $name was accepted" >&2; cat "$log" >&2; return 1; fi
  if ! grep -Fq -- "$signal" "$log"; then echo "FAIL mutant $name rejected for an unrelated reason" >&2; cat "$log" >&2; return 1; fi
  echo "PASS mutant $name caught: $signal"; caught=$((caught + 1))
}
accept() { # name, signal, command...  a positive control: it must pass
  local name="$1" signal="$2"; shift 2
  local log="$tmp/$name.log"
  if ! "$@" >"$log" 2>&1; then echo "FAIL control $name did not pass" >&2; cat "$log" >&2; return 1; fi
  if ! grep -Fq -- "$signal" "$log"; then echo "FAIL control $name passed without $signal" >&2; cat "$log" >&2; return 1; fi
  echo "PASS control $name: $signal"
}
# A golden for one of the planted `wire-tail.ts` programs: the header rows the
# driver reads, then the one row given.
plant() { # file, program, row
  { printf 'format\teffect4-trace-v1\nface\tlean\nprogram\t%s\ntape\t\nrules\t\n' "$2"; printf '%s\n' "$3"; } > "$1"
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
# --- M0: the four wire facts, none of which the corpus reaches ---------------
# 5. a raw U+0001 in a string answer. `JSON.stringify` writes the six-character
# escape and `Trace.escape` now matches it, so a golden holding the raw
# character diverges. The escaped golden beside it is the positive control:
# without it a divergence here would prove nothing about the escaping.
{ printf 'format\teffect4-trace-v1\nface\tlean\nprogram\tcontrol\ntape\t\nrules\t\n'
  printf 'done\t{"success":"a\001b"}\n'; } > "$tmp/control-raw.tsv"
plant "$tmp/control-escaped.tsv" control 'done	{"success":"a\u0001b"}'
expect raw-control "DIVERGES" env EFFECT4_PROGRAM=control node "$tools/packages/harness/trace.mjs" "$here" --golden "$tmp/control-raw.tsv" --masks "$traces/masks.tsv" --tail wire-tail.ts
accept escaped-control "mask m2 ok" env EFFECT4_PROGRAM=control node "$tools/packages/harness/trace.mjs" "$here" --golden "$tmp/control-escaped.tsv" --masks "$traces/masks.tsv" --tail wire-tail.ts
# 6. a natural above 2^53 - 1, refused on both faces: the host tracer reports
# the run invalid, and Lean refuses to emit a golden carrying one at all.
plant "$tmp/overflow.tsv" overflow 'done	{"success":9007199254740992}'
expect unsafe-integer-host "INVALID: tracer defect" env EFFECT4_PROGRAM=overflow node "$tools/packages/harness/trace.mjs" "$here" --golden "$tmp/overflow.tsv" --masks "$traces/masks.tsv" --tail wire-tail.ts
expect unsafe-integer-emission "leaves the host-exact range" lake env lean --run "$here/Generate.lean" admission-probe
# 7. a dying program. A defect rendered as `{"failure":[]}` was byte-identical
# to a unit failure; the golden below still claims that form and must diverge,
# and the row the host actually produced must name the defect.
plant "$tmp/die.tsv" die 'done	{"failure":[]}'
expect die-as-failure '{"defect":' env EFFECT4_PROGRAM=die node "$tools/packages/harness/trace.mjs" "$here" --golden "$tmp/die.tsv" --masks "$traces/masks.tsv" --tail wire-tail.ts
# 8. a doubled frontier. The op budget is one frontier however many primitives
# run past it, so the budget golden with its frontier duplicated must diverge.
awk '{ print; if ($0 == "frontier") print "frontier" }' "$traces/flow/swap.budget.tsv" > "$tmp/double-frontier.tsv"
cmp -s "$tmp/double-frontier.tsv" "$traces/flow/swap.budget.tsv" && { echo "FAIL frontier fixture did not mutate the golden" >&2; exit 1; }
expect doubled-frontier "DIVERGES" env EFFECT4_PROGRAM=swap EFFECT4_BUDGET=19 node "$tools/packages/harness/trace.mjs" "$here" --golden "$tmp/double-frontier.tsv" --masks "$traces/masks.tsv" --tail flow-tail.ts
echo "PASS trace gates react to $caught/$total planted defects"
