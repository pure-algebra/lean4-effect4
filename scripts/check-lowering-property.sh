#!/usr/bin/env bash
# The property loop (P-T6): generate a seeded corpus of flows by construction,
# admit them (a refusal is a generator bug), build tapes by policy, lower every
# flow into one dispatch-form module, and run the whole batch once on the host,
# comparing every case with its Flow-runner golden under every mask. On a
# divergence, shrink the first failing case (budget 64 candidates, each
# confirmed on the host) and store it as first-order data under
# generated/lowering-property-failures/. Writes the batch receipt and prints
# the summary row of generated/lowering-property.tsv.
#   --seed <n> --count <n>      corpus parameters (defaults below)
#   --print-row                 print only the ledger row (used by the generator)
#
# ## Stamp (rule 9)
#
# What it reads: `harness/trace/Property.lean`, which constructs the corpus and
# the Flow-runner goldens, and the Lake traces of its imports; the four harness
# TypeScript files it stages beside the corpus and the pin it copies with them;
# `generated/traces/masks.tsv`; the committed ledger row it compares its own
# summary with; the effect4-tools batch runner; and the pinned installation's
# identity. The seed and the corpus size are inputs too, and neither is a file,
# so both are keyed as facts -- a run at another seed is a different question
# and gets a different stamp.
#
# `--print-row` is the generator's mode: it prints a row rather than closing
# anything, so it neither reads nor writes a stamp.
set -euo pipefail
repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
. "$repo_root/scripts/lib/portable.sh"
. "$repo_root/scripts/lib/stamp.sh"
tools="${EFFECT4_TOOLS:-$repo_root/../effect4-tools}"
here="$repo_root/harness/trace"
seed="${EFFECT4_PROPERTY_SEED:-2026}"; count="${EFFECT4_PROPERTY_COUNT:-200}"; print_row=0
while [ $# -gt 0 ]; do
  case "$1" in
    --seed) seed="$2"; shift 2 ;;
    --count) count="$2"; shift 2 ;;
    --print-row) print_row=1; shift ;;
    --force) export EFFECT4_FORCE=1; shift ;;
    *) echo "unknown argument $1" >&2; exit 2 ;;
  esac
done
cd "$repo_root"
lake build Effect4 >/dev/null
if [ "$print_row" -eq 0 ]; then
  inputs=(
    "$repo_root/scripts/check-lowering-property.sh"
    "$repo_root/scripts/lib/portable.sh"
    "$repo_root/scripts/lib/stamp.sh"
    "$here/Property.lean"
    "$here/tracer.ts" "$here/atoms.ts"
    "$here/property-tail.ts" "$here/property-structured-tail.ts"
    "$repo_root/generated/traces/masks.tsv"
    "$repo_root/generated/lowering-property.tsv"
    "$repo_root/lakefile.toml"
    "$repo_root/lake-manifest.json"
    "$repo_root/lean-toolchain"
  )
  while IFS= read -r input; do inputs+=("$input"); done < <(
    stamp_lean_traces "$here/Property.lean"
    stamp_tools_inputs batch.mjs copy.mjs
    stamp_host_inputs
    stamp_fact seed "$seed"
    stamp_fact count "$count"
  )
  key="$(stamp_key "${inputs[@]}")"
  if stamp_hit lowering-property "$key"; then
    stamp_report lowering-property "$key"
    exit 0
  fi
fi
tmp="$(mktemp -d "${TMPDIR:-/tmp}/effect4-property.XXXXXX")"; trap 'rm -rf -- "$tmp"' EXIT
# `lean_run` comes from scripts/lib/portable.sh: it prints a FAIL line naming
# this gate and everything Lean wrote whenever the run fails. The older spelling
# piped Lean straight into a command substitution, and Lean writes its errors to
# standard output, so a missing-cases error in Property.lean left this script
# exiting 1 with an empty log.
property_run() { lean_run "$here/Property.lean" "$@"; }
prepare() { # dir: the harness files a batch needs beside the corpus
  cp "$here/tracer.ts" "$here/atoms.ts" "$here/property-tail.ts" "$here/property-structured-tail.ts" "$here/host-pin.json" "$1/"
}
mkdir -p "$tmp/corpus" && prepare "$tmp/corpus"
summary="$(property_run corpus "$seed" "$count" "$tmp/corpus")"
digest="$(cat "$tmp/corpus/property-fixture.ts" "$tmp/corpus/property-structured-fixture.ts" "$tmp/corpus/goldens"/*.tsv | sha256)"
mkdir -p "$here/receipts"
batch_log="$tmp/batch.log"
set +e
node "$tools/packages/harness/batch.mjs" "$tmp/corpus" --goldens "$tmp/corpus/goldens" \
  --masks "$repo_root/generated/traces/masks.tsv" --tail property-tail.ts \
  --receipt "$here/receipts/property.json" > "$batch_log" 2>&1
status=$?
if [ "$status" -eq 0 ]; then
  # the structured form of the same corpus against the same goldens
  node "$tools/packages/harness/batch.mjs" "$tmp/corpus" --goldens "$tmp/corpus/goldens" \
    --masks "$repo_root/generated/traces/masks.tsv" --tail property-structured-tail.ts \
    --receipt "$here/receipts/property-structured.json" | sed 's/^batch/batch(structured)/; s/^trace/trace(structured)/' >> "$batch_log" 2>&1
  status=$?
fi
set -e
[ "$print_row" -eq 1 ] || cat "$batch_log"
if [ "$status" -eq 3 ]; then echo "FAIL property batch: invalid host run" >&2; exit 3; fi
if [ "$status" -ne 0 ]; then
  first="$(grep -m1 '^trace .* DIVERGES' "$batch_log" | awk '{print $2}')"
  program="${first%%.*}"; tape="${first#*.}"
  echo "FAIL property batch: $first diverges; shrinking (budget 64)" >&2
  path=""; budget=64
  while [ "$budget" -gt 0 ]; do
    rm -rf "$tmp/shrink" && mkdir -p "$tmp/shrink" && prepare "$tmp/shrink"
    property_run shrink "$seed" "$count" "$program" "$tape" "$path" "$tmp/shrink" >/dev/null
    candidates="$(ls "$tmp/shrink/goldens" | wc -l | tr -d ' ')"
    [ "$candidates" -gt 0 ] || break
    budget=$((budget - candidates))
    set +e
    node "$tools/packages/harness/batch.mjs" "$tmp/shrink" --goldens "$tmp/shrink/goldens" \
      --masks "$repo_root/generated/traces/masks.tsv" --tail property-tail.ts > "$tmp/shrink.log" 2>&1
    set -e
    next="$(grep -m1 '^trace s[0-9]*\.t .* DIVERGES' "$tmp/shrink.log" | awk '{print $2}' | sed 's/^s//; s/\.t$//')"
    [ -n "$next" ] || break
    path="${path:+$path,}$next"
  done
  out="$repo_root/generated/lowering-property-failures/$program.$tape"
  mkdir -p "$out"
  property_run case "$seed" "$count" "$program" "$tape" "$path" > "$out/case.tsv"
  printf 'seed\t%s\ncount\t%s\nprogram\t%s\ntape\t%s\npath\t%s\n' "$seed" "$count" "$program" "$tape" "$path" > "$out/origin.tsv"
  cp "$batch_log" "$out/batch.log"
  echo "FAIL property batch: minimal case stored under $out (path $path)" >&2
  exit 1
fi
row="$(printf '%s\tdigest\tsha256=%s' "$summary" "$digest")"
if [ "$print_row" -eq 1 ]; then echo "$row"; exit 0; fi
echo "PASS property batch: $summary"
# --- drift: the committed ledger row must be this run's row --------------------
ledger="$repo_root/generated/lowering-property.tsv"
if [ -f "$ledger" ]; then
  committed="$(grep '^row	' "$ledger" | cut -f2-)"
  if [ "$committed" != "$row" ]; then
    echo "FAIL stale generated lowering property row; regenerate with ./scripts/generate-lowering-property.sh > generated/lowering-property.tsv" >&2
    echo "  committed: $committed" >&2; echo "  fresh:     $row" >&2; exit 1
  fi
  echo "PASS generated/lowering-property.tsv is current"
fi
# The batch summary is tab-separated; a stamp line is read by a person.
stamp_write lowering-property "$key" "property batch: $(printf '%s' "$summary" | tr '\t' ' ')"
