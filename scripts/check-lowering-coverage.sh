#!/usr/bin/env bash
# Drift gate for generated/lowering-coverage.tsv. --dry-run <candidate.tsv>
# compares the regeneration with a candidate instead (self-test only).
#
# ## Stamp (rule 9)
#
# The generator is where the reading happens, so the key names what IT opens:
# the numerator module `Effect4Test/Target/TypeScript/LoweringCoverage.lean` and
# the Lake traces of its imports; `Effect4/Target/TypeScript/`, which the rule
# census scans for `lowering: rule.*` tags in both directions; every committed
# golden under `generated/traces/`, whose `rules` rows and digests are the
# golden evidence; the top-level host receipts under `harness/trace/receipts/`
# and the pin they are compared with, `harness/trace/host-pin.json`; the type
# receipts under `harness/trace/types/`; `generated/lowering-property.tsv`;
# `docs/LOWERING-COVERAGE.md`, whose digest goes into the provenance block; and
# the manifest, which supplies the effects revision. Finally the committed
# projection itself, because that is what the fresh bytes are compared with.
#
# `--dry-run` compares against a candidate, so it neither reads nor writes a
# stamp.
set -euo pipefail
repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
. "$repo_root/scripts/lib/portable.sh"
. "$repo_root/scripts/lib/stamp.sh"
committed="$repo_root/generated/lowering-coverage.tsv"; note=""; stamped=1
while [ $# -gt 0 ]; do
  case "$1" in
    --dry-run) committed="$2"; note=" (dry run, closes nothing)"; stamped=0; shift 2 ;;
    --force) export EFFECT4_FORCE=1; shift ;;
    *) echo "unknown argument $1" >&2; exit 2 ;;
  esac
done
if [ "$stamped" -eq 1 ]; then
  ( cd "$repo_root" && lake build Effect4 >/dev/null )
  numerator="$repo_root/Effect4Test/Target/TypeScript/LoweringCoverage.lean"
  inputs=(
    "$repo_root/scripts/check-lowering-coverage.sh"
    "$repo_root/scripts/generate-lowering-coverage.sh"
    "$repo_root/scripts/lib/portable.sh"
    "$repo_root/scripts/lib/stamp.sh"
    "$numerator"
    "$repo_root/Effect4/Target/TypeScript"
    "$repo_root/generated/traces"
    "$repo_root/generated/lowering-property.tsv"
    "$repo_root/harness/trace/host-pin.json"
    "$repo_root/docs/LOWERING-COVERAGE.md"
    "$committed"
    "$repo_root/lakefile.toml"
    "$repo_root/lake-manifest.json"
    "$repo_root/lean-toolchain"
  )
  # Only the top level of each evidence directory: the join reads
  # `<receipts>/<golden>.json` and `<types>/<golden>.receipt` and never
  # descends, and `receipts/patched/` is rewritten with an absolute path on
  # every host run, which would make this gate miss for a reason it cannot see.
  for evidence in "$repo_root"/harness/trace/receipts/*.json \
                  "$repo_root"/harness/trace/types/*.receipt; do
    if [ -f "$evidence" ]; then inputs+=("$evidence"); fi
  done
  while IFS= read -r trace; do inputs+=("$trace"); done < <(stamp_lean_traces "$numerator")
  key="$(stamp_key "${inputs[@]}")"
  if stamp_hit lowering-coverage "$key"; then
    stamp_report lowering-coverage "$key"
    exit 0
  fi
fi
tmp="$(mktemp "${TMPDIR:-/tmp}/effect4-lowering.XXXXXX")"; trap 'rm -f -- "$tmp"' EXIT
"$repo_root/scripts/generate-lowering-coverage.sh" > "$tmp"
if ! cmp -s "$tmp" "$committed"; then
  echo "FAIL stale generated lowering coverage: $committed" >&2
  diff -u "$committed" "$tmp" | head -30 >&2 || true; exit 1
fi
counts="$(grep $'^count\t' "$tmp" | awk -F'\t' '{ printf "%s %s ", $2, $3 }')"
summary="generated/lowering-coverage.tsv is current; states: ${counts}"
if [ "$stamped" -eq 1 ]; then stamp_write lowering-coverage "$key" "$summary"; fi
echo "PASS $summary$note"
