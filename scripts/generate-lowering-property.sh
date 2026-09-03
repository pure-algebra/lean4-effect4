#!/usr/bin/env bash
# Prints generated/lowering-property.tsv: provenance rows and the summary row of
# the property batch (seed, generated, admitted, runs, frontiers, sites, corpus
# digest). The corpus itself is regenerated from the seed on every run of
# scripts/check-lowering-property.sh and never committed.
set -euo pipefail
repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
. "$repo_root/scripts/lib/portable.sh"
cd "$repo_root"
effects_rev="$(python3 -c "import json;m=json.load(open('lake-manifest.json'));print(next(p['rev'] for p in m['packages'] if p['name']=='effects'))")"
# An abbreviated revision is not a durable identifier, and the provenance width
# once changed mid-corpus (survey finding H10). Refuse before a byte is printed.
[[ "$effects_rev" =~ ^[0-9a-f]{40}$ ]] || {
  echo "FAIL lake-manifest.json gives the effects rev as '$effects_rev'; a pin row must be 40 hex characters" >&2
  echo "  put the full sha in lakefile.toml and re-resolve the manifest" >&2
  exit 1
}
printf 'format\teffect4-lowering-property-v1\n'
printf 'generator\tscripts/generate-lowering-property.sh\tsha256=%s\n' "$(sha256 scripts/generate-lowering-property.sh)"
printf 'regenerate\t./scripts/generate-lowering-property.sh > generated/lowering-property.tsv\n'
for input in harness/trace/Property.lean harness/trace/property-tail.ts harness/trace/tracer.ts Effect4/Target/TypeScript/FlowLower.lean; do
  printf 'input\t%s\tsha256=%s\n' "$input" "$(sha256 "$input")"
done
printf 'pin\teffects\t%s\n' "$effects_rev"
printf 'row\t%s\n' "$(./scripts/check-lowering-property.sh --print-row)"
