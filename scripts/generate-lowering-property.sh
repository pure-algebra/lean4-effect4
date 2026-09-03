#!/usr/bin/env bash
# Prints generated/lowering-property.tsv: provenance rows and the summary row of
# the property batch (seed, generated, admitted, runs, frontiers, sites, corpus
# digest). The corpus itself is regenerated from the seed on every run of
# scripts/check-lowering-property.sh and never committed.
set -euo pipefail
repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repo_root"
sha() { shasum -a 256 "$1" | cut -d' ' -f1; }
effects_rev="$(python3 -c "import json;m=json.load(open('lake-manifest.json'));print(next(p['rev'] for p in m['packages'] if p['name']=='effects'))")"
printf 'format\teffect4-lowering-property-v1\n'
printf 'generator\tscripts/generate-lowering-property.sh\tsha256=%s\n' "$(sha scripts/generate-lowering-property.sh)"
printf 'regenerate\t./scripts/generate-lowering-property.sh > generated/lowering-property.tsv\n'
for input in harness/trace/Property.lean harness/trace/property-tail.ts harness/trace/tracer.ts Effect4/Target/TypeScript/FlowLower.lean; do
  printf 'input\t%s\tsha256=%s\n' "$input" "$(sha "$input")"
done
printf 'pin\teffects\t%s\n' "$effects_rev"
printf 'row\t%s\n' "$(./scripts/check-lowering-property.sh --print-row)"
