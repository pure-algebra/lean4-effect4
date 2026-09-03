#!/usr/bin/env bash
# Plants defects the lowering ledger must refuse. Mutants live in a temp
# directory; nothing committed is edited.
#
# ## Stamp (rule 9)
#
# A mutation self-test reads what the gate it attacks reads, plus the gate: the
# rule sources under `Effect4/Target/TypeScript/`, the goldens and receipts it
# copies and then breaks, the committed ledger it mutates a state column in,
# the numerator module and the Lake traces of its imports, and the generator
# and checker themselves. If none of that changed, neither did which mutants
# the gate catches.
set -euo pipefail
repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
. "$repo_root/scripts/lib/portable.sh"
. "$repo_root/scripts/lib/stamp.sh"
for argument in "$@"; do
  case "$argument" in
    --force) export EFFECT4_FORCE=1 ;;
    *) echo "unknown argument $argument" >&2; exit 2 ;;
  esac
done
tmp="$(mktemp -d "${TMPDIR:-/tmp}/effect4-lowering-gate.XXXXXX")"; trap 'rm -rf -- "$tmp"' EXIT
cd "$repo_root"
lake build Effect4 >/dev/null
numerator="$repo_root/Effect4Test/Target/TypeScript/LoweringCoverage.lean"
inputs=(
  "$repo_root/scripts/test-lowering-coverage-gate.sh"
  "$repo_root/scripts/generate-lowering-coverage.sh"
  "$repo_root/scripts/check-lowering-coverage.sh"
  "$repo_root/scripts/lib/portable.sh"
  "$repo_root/scripts/lib/stamp.sh"
  "$numerator"
  "$repo_root/Effect4/Target/TypeScript"
  "$repo_root/generated/traces"
  "$repo_root/generated/lowering-coverage.tsv"
  "$repo_root/generated/lowering-property.tsv"
  "$repo_root/harness/trace/host-pin.json"
  "$repo_root/docs/LOWERING-COVERAGE.md"
  "$repo_root/lakefile.toml"
  "$repo_root/lake-manifest.json"
  "$repo_root/lean-toolchain"
)
for evidence in "$repo_root"/harness/trace/receipts/*.json \
                "$repo_root"/harness/trace/types/*.receipt; do
  if [ -f "$evidence" ]; then inputs+=("$evidence"); fi
done
while IFS= read -r trace; do inputs+=("$trace"); done < <(stamp_lean_traces "$numerator")
key="$(stamp_key "${inputs[@]}")"
if stamp_hit lowering-coverage-gate "$key"; then
  stamp_report lowering-coverage-gate "$key"
  exit 0
fi
gen="$repo_root/scripts/generate-lowering-coverage.sh"
caught=0; total=4
expect() {
  local name="$1" signal="$2"; shift 2
  local log="$tmp/$name.log"
  if "$@" >"$log" 2>&1; then echo "FAIL mutant $name was accepted" >&2; cat "$log" >&2; return 1; fi
  if ! grep -Fq -- "$signal" "$log"; then echo "FAIL mutant $name rejected for an unrelated reason" >&2; cat "$log" >&2; return 1; fi
  echo "PASS mutant $name caught: $signal"; caught=$((caught + 1))
}
# 1. a tag with no ledger row
mkdir -p "$tmp/sources" && cp Effect4/Target/TypeScript/*.lean "$tmp/sources/"
printf '/-- lowering: rule.bogus -/\n' >> "$tmp/sources/EffectV4.lean"
expect tag-without-row "lowering rule census" "$gen" --sources "$tmp/sources"
# 2. a claimed golden that is missing
mkdir -p "$tmp/traces" && cp generated/traces/*.tsv "$tmp/traces/" && rm "$tmp/traces/incr.empty.tsv"
expect missing-golden "missing golden evidence" "$gen" --traces "$tmp/traces"
# 3. a host receipt at a different pin
mkdir -p "$tmp/receipts" && cp harness/trace/receipts/*.json "$tmp/receipts/"
python3 - "$tmp/receipts/incr.empty.json" <<'PY'
import json, sys
p = sys.argv[1]; r = json.load(open(p)); r["host"]["pin"]["effectTreeSha256"] = "0" * 64
json.dump(r, open(p, "w"), indent=1)
PY
expect receipt-pin "host receipt pin differs" "$gen" --receipts "$tmp/receipts"
# 4. a stale projection
sed 's/\tchecked\t/\tcovered\t/' generated/lowering-coverage.tsv > "$tmp/stale.tsv"
cmp -s "$tmp/stale.tsv" generated/lowering-coverage.tsv && { echo "FAIL stale fixture did not mutate the projection" >&2; exit 1; }
expect stale-projection "stale generated lowering coverage" "$repo_root/scripts/check-lowering-coverage.sh" --dry-run "$tmp/stale.tsv"
stamp_write lowering-coverage-gate "$key" "the ledger refuses $caught/$total planted defects"
echo "PASS lowering coverage gate reacts to $caught/$total planted defects"
