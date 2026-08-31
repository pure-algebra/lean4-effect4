#!/usr/bin/env bash
# Deterministic mechanical join for the existing DATA-PG-ROW proof graph.
set -euo pipefail

repo_root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd -P)"
generator_rel="scripts/generate-data-row-assurance.sh"
source_rel="Effect4/Data/Row.lean"
contract_rel="test/contracts/data-row.contract.md"
lean_contract_rel="Effect4Test/Data/RowContract.lean"
axiom_report_rel="Effect4Test/Data/AxiomReport.lean"
assurance_rel="Effect4Test/Data/RowAssurance.lean"
register_rel="test/counterexamples/REGISTER.md"
attacks_rel="test/counterexamples/data/ATTACKS.md"
context_projection_rel="generated/environment-context-key-assurance.tsv"
context_gate_rel="scripts/check-environment-context-key-evidence.sh"

expected_contract_sha="7b3b397714267c376e6b5ef613fdbf0cf2266da9c1016e2d075e95794c335662"
expected_battery_sha="862bbc904c0c9150c5e9d722015797e5dcdaaa3a98baabccb9f2bb76a29d67ff"

contract_source="$repo_root/$contract_rel"
generation_mode="production"
if [[ $# -gt 0 ]]; then
  if [[ $# -eq 2 && "$1" == "--dry-run-contract" ]]; then
    generation_mode="dry-run-contract"
    contract_source="$2"
  else
    printf 'usage: generate-data-row-assurance.sh [--dry-run-contract <data-row.contract.md>]\n' >&2
    exit 2
  fi
fi

for override_name in \
    EFFECT4_DATA_ROW_SOURCE \
    EFFECT4_DATA_ROW_CONTRACT \
    EFFECT4_DATA_ROW_BATTERY \
    EFFECT4_DATA_ROW_CONTEXT_EVIDENCE \
    EFFECT4_DATA_ROW_ASSURANCE_DRIVER; do
  if [[ -n "${!override_name-}" ]]; then
    printf 'FAIL Data.Row assurance generator rejects source override variable %s\n' \
      "$override_name" >&2
    exit 2
  fi
done

for required in \
    "$repo_root/$generator_rel" \
    "$repo_root/$source_rel" \
    "$repo_root/$lean_contract_rel" \
    "$repo_root/$axiom_report_rel" \
    "$repo_root/$assurance_rel" \
    "$repo_root/$register_rel" \
    "$repo_root/$attacks_rel" \
    "$repo_root/$context_projection_rel" \
    "$repo_root/$context_gate_rel" \
    "$contract_source"; do
  [[ -f "$required" && ! -L "$required" ]] || {
    printf 'FAIL required Data.Row assurance input is absent, not regular, or a symlink: %s\n' \
      "$required" >&2
    exit 1
  }
done

lake_bin="$(command -v lake || true)"
[[ -n "$lake_bin" ]] || { printf 'FAIL lake is unavailable\n' >&2; exit 1; }

sha256_file() {
  if command -v sha256sum >/dev/null 2>&1; then
    sha256sum "$1" | awk '{print $1}'
  elif command -v shasum >/dev/null 2>&1; then
    shasum -a 256 "$1" | awk '{print $1}'
  else
    printf 'FAIL neither sha256sum nor shasum is available\n' >&2
    return 1
  fi
}

tmp_parent="${TMPDIR:-/tmp}"
tmp_parent="${tmp_parent%/}"
tmp_root="$(mktemp -d "$tmp_parent/effect4-data-row-assurance.XXXXXX")"

cleanup() {
  local cleanup_rc=$?
  set +e
  case "$tmp_root" in
    "$tmp_parent"/effect4-data-row-assurance.*) rm -rf -- "$tmp_root" ;;
    *)
      printf 'FAIL refusing to remove unexpected path: %s\n' "$tmp_root" >&2
      cleanup_rc=1
      ;;
  esac
  exit "$cleanup_rc"
}
trap cleanup EXIT

require_text() {
  local file="$1"
  local required_text="$2"
  grep -Fq -- "$required_text" "$file" || {
    printf 'FAIL required Data.Row assurance text is absent from %s: %s\n' \
      "$file" "$required_text" >&2
    exit 1
  }
}

count_exact_line() {
  local file="$1"
  local line="$2"
  local label="$3"
  local count
  count="$(grep -Fxc -- "$line" "$file" || true)"
  [[ "$count" == 1 ]] || {
    printf 'FAIL %s occurs %s times; expected exactly once\n' "$label" "$count" >&2
    exit 1
  }
}

# Closure must be derived here.  An authored graph or type row cannot supply
# its own completed state.
if grep -Fq -- '`required-closed`' "$contract_source"; then
  printf 'FAIL Data.Row authored contract carries a manual required-closed override\n' >&2
  exit 1
fi

actual_contract_sha="$(sha256_file "$contract_source")"
[[ "$actual_contract_sha" == "$expected_contract_sha" ]] || {
  printf 'FAIL frozen Data.Row contract hash drifted: expected %s, found %s\n' \
    "$expected_contract_sha" "$actual_contract_sha" >&2
  exit 1
}

actual_battery_sha="$(sha256_file "$repo_root/$lean_contract_rel")"
[[ "$actual_battery_sha" == "$expected_battery_sha" ]] || {
  printf 'FAIL frozen Data.Row battery hash drifted: expected %s, found %s\n' \
    "$expected_battery_sha" "$actual_battery_sha" >&2
  exit 1
}

require_text "$contract_source" 'Status: **Pass-B FROZEN; implementation REQUIRED-BLOCKED**'
require_text "$contract_source" '`proofGraphId = DATA-PG-ROW`'
require_text "$contract_source" 'There is no `Effect4.RowOrder`'
require_text "$contract_source" 'LE α'
require_text "$contract_source" 'LT α'
require_text "$contract_source" 'DecidableEq α'
require_text "$contract_source" 'DecidableLT α'
require_text "$contract_source" 'Std.IsLinearOrder α'
require_text "$contract_source" 'Std.LawfulOrderLT α'

graph_nodes=(
  DATA-ROW-IDENTITY
  DATA-ROW-ORDER
  DATA-ROW-INSERT
  DATA-ROW-NORMALIZE
  DATA-ROW-EXTENSIONALITY
  DATA-ROW-UNION
  DATA-ROW-WEAKENING
  DATA-ROW-COUNTEREXAMPLES
  DATA-ROW-TRUST
  DATA-ROW-COVERAGE
)
for node in "${graph_nodes[@]}"; do
  matches="$tmp_root/$node.matches"
  grep -F -- "| \`$node\` |" "$contract_source" >"$matches" || true
  count="$(wc -l <"$matches" | tr -d ' ')"
  [[ "$count" == 1 ]] || {
    printf 'FAIL DATA-PG-ROW node %s occurs %s times in the frozen graph; expected once\n' \
      "$node" "$count" >&2
    exit 1
  }
done

counterexample_rows="$tmp_root/counterexamples.rows"
: >"$counterexample_rows"
for suffix in 001 002 003 004 005 006 007 008 009; do
  counterexample_id="E4-DATA-CE-$suffix"
  matches="$tmp_root/$counterexample_id.matches"
  grep -F -- "| \`$counterexample_id\` |" \
    "$repo_root/$register_rel" >"$matches" || true
  count="$(wc -l <"$matches" | tr -d ' ')"
  [[ "$count" == 1 ]] || {
    printf 'FAIL Data.Row counterexample registration %s occurs %s times; expected once\n' \
      "$counterexample_id" "$count" >&2
    exit 1
  }
  require_text "$matches" '| SEEDED |'
  attack_count="$(grep -Fc -- "\`$counterexample_id\`" \
    "$repo_root/$attacks_rel" || true)"
  [[ "$attack_count" == 1 ]] || {
    printf 'FAIL Data.Row attack %s occurs %s times; expected once\n' \
      "$counterexample_id" "$attack_count" >&2
    exit 1
  }
  cat "$matches" >>"$counterexample_rows"
done

# The Context projection owns only the bridge leaf.  Its parent link must be a
# delegated route, never a second open/closed status. DATA-PG-ROW/ORDER is
# derived and owned in this file.
"$repo_root/$context_gate_rel" >"$tmp_root/context-gate.log" 2>&1
context_projection="$repo_root/$context_projection_rel"
count_exact_line "$context_projection" \
  $'leaf\tENV-LEAF-KEY-ORDER-BRIDGE\tderived-std-order-local-receipts\trequired-closed' \
  'closed Context standard-order bridge leaf'

parent_count="$(awk -F '\t' \
  '$1 == "parent-link" && $2 == "ENV-LEAF-KEY-ORDER-BRIDGE" && \
   $3 == "DATA-PG-ROW/ORDER" && $4 == "Effect4.ServiceKey" && \
   $5 == "delegated" { count++ } \
   END { print count + 0 }' "$context_projection")"
[[ "$parent_count" == 1 ]] || {
  printf 'FAIL Context order bridge has %s delegated DATA-PG-ROW/ORDER routes; expected once\n' \
    "$parent_count" >&2
  exit 1
}

context_semantic_count="$(awk -F '\t' \
  '$1 == "graph-attachment" && $2 == "ENV-PG-CONTEXT" && \
   $3 == "ENV-KEY-INTERP" && $4 == "Effect4.ServiceUniverse" && \
   $5 == "required-open" { count++ } END { print count + 0 }' \
  "$context_projection")"
[[ "$context_semantic_count" == 1 ]] || {
  printf 'FAIL ENV-PG-CONTEXT/ENV-KEY-INTERP must remain exactly once and required-open\n' >&2
  exit 1
}

bridge_api_count="$(awk -F '\t' '$1 == "order-bridge-api" { count++ } END { print count + 0 }' \
  "$context_projection")"
bridge_theorem_count="$(awk -F '\t' '$1 == "order-bridge-theorem" { count++ } END { print count + 0 }' \
  "$context_projection")"
bridge_receipt_count="$(awk -F '\t' '$1 == "order-bridge-receipt" { count++ } END { print count + 0 }' \
  "$context_projection")"
bridge_axiom_count="$(awk -F '\t' \
  '$1 == "axiom" && $4 == "none" && $5 == "ENV-LEAF-KEY-ORDER-BRIDGE" { count++ } \
   END { print count + 0 }' "$context_projection")"
[[ "$bridge_api_count" == 14 ]] || {
  printf 'FAIL Context order bridge API count is %s; expected 14\n' "$bridge_api_count" >&2
  exit 1
}
[[ "$bridge_theorem_count" == 7 ]] || {
  printf 'FAIL Context order bridge theorem count is %s; expected 7\n' \
    "$bridge_theorem_count" >&2
  exit 1
}
[[ "$bridge_receipt_count" == 8 ]] || {
  printf 'FAIL Context order bridge synthesis/relation/computation count is %s; expected 8\n' \
    "$bridge_receipt_count" >&2
  exit 1
}
[[ "$bridge_axiom_count" == 14 ]] || {
  printf 'FAIL Context order bridge axiom count is %s; expected 14 axiom-free receipts\n' \
    "$bridge_axiom_count" >&2
  exit 1
}

printf '%s\n' \
  Effect4.ServiceKey.Le \
  Effect4.ServiceKey.instLE \
  Effect4.ServiceKey.le_iff \
  Effect4.ServiceKey.instDecidableLE \
  Effect4.ServiceKey.lt_asymm \
  Effect4.ServiceKey.le_refl \
  Effect4.ServiceKey.le_trans \
  Effect4.ServiceKey.le_antisymm \
  Effect4.ServiceKey.le_total \
  Effect4.ServiceKey.lt_iff_le_not_le \
  Effect4.ServiceKey.instIsPreorder \
  Effect4.ServiceKey.instIsPartialOrder \
  Effect4.ServiceKey.instIsLinearOrder \
  Effect4.ServiceKey.instLawfulOrderLT \
  >"$tmp_root/expected-bridge-api.names"
awk -F '\t' '$1 == "order-bridge-api" { print $2 }' \
  "$context_projection" >"$tmp_root/actual-bridge-api.names"
if ! cmp -s -- "$tmp_root/expected-bridge-api.names" \
    "$tmp_root/actual-bridge-api.names"; then
  printf 'FAIL Context standard-order bridge API names drifted\n' >&2
  diff -u -- "$tmp_root/expected-bridge-api.names" \
    "$tmp_root/actual-bridge-api.names" >&2 || true
  exit 1
fi

(
  cd -- "$repo_root"
  unset LEAN_PATH LEAN_SRC_PATH
  "$lake_bin" build Effect4Test.Data.RowAssurance >"$tmp_root/build.log" 2>&1
  "$lake_bin" env lean "$lean_contract_rel" >"$tmp_root/contract.log" 2>&1
  "$lake_bin" env lean "$axiom_report_rel" >"$tmp_root/axioms.log" 2>&1
  "$lake_bin" env lean "$assurance_rel" >"$tmp_root/driver.log" 2>&1
)

grep $'^E4ROW\t' "$tmp_root/driver.log" >"$tmp_root/evidence.rows" || {
  printf 'FAIL Data.Row assurance driver emitted no evidence rows\n' >&2
  cat "$tmp_root/driver.log" >&2
  exit 1
}
sed 's/^E4ROW\t//' "$tmp_root/evidence.rows" >"$tmp_root/evidence.tsv"

evidence_count() {
  awk -F '\t' -v kind="$1" '$1 == kind { count++ } END { print count + 0 }' \
    "$tmp_root/evidence.tsv"
}

owned_count="$(evidence_count owned-declaration)"
api_count="$(evidence_count api)"
hypothesis_count="$(evidence_count hypotheses)"
theorem_count="$(evidence_count theorem)"
axiom_count="$(evidence_count axiom)"
absent_count="$(evidence_count absent)"
edge_count="$(evidence_count graph-edge)"

[[ "$owned_count" == 60 ]] || {
  printf 'FAIL Data.Row owned-declaration census emitted %s rows; expected 60\n' \
    "$owned_count" >&2
  exit 1
}
[[ "$api_count" == 34 ]] || {
  printf 'FAIL Data.Row authored API emitted %s rows; expected 34\n' "$api_count" >&2
  exit 1
}
[[ "$hypothesis_count" == 34 ]] || {
  printf 'FAIL Data.Row exact hypothesis profiles emitted %s rows; expected 34\n' \
    "$hypothesis_count" >&2
  exit 1
}
[[ "$theorem_count" == 23 ]] || {
  printf 'FAIL Data.Row theorem receipts emitted %s rows; expected 23\n' \
    "$theorem_count" >&2
  exit 1
}
[[ "$axiom_count" == 23 ]] || {
  printf 'FAIL Data.Row axiom receipts emitted %s rows; expected 23\n' \
    "$axiom_count" >&2
  exit 1
}
[[ "$absent_count" == 8 ]] || {
  printf 'FAIL Data.Row duplicate-prevention receipts emitted %s rows; expected 8\n' \
    "$absent_count" >&2
  exit 1
}
[[ "$edge_count" == 10 ]] || {
  printf 'FAIL DATA-PG-ROW emitted %s edges; expected 10\n' "$edge_count" >&2
  exit 1
}

awk '/^#print axioms / { print $3 }' "$repo_root/$axiom_report_rel" \
  >"$tmp_root/axiom-report.names"
awk -F '\t' '$1 == "axiom" { print $2 }' "$tmp_root/evidence.tsv" \
  >"$tmp_root/generated-axiom.names"
if ! cmp -s -- "$tmp_root/axiom-report.names" "$tmp_root/generated-axiom.names"; then
  printf 'FAIL generated Data.Row axiom names do not exactly match %s\n' \
    "$axiom_report_rel" >&2
  diff -u -- "$tmp_root/axiom-report.names" \
    "$tmp_root/generated-axiom.names" >&2 || true
  exit 1
fi

printf '%s\n' \
  $'DATA-PG-ROW/IDENTITY\tDATA-ROW-IDENTITY' \
  $'DATA-PG-ROW/ORDER\tDATA-ROW-ORDER' \
  $'DATA-PG-ROW/INSERT\tDATA-ROW-INSERT' \
  $'DATA-PG-ROW/NORMALIZE\tDATA-ROW-NORMALIZE' \
  $'DATA-PG-ROW/EXTENSIONALITY\tDATA-ROW-EXTENSIONALITY' \
  $'DATA-PG-ROW/UNION\tDATA-ROW-UNION' \
  $'DATA-PG-ROW/WEAKENING\tDATA-ROW-WEAKENING' \
  $'DATA-PG-ROW/COUNTEREXAMPLES\tDATA-ROW-COUNTEREXAMPLES' \
  $'DATA-PG-ROW/TRUST\tDATA-ROW-TRUST' \
  $'DATA-PG-ROW/COVERAGE\tDATA-ROW-COVERAGE' \
  >"$tmp_root/expected-edges.tsv"
awk -F '\t' '$1 == "graph-edge" { print $2 "\t" $3 }' \
  "$tmp_root/evidence.tsv" >"$tmp_root/actual-edges.tsv"
if ! cmp -s -- "$tmp_root/expected-edges.tsv" "$tmp_root/actual-edges.tsv"; then
  printf 'FAIL DATA-PG-ROW exact edge set drifted\n' >&2
  diff -u -- "$tmp_root/expected-edges.tsv" "$tmp_root/actual-edges.tsv" >&2 || true
  exit 1
fi

printf 'format\teffect4-data-row-assurance-v1\n'
if [[ "$generation_mode" == "dry-run-contract" ]]; then
  printf 'mode\tdry-run-contract\tcloses-nothing\n'
fi
printf 'generator\t%s\tsha256=%s\n' \
  "$generator_rel" "$(sha256_file "$repo_root/$generator_rel")"
printf 'regenerate\t./scripts/generate-data-row-assurance.sh > generated/data-row-assurance.tsv\n'
printf 'input\t%s\tsha256=%s\n' "$source_rel" \
  "$(sha256_file "$repo_root/$source_rel")"
printf 'input\t%s\tsha256=%s\n' "$contract_rel" "$actual_contract_sha"
printf 'input\t%s\tsha256=%s\n' "$lean_contract_rel" "$actual_battery_sha"
printf 'input\t%s\tsha256=%s\n' "$axiom_report_rel" \
  "$(sha256_file "$repo_root/$axiom_report_rel")"
printf 'input\t%s\tsha256=%s\n' "$assurance_rel" \
  "$(sha256_file "$repo_root/$assurance_rel")"
printf 'input\t%s#E4-DATA-CE-001--009\tsha256=%s\n' "$register_rel" \
  "$(sha256_file "$counterexample_rows")"
printf 'input\t%s\tsha256=%s\n' "$attacks_rel" \
  "$(sha256_file "$repo_root/$attacks_rel")"
printf 'input\t%s#ENV-LEAF-KEY-ORDER-BRIDGE\tsha256=%s\n' \
  "$context_projection_rel" "$(sha256_file "$context_projection")"
printf 'contract\tDATA-EV-ROW-CONTRACT\t%s\trequired-closed\n' "$contract_rel"
printf 'battery\tDATA-ROW-FROZEN-BATTERY\t%s\tsha256=%s\trequired-closed\n' \
  "$lean_contract_rel" "$actual_battery_sha"
printf 'type\tE4-TYPE-DATA-ROW\tEffect4.Row\tEffect4.Data.Row\tDATA-PG-ROW\trequired-closed\n'
printf 'type\tE4-TYPE-DATA-ASCENDING\tEffect4.Ascending\tEffect4.Data.Row\tDATA-PG-ROW/IDENTITY\trequired-closed\n'
printf 'dependency\tENV-LEAF-KEY-ORDER-BRIDGE\t%s\tDATA-PG-ROW/ORDER\trequired-closed\n' \
  "$context_projection_rel"
printf 'authority\tDATA-PG-ROW/ORDER\tgenerated/data-row-assurance.tsv\tderived-not-mirrored\n'
printf 'external-open\tENV-PG-CONTEXT/ENV-KEY-INTERP\tEffect4.ServiceUniverse\trequired-open\n'
for suffix in 001 002 003 004 005 006 007 008 009; do
  printf 'counterexample\tE4-DATA-CE-%s\tSEEDED\t%s\t%s\trequired-closed\n' \
    "$suffix" "$register_rel" "$lean_contract_rel"
done

awk -F '\t' '$1 != "graph-edge" { print }' "$tmp_root/evidence.tsv"
while IFS=$'\t' read -r edge node; do
  printf 'graph-edge\t%s\t%s\trequired-closed\n' "$edge" "$node"
done <"$tmp_root/expected-edges.tsv"
