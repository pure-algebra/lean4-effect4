#!/usr/bin/env bash
# Deterministic generated-evidence projection for the environment Context Key
# leaf and its additive Std order bridge.  The semantic edge ENV-KEY-INTERP
# and the bridge's DATA-PG-ROW/ORDER attachment are recorded as open; this
# generator closes only declaration ownership and the local Lean receipts.
set -euo pipefail

repo_root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd -P)"
generator_rel="scripts/generate-environment-context-key-evidence.sh"
driver_rel="test/fixtures/environment-context-key-evidence/Required.lean"
contract_rel="test/contracts/environment-context-key.contract.md"
lean_contract_rel="Effect4Test/Environment/ContextKeyContract.lean"
axiom_report_rel="Effect4Test/Environment/AxiomReport.lean"
assurance_rel="Effect4Test/Environment/ContextKeyAssurance.lean"
key_source_rel="Effect4/Context/Key.lean"
manifest_rel="PORT-MANIFEST.md"
counterexample_register_rel="test/counterexamples/REGISTER.md"
counterexample_attacks_rel="test/counterexamples/environment/ATTACKS.md"
manifest_source="$repo_root/$manifest_rel"
generation_mode="production"

if [[ $# -gt 0 ]]; then
  if [[ $# -eq 2 && "$1" == "--dry-run-manifest" ]]; then
    generation_mode="dry-run"
    manifest_source="$2"
  else
    printf 'usage: generate-environment-context-key-evidence.sh [--dry-run-manifest <PORT-MANIFEST.md>]\n' >&2
    exit 2
  fi
fi

for override_name in \
    EFFECT4_CONTEXT_KEY_SOURCE \
    EFFECT4_CONTEXT_KEY_CONTRACT \
    EFFECT4_CONTEXT_KEY_MANIFEST \
    EFFECT4_CONTEXT_KEY_EVIDENCE_DRIVER; do
  if [[ -n "${!override_name-}" ]]; then
    printf 'FAIL context-key evidence generator rejects source override variable %s\n' \
      "$override_name" >&2
    exit 2
  fi
done

for required in \
    "$repo_root/$generator_rel" \
    "$repo_root/$driver_rel" \
    "$repo_root/$contract_rel" \
    "$repo_root/$lean_contract_rel" \
    "$repo_root/$axiom_report_rel" \
    "$repo_root/$assurance_rel" \
    "$repo_root/$key_source_rel" \
    "$repo_root/$counterexample_register_rel" \
    "$repo_root/$counterexample_attacks_rel" \
    "$manifest_source"; do
  [[ -f "$required" && ! -L "$required" ]] || {
    printf 'FAIL required context-key evidence input is absent, not regular, or a symlink: %s\n' \
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
tmp_root="$(mktemp -d "$tmp_parent/effect4-context-key-evidence.XXXXXX")"

cleanup() {
  local cleanup_status=$?
  set +e
  case "$tmp_root" in
    "$tmp_parent"/effect4-context-key-evidence.*) rm -rf -- "$tmp_root" ;;
    *)
      printf 'FAIL refusing to remove unexpected path: %s\n' "$tmp_root" >&2
      cleanup_status=1
      ;;
  esac
  exit "$cleanup_status"
}
trap cleanup EXIT

require_text() {
  local file="$1"
  local text="$2"
  grep -Fq -- "$text" "$file" || {
    printf 'FAIL required context-key contract/allocation text is absent from %s: %s\n' \
      "$file" "$text" >&2
    exit 1
  }
}

# The evidence ID is the existing manifest allocation for this frozen packet;
# no second contract identity is minted by the generator.
require_text "$repo_root/$contract_rel" 'Status: FROZEN breaker packet'
require_text "$repo_root/$contract_rel" 'Implementation fence: `F-KEY` = `Effect4/Context/Key.lean`'
for obligation_id in ENV-KEY-01 ENV-KEY-02 ENV-KEY-03 ENV-KEY-04; do
  require_text "$repo_root/$contract_rel" "\`$obligation_id\`"
done
require_text "$repo_root/$contract_rel" '`ENV-KEY-INTERP`'
require_text "$repo_root/$contract_rel" 'not with its own proof graph'

counterexample_rows="$tmp_root/counterexamples.rows"
: >"$counterexample_rows"
for suffix in 001 002 003 004 005 006; do
  counterexample_id="E4-ENV-CE-$suffix"
  matches="$tmp_root/$counterexample_id.matches"
  grep -F -- "| \`$counterexample_id\` |" \
    "$repo_root/$counterexample_register_rel" >"$matches" || true
  count="$(wc -l <"$matches" | tr -d ' ')"
  [[ "$count" == 1 ]] || {
    printf 'FAIL counterexample registration %s occurs %s times; expected exactly once\n' \
      "$counterexample_id" "$count" >&2
    exit 1
  }
  require_text "$matches" '| `E4-ENV-CE-'
  require_text "$matches" '| SEEDED |'
  require_text "$repo_root/$contract_rel" "\`$counterexample_id\`"
  require_text "$repo_root/$counterexample_attacks_rel" "\`$counterexample_id\`"
  cat "$matches" >>"$counterexample_rows"
done

manifest_rows="$tmp_root/manifest.rows"
: >"$manifest_rows"

manifest_row() {
  local row_id="$1"
  local matches="$tmp_root/$row_id.matches"
  grep -F -- "| \`$row_id\` |" "$manifest_source" >"$matches" || true
  local count
  count="$(wc -l <"$matches" | tr -d ' ')"
  [[ "$count" == 1 ]] || {
    printf 'FAIL manifest allocation %s occurs %s times; expected exactly once\n' \
      "$row_id" "$count" >&2
    exit 1
  }
  cat "$matches" >>"$manifest_rows"
}

manifest_row E4-TYPE-ENV-SERVICE-NAME
manifest_row E4-TYPE-ENV-SERVICE-TYPE-CODE
manifest_row E4-TYPE-ENV-SERVICE-KEY
manifest_row E4-TYPE-ENV-SERVICE-UNIVERSE

if grep -Fq -- '`required-closed`' "$manifest_rows"; then
  printf 'FAIL manifest allocation carries a manual required-closed override; closure must be generated\n' >&2
  exit 1
fi
require_text "$tmp_root/E4-TYPE-ENV-SERVICE-NAME.matches" '`status = generated`'
require_text "$tmp_root/E4-TYPE-ENV-SERVICE-TYPE-CODE.matches" '`status = generated`'
require_text "$tmp_root/E4-TYPE-ENV-SERVICE-KEY.matches" '`status = generated`'
require_text "$tmp_root/E4-TYPE-ENV-SERVICE-NAME.matches" \
  '`closureSource = generated/environment-context-key-assurance.tsv`'
require_text "$tmp_root/E4-TYPE-ENV-SERVICE-TYPE-CODE.matches" \
  '`closureSource = generated/environment-context-key-assurance.tsv`'
require_text "$tmp_root/E4-TYPE-ENV-SERVICE-KEY.matches" \
  '`closureSource = generated/environment-context-key-assurance.tsv`'
require_text "$tmp_root/E4-TYPE-ENV-SERVICE-KEY.matches" \
  '`orderBridgeLeafReceiptId = ENV-LEAF-KEY-ORDER-BRIDGE`'
require_text "$tmp_root/E4-TYPE-ENV-SERVICE-KEY.matches" \
  '`orderBridgeParentEdge = DATA-PG-ROW/ORDER`'
require_text "$tmp_root/E4-TYPE-ENV-SERVICE-KEY.matches" \
  '`orderBridgeClosureSource = generated/environment-context-key-assurance.tsv`'
require_text "$tmp_root/E4-TYPE-ENV-SERVICE-KEY.matches" \
  '`orderBridgeStatus = generated`'
require_text "$tmp_root/E4-TYPE-ENV-SERVICE-UNIVERSE.matches" \
  '`declarationJoinSource = generated/environment-context-key-assurance.tsv`'
require_text "$tmp_root/E4-TYPE-ENV-SERVICE-UNIVERSE.matches" \
  '`declarationJoinStatus = generated`'
require_text "$tmp_root/E4-TYPE-ENV-SERVICE-UNIVERSE.matches" '`required-open`'

require_text "$manifest_rows" '`Effect4.ServiceName`; `Effect4.Context.Key`'
require_text "$manifest_rows" '`Effect4.ServiceTypeCode`; `Effect4.Context.Key`'
require_text "$manifest_rows" '`Effect4.ServiceKey`; `Effect4.Context.Key`'
require_text "$manifest_rows" '`Effect4.ServiceUniverse`; `Effect4.Context.Key`'
require_text "$manifest_rows" 'leafReceiptId = ENV-LEAF-KEY-IDENTITY'
require_text "$manifest_rows" 'receiptId = ENV-AX-KEY'
require_text "$manifest_rows" 'evidenceId = ENV-EV-KEY-CONTRACT'
require_text "$manifest_rows" 'parentGraphEdge = ENV-PG-CONTEXT/identity'
require_text "$manifest_rows" 'orderBridgeLeafReceiptId = ENV-LEAF-KEY-ORDER-BRIDGE'
require_text "$manifest_rows" 'orderBridgeParentEdge = DATA-PG-ROW/ORDER'
require_text "$manifest_rows" 'proofGraphId = ENV-PG-CONTEXT'
require_text "$manifest_rows" 'nodeId = ENV-KEY-INTERP'

(
  cd -- "$repo_root"
  unset LEAN_PATH LEAN_SRC_PATH
  "$lake_bin" build Effect4Test.Environment.ContextKeyAssurance \
    >"$tmp_root/build.log" 2>&1
  "$lake_bin" env lean "$lean_contract_rel" \
    >"$tmp_root/contract.log" 2>&1
  "$lake_bin" env lean "$axiom_report_rel" \
    >"$tmp_root/axioms.log" 2>&1
  "$lake_bin" env lean "$driver_rel" \
    >"$tmp_root/driver.log" 2>&1
)

grep $'^E4CTX\t' "$tmp_root/driver.log" >"$tmp_root/evidence.rows" || {
  printf 'FAIL context-key evidence driver emitted no evidence rows\n' >&2
  cat "$tmp_root/driver.log" >&2
  exit 1
}
sed 's/^E4CTX\t//' "$tmp_root/evidence.rows" >"$tmp_root/evidence.tsv"

declaration_count="$(awk -F '\t' '$1 == "owned-declaration" { count++ } END { print count + 0 }' \
  "$tmp_root/evidence.tsv")"
api_count="$(awk -F '\t' '$1 == "api" { count++ } END { print count + 0 }' \
  "$tmp_root/evidence.tsv")"
theorem_count="$(awk -F '\t' '$1 == "theorem" { count++ } END { print count + 0 }' \
  "$tmp_root/evidence.tsv")"
order_bridge_api_count="$(awk -F '\t' '$1 == "order-bridge-api" { count++ } END { print count + 0 }' \
  "$tmp_root/evidence.tsv")"
order_bridge_theorem_count="$(awk -F '\t' '$1 == "order-bridge-theorem" { count++ } END { print count + 0 }' \
  "$tmp_root/evidence.tsv")"
order_bridge_receipt_count="$(awk -F '\t' '$1 == "order-bridge-receipt" { count++ } END { print count + 0 }' \
  "$tmp_root/evidence.tsv")"
axiom_count="$(awk -F '\t' '$1 == "axiom" { count++ } END { print count + 0 }' \
  "$tmp_root/evidence.tsv")"

[[ "$declaration_count" == 97 ]] || {
  printf 'FAIL context-key owned-declaration census emitted %s rows; expected 97\n' \
    "$declaration_count" >&2
  exit 1
}
[[ "$api_count" == 25 ]] || {
  printf 'FAIL context-key contracted API emitted %s rows; expected 25\n' \
    "$api_count" >&2
  exit 1
}
[[ "$theorem_count" == 8 ]] || {
  printf 'FAIL context-key theorem receipt emitted %s rows; expected 8\n' \
    "$theorem_count" >&2
  exit 1
}
[[ "$order_bridge_api_count" == 14 ]] || {
  printf 'FAIL Context Key Std order bridge API emitted %s rows; expected 14\n' \
    "$order_bridge_api_count" >&2
  exit 1
}
[[ "$order_bridge_theorem_count" == 7 ]] || {
  printf 'FAIL Context Key Std order bridge theorem receipt emitted %s rows; expected 7\n' \
    "$order_bridge_theorem_count" >&2
  exit 1
}
[[ "$order_bridge_receipt_count" == 8 ]] || {
  printf 'FAIL Context Key Std order bridge exact receipt emitted %s rows; expected 8\n' \
    "$order_bridge_receipt_count" >&2
  exit 1
}
[[ "$axiom_count" == 37 ]] || {
  printf 'FAIL context-key axiom receipt emitted %s rows; expected 37\n' \
    "$axiom_count" >&2
  exit 1
}

printf '%s\n' \
  $'Effect4.ServiceKey.Le\tEffect4.Context.Key\tENV-LEAF-KEY-ORDER-BRIDGE' \
  $'Effect4.ServiceKey.instLE\tEffect4.Context.Key\tENV-LEAF-KEY-ORDER-BRIDGE' \
  $'Effect4.ServiceKey.le_iff\tEffect4.Context.Key\tENV-LEAF-KEY-ORDER-BRIDGE' \
  $'Effect4.ServiceKey.instDecidableLE\tEffect4.Context.Key\tENV-LEAF-KEY-ORDER-BRIDGE' \
  $'Effect4.ServiceKey.lt_asymm\tEffect4.Context.Key\tENV-LEAF-KEY-ORDER-BRIDGE' \
  $'Effect4.ServiceKey.le_refl\tEffect4.Context.Key\tENV-LEAF-KEY-ORDER-BRIDGE' \
  $'Effect4.ServiceKey.le_trans\tEffect4.Context.Key\tENV-LEAF-KEY-ORDER-BRIDGE' \
  $'Effect4.ServiceKey.le_antisymm\tEffect4.Context.Key\tENV-LEAF-KEY-ORDER-BRIDGE' \
  $'Effect4.ServiceKey.le_total\tEffect4.Context.Key\tENV-LEAF-KEY-ORDER-BRIDGE' \
  $'Effect4.ServiceKey.lt_iff_le_not_le\tEffect4.Context.Key\tENV-LEAF-KEY-ORDER-BRIDGE' \
  $'Effect4.ServiceKey.instIsPreorder\tEffect4.Context.Key\tENV-LEAF-KEY-ORDER-BRIDGE' \
  $'Effect4.ServiceKey.instIsPartialOrder\tEffect4.Context.Key\tENV-LEAF-KEY-ORDER-BRIDGE' \
  $'Effect4.ServiceKey.instIsLinearOrder\tEffect4.Context.Key\tENV-LEAF-KEY-ORDER-BRIDGE' \
  $'Effect4.ServiceKey.instLawfulOrderLT\tEffect4.Context.Key\tENV-LEAF-KEY-ORDER-BRIDGE' \
  >"$tmp_root/expected-order-bridge-api.tsv"
awk -F '\t' '$1 == "order-bridge-api" { print $2 "\t" $3 "\t" $4 }' \
  "$tmp_root/evidence.tsv" >"$tmp_root/actual-order-bridge-api.tsv"
if ! cmp -s -- "$tmp_root/expected-order-bridge-api.tsv" \
    "$tmp_root/actual-order-bridge-api.tsv"; then
  printf 'FAIL Context Key Std order bridge API names/owners/receipt allocation drifted\n' >&2
  diff -u -- "$tmp_root/expected-order-bridge-api.tsv" \
    "$tmp_root/actual-order-bridge-api.tsv" >&2 || true
  exit 1
fi

printf '%s\n' \
  $'instance-synth\tLE Effect4.ServiceKey\tENV-LEAF-KEY-ORDER-BRIDGE' \
  $'instance-synth\tDecidable (a <= b) for Effect4.ServiceKey\tENV-LEAF-KEY-ORDER-BRIDGE' \
  $'instance-synth\tStd.IsLinearOrder Effect4.ServiceKey\tENV-LEAF-KEY-ORDER-BRIDGE' \
  $'instance-synth\tStd.LawfulOrderLT Effect4.ServiceKey\tENV-LEAF-KEY-ORDER-BRIDGE' \
  $'relation\ta <= b iff a < b or a = b\tENV-LEAF-KEY-ORDER-BRIDGE' \
  $'relation\ta < b iff a <= b and not b <= a\tENV-LEAF-KEY-ORDER-BRIDGE' \
  $'computation\tServiceKey(0,9) <= ServiceKey(1,0)\tENV-LEAF-KEY-ORDER-BRIDGE' \
  $'computation\tnot ServiceKey(1,0) <= ServiceKey(0,9)\tENV-LEAF-KEY-ORDER-BRIDGE' \
  >"$tmp_root/expected-order-bridge-receipts.tsv"
awk -F '\t' '$1 == "order-bridge-receipt" { print $2 "\t" $3 "\t" $4 }' \
  "$tmp_root/evidence.tsv" >"$tmp_root/actual-order-bridge-receipts.tsv"
if ! cmp -s -- "$tmp_root/expected-order-bridge-receipts.tsv" \
    "$tmp_root/actual-order-bridge-receipts.tsv"; then
  printf 'FAIL Context Key Std order bridge exact receipt set drifted\n' >&2
  diff -u -- "$tmp_root/expected-order-bridge-receipts.tsv" \
    "$tmp_root/actual-order-bridge-receipts.tsv" >&2 || true
  exit 1
fi

awk -F '\t' '$1 == "order-bridge-api" { print $2 }' "$tmp_root/evidence.tsv" \
  >"$tmp_root/order-bridge-api.names"
awk -F '\t' '$1 == "axiom" && $5 == "ENV-LEAF-KEY-ORDER-BRIDGE" { print $2 }' \
  "$tmp_root/evidence.tsv" >"$tmp_root/order-bridge-axiom.names"
if ! cmp -s -- "$tmp_root/order-bridge-api.names" \
    "$tmp_root/order-bridge-axiom.names"; then
  printf 'FAIL Context Key Std order bridge API does not have an exact axiom receipt set\n' >&2
  diff -u -- "$tmp_root/order-bridge-api.names" \
    "$tmp_root/order-bridge-axiom.names" >&2 || true
  exit 1
fi

awk '/^#print axioms / { print $3 }' "$repo_root/$axiom_report_rel" \
  >"$tmp_root/axiom-report.names"
awk -F '\t' '$1 == "axiom" { print $2 }' "$tmp_root/evidence.tsv" \
  >"$tmp_root/generated-axiom.names"
if ! cmp -s -- "$tmp_root/axiom-report.names" "$tmp_root/generated-axiom.names"; then
  printf 'FAIL generated axiom receipt names do not exactly match %s\n' \
    "$axiom_report_rel" >&2
  diff -u -- "$tmp_root/axiom-report.names" "$tmp_root/generated-axiom.names" >&2 || true
  exit 1
fi

printf 'format\teffect4-context-key-assurance-v1\n'
if [[ "$generation_mode" == "dry-run" ]]; then
  printf 'mode\tdry-run-manifest\tcloses-nothing\n'
fi
printf 'generator\t%s\tsha256=%s\n' \
  "$generator_rel" "$(sha256_file "$repo_root/$generator_rel")"
printf 'regenerate\t./%s > generated/environment-context-key-assurance.tsv\n' \
  "$generator_rel"
printf 'input\t%s\tsha256=%s\n' \
  "$key_source_rel" "$(sha256_file "$repo_root/$key_source_rel")"
printf 'input\t%s\tsha256=%s\n' \
  "$lean_contract_rel" "$(sha256_file "$repo_root/$lean_contract_rel")"
printf 'input\t%s\tsha256=%s\n' \
  "$axiom_report_rel" "$(sha256_file "$repo_root/$axiom_report_rel")"
printf 'input\t%s\tsha256=%s\n' \
  "$contract_rel" "$(sha256_file "$repo_root/$contract_rel")"
printf 'input\t%s\tsha256=%s\n' \
  "$assurance_rel" "$(sha256_file "$repo_root/$assurance_rel")"
printf 'input\t%s#E4-ENV-CE-001--006\tsha256=%s\n' \
  "$counterexample_register_rel" "$(sha256_file "$counterexample_rows")"
printf 'input\t%s\tsha256=%s\n' \
  "$counterexample_attacks_rel" "$(sha256_file "$repo_root/$counterexample_attacks_rel")"
printf 'input\t%s#environment-key-declaration-dispositions\tsha256=%s\n' \
  "$manifest_rel" "$(sha256_file "$manifest_rows")"
printf 'contract\tENV-EV-KEY-CONTRACT\t%s\trequired-closed\n' "$contract_rel"
for obligation_id in ENV-KEY-01 ENV-KEY-02 ENV-KEY-03 ENV-KEY-04; do
  printf 'obligation\t%s\t%s\trequired-closed\n' "$obligation_id" "$lean_contract_rel"
done
for suffix in 001 002 003 004 005 006; do
  printf 'counterexample\tE4-ENV-CE-%s\tSEEDED\t%s\t%s\n' \
    "$suffix" "$counterexample_register_rel" "$lean_contract_rel"
done
printf 'leaf\tENV-LEAF-KEY-IDENTITY\tpassive-key-family\trequired-closed\n'
printf 'leaf\tENV-LEAF-KEY-ORDER-BRIDGE\tderived-std-order-local-receipts\trequired-closed\n'
printf 'axiom-receipt\tENV-AX-KEY\t%s\trequired-closed\n' "$axiom_report_rel"
printf 'graph-attachment\tENV-PG-CONTEXT\tENV-KEY-INTERP\tEffect4.ServiceUniverse\trequired-open\n'
printf 'parent-link\tENV-LEAF-KEY-IDENTITY\tENV-PG-CONTEXT/identity\tEffect4.ServiceKey\trequired-closed\n'
printf 'parent-link\tENV-LEAF-KEY-ORDER-BRIDGE\tDATA-PG-ROW/ORDER\tEffect4.ServiceKey\trequired-open\n'
printf 'type\tE4-TYPE-ENV-SERVICE-NAME\tEffect4.ServiceName\tEffect4.Context.Key\tENV-LEAF-KEY-IDENTITY\trequired-closed\n'
printf 'type\tE4-TYPE-ENV-SERVICE-TYPE-CODE\tEffect4.ServiceTypeCode\tEffect4.Context.Key\tENV-LEAF-KEY-IDENTITY\trequired-closed\n'
printf 'type\tE4-TYPE-ENV-SERVICE-KEY\tEffect4.ServiceKey\tEffect4.Context.Key\tENV-LEAF-KEY-IDENTITY\trequired-closed\n'
printf 'type\tE4-TYPE-ENV-SERVICE-UNIVERSE\tEffect4.ServiceUniverse\tEffect4.Context.Key\tENV-PG-CONTEXT/ENV-KEY-INTERP\trequired-open\n'
cat "$tmp_root/evidence.tsv"
