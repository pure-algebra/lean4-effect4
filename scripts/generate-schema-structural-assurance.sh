#!/usr/bin/env bash
# Deterministic join for the implemented structural Schema proof graph shares.
set -euo pipefail

repo_root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd -P)"
generator_rel="scripts/generate-schema-structural-assurance.sh"
assurance_rel="Effect4Test/Schema/StructuralAssurance.lean"
axiom_report_rel="Effect4Test/Schema/AxiomReport.lean"
surface_rel="Effect4Test/Schema/PayloadSurface.lean"
pin_rel="vendor/effect-4.0.0-rc.112/src/SchemaRepresentation.ts"
register_rel="test/counterexamples/REGISTER.md"
attacks_rel="test/counterexamples/schema/ATTACKS.md"

source_rels=(
  Effect4/Data/Json.lean
  Effect4/Schema/Payload.lean
  Effect4/Schema/Representation.lean
  Effect4/Schema/Document.lean
  Effect4/Schema/Check.lean
)
contract_rels=(
  test/contracts/schema-representation.contract.md
  test/contracts/schema-subalphabets.contract.md
  test/contracts/schema-payload.contract.md
)
battery_rels=(
  Effect4Test/Schema/RepresentationContract.lean
  Effect4Test/Schema/SubAlphabetContract.lean
  Effect4Test/Schema/PayloadContract.lean
)

expected_source_shas=(
  8714c8fbb3a3e3ba3bee94ed392bc32abe5367e9a468f5c0817e86d01926d330
  a6292ad42ae08a49ff2b438dc57b16c6361b6980b75286fe61657db7b07822dc
  05ef472aaced4a688465ac65d7ee0f9a4c349dbe896a6e494a9dbcc2713edd43
  fc86b4ba9a6ce2d7b0bb912588c54429e46a7cfb509287a5fc2a650e1a20e6ad
  98439bbd47195d266a188345dc749fbd9aa11bb1499d2944476dde78c8c2a9ef
)
expected_contract_shas=(
  a2b85dd7ce72a8f74abfedeccb1142d7a85fa9913820fa8412c1410489ab90ee
  1b3d298d732be54c47108dafe914639bb5167eecc1d6b3dd27d50591fed65555
  7b70c82199c46cd45f312f62f0cf81a276a8a759ec94457c08dd99639888f274
)
expected_battery_shas=(
  fed90a2b7174a41546003dc77f248d8838935fd4ecef707e868a4705f85bcd61
  a57ed694dabe08754f28d32dc57252c49044e0c7a85ff13592eb8f968cefdf8a
  e80d4be2f6385228aa87766d61ad4056fef68f947d0347cc15e1ac9279c6d27f
)
expected_surface_sha="500bb9b2e95362d14440d4a8cc5e990e52c6864548e11acb2186cc5ecc390493"
expected_pin_sha="a0a7a1537cfe3a9159a80210e3de92342cc9e98651f0e8273a75ccdcccae69bc"

generation_mode="production"
payload_contract_source="$repo_root/${contract_rels[2]}"
if [[ $# -gt 0 ]]; then
  if [[ $# -eq 2 && "$1" == "--dry-run-contract" ]]; then
    generation_mode="dry-run-contract"
    payload_contract_source="$2"
  else
    printf 'usage: generate-schema-structural-assurance.sh [--dry-run-contract <schema-payload.contract.md>]\n' >&2
    exit 2
  fi
fi

for override_name in \
    EFFECT4_SCHEMA_STRUCTURAL_SOURCE \
    EFFECT4_SCHEMA_STRUCTURAL_CONTRACT \
    EFFECT4_SCHEMA_STRUCTURAL_BATTERY \
    EFFECT4_SCHEMA_STRUCTURAL_DRIVER \
    EFFECT4_SCHEMA_STRUCTURAL_PIN; do
  if [[ -n "${!override_name-}" ]]; then
    printf 'FAIL Schema structural assurance generator rejects source override variable %s\n' \
      "$override_name" >&2
    exit 2
  fi
done

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

required_rels=(
  "$generator_rel" "$assurance_rel" "$axiom_report_rel" "$surface_rel"
  "$pin_rel" "$register_rel" "$attacks_rel"
  scripts/check-schema-census.sh scripts/check-schema-fields.sh
  scripts/check-schema-payload-surface.sh scripts/test-schema-payload-surface-gate.sh
  "${source_rels[@]}" "${contract_rels[@]}" "${battery_rels[@]}"
)
for rel in "${required_rels[@]}"; do
  required="$repo_root/$rel"
  [[ -f "$required" && ! -L "$required" ]] || {
    printf 'FAIL required Schema structural assurance input is absent, not regular, or a symlink: %s\n' \
      "$required" >&2
    exit 1
  }
done
[[ -f "$payload_contract_source" && ! -L "$payload_contract_source" ]] || {
  printf 'FAIL dry-run Schema payload contract is absent, not regular, or a symlink\n' >&2
  exit 1
}

lake_bin="$(command -v lake || true)"
[[ -n "$lake_bin" ]] || { printf 'FAIL lake is unavailable\n' >&2; exit 1; }

tmp_parent="${TMPDIR:-/tmp}"
tmp_parent="${tmp_parent%/}"
tmp_root="$(mktemp -d "$tmp_parent/effect4-schema-structural-assurance.XXXXXX")"
cleanup() {
  local cleanup_rc=$?
  set +e
  case "$tmp_root" in
    "$tmp_parent"/effect4-schema-structural-assurance.*) rm -rf -- "$tmp_root" ;;
    *) printf 'FAIL refusing to remove unexpected path: %s\n' "$tmp_root" >&2; cleanup_rc=1 ;;
  esac
  exit "$cleanup_rc"
}
trap cleanup EXIT

if grep -Fq 'required-closed' "$payload_contract_source"; then
  printf 'FAIL Schema authored payload contract carries a manual required-closed override\n' >&2
  exit 1
fi

for i in "${!source_rels[@]}"; do
  actual="$(sha256_file "$repo_root/${source_rels[$i]}")"
  [[ "$actual" == "${expected_source_shas[$i]}" ]] || {
    printf 'FAIL frozen Schema source %s drifted: expected %s, found %s\n' \
      "${source_rels[$i]}" "${expected_source_shas[$i]}" "$actual" >&2
    exit 1
  }
done
for i in "${!contract_rels[@]}"; do
  contract_source="$repo_root/${contract_rels[$i]}"
  if [[ "$i" == 2 ]]; then contract_source="$payload_contract_source"; fi
  actual="$(sha256_file "$contract_source")"
  [[ "$actual" == "${expected_contract_shas[$i]}" ]] || {
    printf 'FAIL frozen Schema contract %s drifted: expected %s, found %s\n' \
      "${contract_rels[$i]}" "${expected_contract_shas[$i]}" "$actual" >&2
    exit 1
  }
done
for i in "${!battery_rels[@]}"; do
  actual="$(sha256_file "$repo_root/${battery_rels[$i]}")"
  [[ "$actual" == "${expected_battery_shas[$i]}" ]] || {
    printf 'FAIL frozen Schema battery %s drifted: expected %s, found %s\n' \
      "${battery_rels[$i]}" "${expected_battery_shas[$i]}" "$actual" >&2
    exit 1
  }
done
actual_surface_sha="$(sha256_file "$repo_root/$surface_rel")"
[[ "$actual_surface_sha" == "$expected_surface_sha" ]] || {
  printf 'FAIL repaired Schema payload surface checker drifted: expected %s, found %s\n' \
    "$expected_surface_sha" "$actual_surface_sha" >&2
  exit 1
}
actual_pin_sha="$(sha256_file "$repo_root/$pin_rel")"
[[ "$actual_pin_sha" == "$expected_pin_sha" ]] || {
  printf 'FAIL vendored rc.112 Schema source pin drifted: expected %s, found %s\n' \
    "$expected_pin_sha" "$actual_pin_sha" >&2
  exit 1
}

(
  cd -- "$repo_root"
  unset LEAN_PATH LEAN_SRC_PATH
  ./scripts/check-schema-census.sh "$pin_rel" >"$tmp_root/census.log" 2>&1
  ./scripts/check-schema-fields.sh "$pin_rel" >"$tmp_root/fields.log" 2>&1
  ./scripts/check-schema-payload-surface.sh >"$tmp_root/surface.log" 2>&1
  ./scripts/test-schema-payload-surface-gate.sh >"$tmp_root/surface-reaction.log" 2>&1
  for battery in "${battery_rels[@]}"; do
    "$lake_bin" env lean "$battery" >"$tmp_root/$(basename "$battery").log" 2>&1
  done
  "$lake_bin" env lean "$assurance_rel" >"$tmp_root/assurance.log" 2>&1
)

awk -F '\t' '$1 == "E4SCHEMA" { $1 = ""; sub(/^\t/, ""); print }' \
  OFS='\t' "$tmp_root/assurance.log" >"$tmp_root/evidence.tsv"

evidence_count() {
  awk -F '\t' -v kind="$1" '$1 == kind { count++ } END { print count + 0 }' \
    "$tmp_root/evidence.tsv"
}
[[ "$(evidence_count owned-declaration)" == 1092 ]] || {
  printf 'FAIL Schema owned declaration census is not exactly 1092 rows\n' >&2; exit 1; }
[[ "$(evidence_count theorem)" == 418 ]] || {
  printf 'FAIL Schema theorem census is not exactly 418 rows\n' >&2; exit 1; }
[[ "$(evidence_count axiom)" == 418 ]] || {
  printf 'FAIL Schema axiom census is not exactly 418 rows\n' >&2; exit 1; }
[[ "$(evidence_count absent)" == 9 ]] || {
  printf 'FAIL Schema duplicate-prevention census is not exactly 9 rows\n' >&2; exit 1; }

printf '%s\n' \
  $'Effect4.Data.Json\t122' \
  $'Effect4.Schema.Payload\t255' \
  $'Effect4.Schema.Representation\t518' \
  $'Effect4.Schema.Document\t56' \
  $'Effect4.Schema.Check\t141' >"$tmp_root/expected-module-counts.tsv"
awk -F '\t' '$1 == "owned-declaration" { count[$3]++ }
  END { for (owner in count) print owner "\t" count[owner] }' \
  "$tmp_root/evidence.tsv" | LC_ALL=C sort >"$tmp_root/actual-module-counts.tsv"
LC_ALL=C sort "$tmp_root/expected-module-counts.tsv" -o "$tmp_root/expected-module-counts.tsv"
if ! cmp -s "$tmp_root/expected-module-counts.tsv" "$tmp_root/actual-module-counts.tsv"; then
  printf 'FAIL exact Schema per-module declaration counts drifted\n' >&2
  diff -u "$tmp_root/expected-module-counts.tsv" "$tmp_root/actual-module-counts.tsv" >&2 || true
  exit 1
fi

if awk -F '\t' '$1 == "axiom" && $3 != "none" && $3 != "propext" &&
    $3 != "Quot.sound" && $3 != "Quot.sound,propext" { print; bad=1 }
    END { exit bad ? 0 : 1 }' "$tmp_root/evidence.tsv" >"$tmp_root/forbidden-axioms.tsv"; then
  printf 'FAIL Schema axiom receipt exceeds [propext, Quot.sound]\n' >&2
  cat "$tmp_root/forbidden-axioms.tsv" >&2
  exit 1
fi

awk '/^#print axioms / { print $3 }' "$repo_root/$axiom_report_rel" \
  >"$tmp_root/report.names"
[[ "$(wc -l <"$tmp_root/report.names" | tr -d ' ')" == 139 ]] || {
  printf 'FAIL curated Schema axiom report no longer contains exactly 139 names\n' >&2; exit 1; }
awk -F '\t' '$1 == "theorem" { print $2 }' "$tmp_root/evidence.tsv" \
  >"$tmp_root/theorem.names"
while IFS= read -r theorem_name; do
  count="$(grep -Fxc -- "$theorem_name" "$tmp_root/theorem.names" || true)"
  [[ "$count" == 1 ]] || {
    printf 'FAIL curated Schema theorem %s has %s exhaustive-census receipts; expected one\n' \
      "$theorem_name" "$count" >&2
    exit 1
  }
done <"$tmp_root/report.names"

: >"$tmp_root/counterexamples.tsv"
for suffix in $(seq -w 17 42); do
  counterexample_id="E4-SCHEMA-CE-0$suffix"
  row="$(grep -F "| \`$counterexample_id\` |" "$repo_root/$register_rel" || true)"
  [[ "$(printf '%s\n' "$row" | grep -c . || true)" == 1 ]] || {
    printf 'FAIL Schema counterexample %s does not have exactly one register row\n' \
      "$counterexample_id" >&2
    exit 1
  }
  status="$(printf '%s\n' "$row" | awk -F '|' '{ gsub(/^ +| +$/, "", $3); print $3 }')"
  [[ "$status" == "SEEDED" || "$status" == "PINNED" ]] || {
    printf 'FAIL Schema counterexample %s has inadmissible status %s\n' \
      "$counterexample_id" "$status" >&2
    exit 1
  }
  printf 'counterexample\t%s\t%s\t%s\trequired-closed\n' \
    "$counterexample_id" "$status" "$register_rel" >>"$tmp_root/counterexamples.tsv"
done

printf 'format\teffect4-schema-structural-assurance-v1\n'
if [[ "$generation_mode" == "dry-run-contract" ]]; then
  printf 'mode\tdry-run-contract\tcloses-nothing\n'
fi
printf 'generator\t%s\tsha256=%s\n' "$generator_rel" \
  "$(sha256_file "$repo_root/$generator_rel")"
printf 'regenerate\t./scripts/generate-schema-structural-assurance.sh > generated/schema-structural-assurance.tsv\n'
for i in "${!source_rels[@]}"; do
  printf 'input\t%s\tsha256=%s\n' "${source_rels[$i]}" "${expected_source_shas[$i]}"
done
for i in "${!contract_rels[@]}"; do
  printf 'input\t%s\tsha256=%s\n' "${contract_rels[$i]}" "${expected_contract_shas[$i]}"
done
for i in "${!battery_rels[@]}"; do
  printf 'battery\t%s\tsha256=%s\trequired-closed\n' \
    "${battery_rels[$i]}" "${expected_battery_shas[$i]}"
done
printf 'input\t%s\tsha256=%s\n' "$surface_rel" "$expected_surface_sha"
printf 'input\t%s\tsha256=%s\n' "$assurance_rel" \
  "$(sha256_file "$repo_root/$assurance_rel")"
printf 'input\t%s\tsha256=%s\n' "$axiom_report_rel" \
  "$(sha256_file "$repo_root/$axiom_report_rel")"
printf 'source-pin\teffect@4.0.0-rc.112\t%s\tsha256=%s\trequired-closed\n' \
  "$pin_rel" "$expected_pin_sha"
printf 'gate\tSC-REP-CENSUS-PIN\tscripts/check-schema-census.sh\trequired-closed\n'
printf 'gate\tSC-REP-FIELD-PIN\tscripts/check-schema-fields.sh\trequired-closed\n'
printf 'gate\tSCHEMA-PAYLOAD-SURFACE\tscripts/check-schema-payload-surface.sh\trequired-closed\n'
printf 'detector\tSCHEMA-PAYLOAD-SURFACE-REACTION\tscripts/test-schema-payload-surface-gate.sh\t13-of-13\trequired-closed\n'

cat "$tmp_root/counterexamples.tsv"
cat "$tmp_root/evidence.tsv"

cat <<'EOF'
leaf	SCHEMA-LEAF-UNION-MODE	finite-local-receipts	required-closed
leaf	SCHEMA-LEAF-CHECK-TAG	finite-local-receipts	required-closed
leaf	SCHEMA-LEAF-LITERAL-KIND	finite-local-receipts	required-closed
leaf	SCHEMA-LEAF-ENUM-VALUE-KIND	finite-local-receipts	required-closed
leaf	SCHEMA-LEAF-PROPERTY-KEY-KIND	finite-local-receipts	required-closed
leaf	SCHEMA-LEAF-FLOAT64-BITS	bit-bijection-and-finiteness	required-closed
leaf	SCHEMA-LEAF-PAYLOAD-SCALARS	exact-carriers-and-local-laws	required-closed
leaf	SCHEMA-LEAF-PAYLOAD-RECORDS	exact-record-surfaces	required-closed
leaf	SCHEMA-LEAF-DOCUMENT-CONTAINERS	exact-containers-and-toMulti	required-closed
graph-edge	SCHEMA-PG-REPRESENTATION-TAG/identity	SCHEMA-TAG-IDENTITY	required-closed
graph-edge	SCHEMA-PG-REPRESENTATION-TAG/construction	SCHEMA-TAG-CONSTRUCTION	required-closed
graph-edge	SCHEMA-PG-REPRESENTATION-TAG/semantics	SCHEMA-TAG-SEMANTICS	not-applicable
graph-edge	SCHEMA-PG-REPRESENTATION-TAG/laws	SCHEMA-TAG-LAWS	not-applicable
graph-edge	SCHEMA-PG-REPRESENTATION-TAG/representation	SCHEMA-TAG-REPRESENTATION	required-closed
graph-edge	SCHEMA-PG-REPRESENTATION-TAG/counterexamples	SCHEMA-TAG-COUNTEREXAMPLES	required-closed
graph-edge	SCHEMA-PG-REPRESENTATION-TAG/bridges	SCHEMA-TAG-BRIDGES	not-applicable
graph-edge	SCHEMA-PG-REPRESENTATION-TAG/targets	SCHEMA-TAG-TARGETS	not-applicable
graph-edge	SCHEMA-PG-REPRESENTATION-TAG/trust	SCHEMA-TAG-TRUST	required-closed
graph-edge	SCHEMA-PG-REPRESENTATION-TAG/coverage	SCHEMA-TAG-COVERAGE	required-closed
graph-attachment	SCHEMA-PG-PAYLOAD/SCHEMA-LEAF-FLOAT64-BITS	required-closed
graph-attachment	SCHEMA-PG-PAYLOAD/SCHEMA-NODE-JSON-FINITENESS	required-closed
graph-attachment	SCHEMA-PG-PAYLOAD/SCHEMA-LEAF-PAYLOAD-SCALARS	required-closed
graph-attachment	SCHEMA-PG-PAYLOAD/SCHEMA-LEAF-PAYLOAD-RECORDS	required-closed
graph-attachment	SCHEMA-PG-PAYLOAD/SCHEMA-LEAF-DOCUMENT-CONTAINERS	required-closed
graph-edge	SCHEMA-PG-PAYLOAD/SC-REP-01	SCHEMA-PAYLOAD-DECLARATION-COVERAGE	required-closed
graph-edge	SCHEMA-PG-PAYLOAD/SC-REP-03-STRUCTURAL	SCHEMA-PAYLOAD-EQUALITY-TAG-PROJECTION	required-closed
graph-edge	SCHEMA-PG-PAYLOAD/SC-REP-03-RECURSOR	SCHEMA-PAYLOAD-GENERAL-RECURSOR	required-open
graph-edge	SCHEMA-PG-FIELD-ADMISSION/SC-REP-04	SCHEMA-FIELD-ADMISSION-RECURSIVE	required-closed
graph-status	SCHEMA-PG-REPRESENTATION-TAG	all-applicable-edges-closed	required-closed
graph-status	SCHEMA-PG-PAYLOAD	general-recursor-remains-open	required-open
graph-status	SCHEMA-PG-FIELD-ADMISSION	recursive-judgment-closed	required-closed
external-open	SCHEMA-PG-DOCUMENT	reference-semantics	required-open
external-open	SCHEMA-PG-WIRE	codec-and-canonicalization	required-open
EOF

