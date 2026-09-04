#!/usr/bin/env bash
# Deterministic join for the implemented structural Schema proof graph shares.
set -euo pipefail

repo_root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd -P)"
generator_rel="scripts/generate-schema-structural-assurance.sh"
assurance_rel="Test/Schema/StructuralAssurance.lean"
axiom_report_rel="Test/Schema/AxiomReport.lean"
surface_rel="Test/Schema/PayloadSurface.lean"
pin_rel="vendor/effect-4.0.0-rc.112/src/SchemaRepresentation.ts"
register_rel="Test/Counterexamples/REGISTER.md"
attacks_rel="Test/Counterexamples/Schema/ATTACKS.md"
recursor_attack_rel="Test/Counterexamples/Schema/RecursiveElimination.lean"
annotation_attack_rel="Test/Counterexamples/Schema/AnnotationDataPlane.lean"
annotation_gate_rel="scripts/check-schema-annotations.sh"
effectful_attack_rel="Test/Counterexamples/Schema/EffectfulField.lean"
effectful_properties_attack_rel="Test/Counterexamples/Schema/EffectfulFieldProperties.lean"
effectful_gate_rel="scripts/check-schema-effectful-field.sh"

source_rels=(
  src/Effect4/Data/Optic.lean
  src/Effect4/Data/Json.lean
  src/Effect4/Schema/Payload.lean
  src/Effect4/Schema/Representation.lean
  src/Effect4/Schema/Annotations.lean
  src/Effect4/Schema/Document.lean
  src/Effect4/Schema/Check.lean
  src/Effect4/Codegen/Schema.lean
  src/Effect4/Schema/EffectfulField.lean
)
contract_rels=(
  Test/contracts/schema-representation.contract.md
  Test/contracts/schema-subalphabets.contract.md
  Test/contracts/schema-payload.contract.md
  Test/contracts/schema-recursor.contract.md
  Test/contracts/schema-annotations.contract.md
  Test/contracts/schema-effectful-field.contract.md
  Test/contracts/schema-effectful-field-properties.contract.md
)
battery_rels=(
  Test/Schema/RepresentationContract.lean
  Test/Schema/SubAlphabetContract.lean
  Test/Schema/PayloadContract.lean
  Test/Schema/RepresentationFoldContract.lean
  Test/Data/OpticContract.lean
  Test/Schema/AnnotationDataPlaneContract.lean
  Test/Schema/EffectfulFieldContract.lean
  Test/Schema/EffectfulFieldPropertiesContract.lean
)

expected_source_shas=(
  0a02907cd4e994ff180c2d11b090f7948481dc888812d85bdb892fb7c0adf78f
  49c8596a6a84ee3d35e1b1def69f3d665a559340effb2237996ecd4ec953c75e
  77dc812193a79c389d2a69e4ce3f6a3461c966e6487b273ae673258e4b65d18e
  a1037e5b38ae0eaf1c04efb46ea137d44569b7321b61dc73550d042023ce4fc3
  94fdb0e002c79fbaddd00f862f184f822373a0d33dda947ecb85443b3bd2beb7
  16ac1aaf3f7abff54b53f1fda0091969635a0bf4aad97f2e09bfdc0921f7e364
  49c40a2d14d5a18e04484403995ff236db0860a15f1c985e00e73ce0fbede9fe
  eee62e67b1602e1e86e4c64c009fbd3a1374d8a855484d76b98bd2e64fd86198
  2c54ef3ce3f1a60442b40c5cffe7bf850bd1bdc669cd7a6915bc9dd7666052b9
)
expected_contract_shas=(
  a2b85dd7ce72a8f74abfedeccb1142d7a85fa9913820fa8412c1410489ab90ee
  1b3d298d732be54c47108dafe914639bb5167eecc1d6b3dd27d50591fed65555
  aa7d193d778cbc8e1c6ddb616d14ed7fc856889178d201439a4e36f550000f89
  c70ff82cf5b55e18516e78db1f6720441920225390ad90e99e3e3c2dd115a4d3
  0414c65d3c1120d6be286d79a7cdd7b0334e97517604dde60795b9f9813726f8
  7703abd3d4533387faf5c0e482da8008e4c390f2a7a6145ad6b22879d51d03d2
  9c23feccc4762a50c2fa2806079758843ce40c460927020c4a0c870cfaa83f7c
)
expected_battery_shas=(
  fed90a2b7174a41546003dc77f248d8838935fd4ecef707e868a4705f85bcd61
  a57ed694dabe08754f28d32dc57252c49044e0c7a85ff13592eb8f968cefdf8a
  e80d4be2f6385228aa87766d61ad4056fef68f947d0347cc15e1ac9279c6d27f
  4de2a571131c843e83a036fcb518b45b2f1272caf3ec1467e601bc7e4510396b
  b65b86534af75ec8067bda3cb3a96bd58bf8dc541a3b28dd55ddd6b7608a8bc5
  1b2aa06d0940a6e48d2c4cdbacc6a9cb67745113d78ce07ee03bcae0090fcb67
  9293f80d81b41fb9d2e85c25f6e62bc2da9b889e8b7e9f57dce4f744265333b4
  504911bba1a85bf1aa5a07244ca415b510d5917d4b027c197ad355ed8d8d0eb3
)
expected_recursor_attack_sha="6625927071bd376f3088f2086c50f03d6440c3921e1fac94f7968d54e20197d9"
expected_annotation_attack_sha="7cc4b2518165952dfbd8bcde720025d1f4c589f2af1d0a177ba9a2112857694b"
expected_effectful_attack_sha="1a9c34f81e531faf4fb2c44aa7a27bb20fbab9c16ebf91e638fc4ca6d3cef6f1"
expected_effectful_properties_attack_sha="3a63c61023f4d0b1cd74fa2911dabd277a99693492a5b2efa45ecf9a2aa4cabd"
expected_surface_sha="039055e0302c7747e63a9ac8e3b63635e6a212c6ad18a60caabd6dfb44a20df8"
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
  "$recursor_attack_rel" "$annotation_attack_rel" "$annotation_gate_rel"
  "$effectful_attack_rel" "$effectful_properties_attack_rel" "$effectful_gate_rel"
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
actual_recursor_attack_sha="$(sha256_file "$repo_root/$recursor_attack_rel")"
[[ "$actual_recursor_attack_sha" == "$expected_recursor_attack_sha" ]] || {
  printf 'FAIL frozen Schema recursor attack drifted: expected %s, found %s\n' \
    "$expected_recursor_attack_sha" "$actual_recursor_attack_sha" >&2
  exit 1
}
actual_annotation_attack_sha="$(sha256_file "$repo_root/$annotation_attack_rel")"
[[ "$actual_annotation_attack_sha" == "$expected_annotation_attack_sha" ]] || {
  printf 'FAIL frozen Schema annotation attack drifted: expected %s, found %s\n' \
    "$expected_annotation_attack_sha" "$actual_annotation_attack_sha" >&2
  exit 1
}
actual_effectful_attack_sha="$(sha256_file "$repo_root/$effectful_attack_rel")"
[[ "$actual_effectful_attack_sha" == "$expected_effectful_attack_sha" ]] || {
  printf 'FAIL frozen Schema annotation attack drifted: expected %s, found %s\n' \
    "$expected_effectful_attack_sha" "$actual_effectful_attack_sha" >&2
  exit 1
}
actual_effectful_properties_attack_sha="$(sha256_file "$repo_root/$effectful_properties_attack_rel")"
[[ "$actual_effectful_properties_attack_sha" == "$expected_effectful_properties_attack_sha" ]] || {
  printf 'FAIL frozen Schema annotation attack drifted: expected %s, found %s\n' \
    "$expected_effectful_properties_attack_sha" "$actual_effectful_properties_attack_sha" >&2
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
  "$lake_bin" env lean "$recursor_attack_rel" >"$tmp_root/RecursiveElimination.log" 2>&1
  "$lake_bin" env lean "$annotation_attack_rel" >"$tmp_root/AnnotationDataPlane.log" 2>&1
  "$repo_root/$annotation_gate_rel" >"$tmp_root/annotations-host.log" 2>&1
  "$lake_bin" env lean "$effectful_attack_rel" >"$tmp_root/EffectfulField.log" 2>&1
  "$lake_bin" env lean "$effectful_properties_attack_rel" >"$tmp_root/EffectfulFieldProperties.log" 2>&1
  "$repo_root/$effectful_gate_rel" >"$tmp_root/effectful-field-host.log" 2>&1
  "$lake_bin" env lean "$axiom_report_rel" >"$tmp_root/AxiomReport.log" 2>&1
  "$lake_bin" env lean "$assurance_rel" >"$tmp_root/assurance.log" 2>&1
)

awk -F '\t' '$1 == "E4SCHEMA" { $1 = ""; sub(/^\t/, ""); print }' \
  OFS='\t' "$tmp_root/assurance.log" >"$tmp_root/evidence.tsv"

evidence_count() {
  awk -F '\t' -v kind="$1" '$1 == kind { count++ } END { print count + 0 }' \
    "$tmp_root/evidence.tsv"
}
[[ "$(evidence_count owned-declaration)" == 1426 ]] || {
  printf 'FAIL Schema owned declaration census is not exactly 1426 rows (found %s)\n' "$(evidence_count owned-declaration)" >&2; exit 1; }
[[ "$(evidence_count theorem)" == 557 ]] || {
  printf 'FAIL Schema theorem census is not exactly 557 rows (found %s)\n' "$(evidence_count theorem)" >&2; exit 1; }
[[ "$(evidence_count axiom)" == 557 ]] || {
  printf 'FAIL Schema axiom census is not exactly 557 rows (found %s)\n' "$(evidence_count axiom)" >&2; exit 1; }
[[ "$(evidence_count absent)" == 9 ]] || {
  printf 'FAIL Schema duplicate-prevention census is not exactly 9 rows (found %s)\n' "$(evidence_count absent)" >&2; exit 1; }

printf '%s\n' \
  $'Effect4.Data.Optic\t113' \
  $'Effect4.Data.Json\t124' \
  $'Effect4.Schema.Payload\t255' \
  $'Effect4.Schema.Representation\t585' \
  $'Effect4.Schema.Annotations\t63' \
  $'Effect4.Schema.Document\t62' \
  $'Effect4.Schema.Check\t142' \
  $'Effect4.Schema.EffectfulField\t82' >"$tmp_root/expected-module-counts.tsv"
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
[[ "$(wc -l <"$tmp_root/report.names" | tr -d ' ')" == 188 ]] || {
  printf 'FAIL curated Schema axiom report no longer contains exactly 188 names\n' >&2; exit 1; }
awk -F '\t' '$1 == "theorem" { print $2 }' "$tmp_root/evidence.tsv" \
  >"$tmp_root/theorem.names"
awk -F '\t' '$1 == "owned-declaration" { print $2 }' "$tmp_root/evidence.tsv" \
  >"$tmp_root/declaration.names"
printf '%s\n' \
  Effect4.Representation.FoldAlgebra \
  Effect4.Representation.fold \
  Effect4.Check.fold \
  Effect4.Representation.FoldAlgebra.rebuild \
  >"$tmp_root/axiom-free-recursor-declarations.names"
while IFS= read -r theorem_name; do
  theorem_count="$(grep -Fxc -- "$theorem_name" "$tmp_root/theorem.names" || true)"
  definition_count=0
  if grep -Fxq -- "$theorem_name" "$tmp_root/axiom-free-recursor-declarations.names"; then
    definition_count="$(grep -Fxc -- "$theorem_name" "$tmp_root/declaration.names" || true)"
  fi
  count=$((theorem_count + definition_count))
  [[ "$count" == 1 ]] || {
    printf 'FAIL curated Schema axiom subject %s has %s exhaustive-census receipts; expected one\n' \
      "$theorem_name" "$count" >&2
    exit 1
  }
done <"$tmp_root/report.names"

: >"$tmp_root/counterexamples.tsv"
for suffix in $(seq -w 17 55); do
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
printf 'counterexample-battery\t%s\tsha256=%s\trequired-closed\n' \
  "$recursor_attack_rel" "$expected_recursor_attack_sha"
printf 'counterexample-battery\t%s\tsha256=%s\trequired-closed\n' \
  "$annotation_attack_rel" "$expected_annotation_attack_sha"
printf 'counterexample-battery\t%s\tsha256=%s\trequired-closed\n' \
  "$effectful_attack_rel" "$expected_effectful_attack_sha"
printf 'counterexample-battery\t%s\tsha256=%s\trequired-closed\n' \
  "$effectful_properties_attack_rel" "$expected_effectful_properties_attack_sha"
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
printf 'gate\tSCHEMA-ANNOTATION-HOST\t%s\trequired-closed\n' "$annotation_gate_rel"
printf 'gate\tSCHEMA-EFFECTFUL-FIELD-HOST\t%s\trequired-closed\n' "$effectful_gate_rel"

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
graph-edge	SCHEMA-PG-PAYLOAD/SC-REP-03-RECURSOR	SCHEMA-PAYLOAD-GENERAL-RECURSOR	required-closed
graph-edge	SCHEMA-PG-FIELD-ADMISSION/SC-REP-04	SCHEMA-FIELD-ADMISSION-RECURSIVE	required-closed
graph-edge	DATA-PG-OPTIC/composition	OPTIC-LAWFUL-COMPOSITION	required-closed
graph-edge	DATA-PG-OPTIC/conversion	OPTIC-LAWFUL-CONVERSION	required-closed
graph-edge	DATA-PG-OPTIC/trust	OPTIC-AXIOM-FREE-LAWS	required-closed
graph-edge	SCHEMA-PG-ANNOTATION-DATA/typed-keys	ANNOTATION-EXACT-PARTIAL-ISOMORPHISM	required-closed
graph-edge	SCHEMA-PG-ANNOTATION-DATA/local-optics	ANNOTATION-LOCAL-VIEWS	required-closed
graph-edge	SCHEMA-PG-ANNOTATION-DATA/recursive-traversal	ANNOTATION-EXHAUSTIVE-STRUCTURAL-WALK	required-closed
graph-edge	SCHEMA-PG-ANNOTATION-DATA/counterexamples	E4-SCHEMA-CE-044-048	required-closed
graph-edge	SCHEMA-PG-ANNOTATION-DATA/host	SCHEMA-ANNOTATION-HOST	required-closed
graph-edge	SCHEMA-PG-ANNOTATION-DATA/trust	ANNOTATION-AXIOM-FREE-LAWS	required-closed
graph-edge	SCHEMA-PG-EFFECTFUL-FIELD/marker-codec	EFFECTFUL-FIELD-MARKER-CODEC	required-closed
graph-edge	SCHEMA-PG-EFFECTFUL-FIELD/occurrence-admission	EFFECTFUL-FIELD-RAW-OCCURRENCE-ADMISSION	required-closed
graph-edge	SCHEMA-PG-EFFECTFUL-FIELD/identity	EFFECTFUL-FIELD-IDENTITY-AGREEMENT	required-closed
graph-edge	SCHEMA-PG-EFFECTFUL-FIELD/program-equations	EFFECTFUL-FIELD-PROGRAM-EQUATIONS	required-closed
graph-edge	SCHEMA-PG-EFFECTFUL-FIELD/interpretation	EFFECTFUL-FIELD-INTERPRET-PRESERVATION	required-closed
graph-edge	SCHEMA-PG-EFFECTFUL-FIELD/counterexamples	E4-SCHEMA-CE-049-055	required-closed
graph-edge	SCHEMA-PG-EFFECTFUL-FIELD/host	SCHEMA-EFFECTFUL-FIELD-HOST	required-closed
graph-edge	SCHEMA-PG-EFFECTFUL-FIELD/trust	EFFECTFUL-FIELD-AXIOM-CEILING	required-closed
graph-status	SCHEMA-PG-REPRESENTATION-TAG	all-applicable-edges-closed	required-closed
graph-status	SCHEMA-PG-PAYLOAD	all-applicable-edges-closed	required-closed
graph-status	SCHEMA-PG-FIELD-ADMISSION	recursive-judgment-closed	required-closed
graph-status	DATA-PG-OPTIC	all-applicable-edges-closed	required-closed
graph-status	SCHEMA-PG-ANNOTATION-DATA	all-applicable-edges-closed	required-closed
graph-status	SCHEMA-PG-EFFECTFUL-FIELD	all-applicable-edges-closed	required-closed
external-open	SCHEMA-PG-DOCUMENT	reference-semantics	required-open
external-open	SCHEMA-PG-WIRE	codec-and-canonicalization	required-open
EOF
