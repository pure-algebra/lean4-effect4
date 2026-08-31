#!/usr/bin/env bash
# Exercises whether `scripts/check-schema-fields.sh` reacts to specified drift.
#
# This exercises the DETECTOR, not the field set. It runs against a synthetic
# fixture, so a pass here says nothing about Effect's real persisted fields or
# semantics; it says only that the twelve named source mutations and three
# invocation-safety cases cannot return a vacuous success.
set -euo pipefail

repo_root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd -P)"
gate="$repo_root/scripts/check-schema-fields.sh"
fixture="$repo_root/test/fixtures/schema-fields/reference.ts"
expected="$repo_root/test/fixtures/schema-fields/expected.txt"
tmp_parent="${TMPDIR:-/tmp}"
tmp_parent="${tmp_parent%/}"
tmp_root="$(mktemp -d "$tmp_parent/effect4-fields-gate.XXXXXX")"
fixture_before="$tmp_root/fixture.before"
expected_before="$tmp_root/expected.before"

cleanup() {
  local status=$?
  set +e
  if [[ -f "$fixture_before" ]] && ! cmp -s -- "$fixture_before" "$fixture"; then
    printf 'FAIL fixture changed while the gate tests ran\n' >&2
    status=1
  fi
  if [[ -f "$expected_before" ]] && ! cmp -s -- "$expected_before" "$expected"; then
    printf 'FAIL expected table changed while the gate tests ran\n' >&2
    status=1
  fi
  case "$tmp_root" in
    "$tmp_parent"/effect4-fields-gate.*) rm -rf -- "$tmp_root" ;;
    *) printf 'FAIL refusing to remove unexpected path: %s\n' "$tmp_root" >&2; status=1 ;;
  esac
  exit "$status"
}
trap cleanup EXIT

[[ -x "$gate" ]] || { printf 'FAIL gate is not executable: %s\n' "$gate" >&2; exit 1; }
[[ -f "$fixture" ]] || { printf 'FAIL fixture is missing: %s\n' "$fixture" >&2; exit 1; }
[[ -f "$expected" ]] || { printf 'FAIL expected table is missing: %s\n' "$expected" >&2; exit 1; }
cp -- "$fixture" "$fixture_before"
cp -- "$expected" "$expected_before"

expect_reject() {
  local name="$1" candidate="$2" signal="$3"
  local log="$tmp_root/$name.log"
  if "$gate" --dry-run --expect "$expected" "$candidate" >"$log" 2>&1; then
    printf 'FAIL gate accepted a mutant it must reject: %s\n' "$name" >&2
    cat "$log" >&2
    exit 1
  fi
  if ! grep -Fq -- "$signal" "$log"; then
    printf 'FAIL %s was rejected, but the expected signal was absent: %s\n' "$name" "$signal" >&2
    cat "$log" >&2
    exit 1
  fi
  printf 'PASS rejected: %s\n' "$name"
}

baseline="$tmp_root/baseline.ts"
cp -- "$fixture" "$baseline"
if ! "$gate" --dry-run --expect "$expected" "$baseline" >"$tmp_root/baseline.log" 2>&1; then
  printf 'FAIL the unmutated fixture did not pass the gate\n' >&2
  cat "$tmp_root/baseline.log" >&2
  exit 1
fi
grep -Fq 'remains OPEN' "$tmp_root/baseline.log" || {
  printf 'FAIL a dry run must state that SC-REP-FIELD-PIN remains open\n' >&2
  exit 1
}
printf 'PASS baseline fixture accepted, and reported as closing nothing\n'

drift='persisted field spelling drift'

# 1. a persisted field is renamed
sed 's/^  thunk:/  thunkk:/' "$fixture" >"$tmp_root/m1.ts"
expect_reject "renamed field" "$tmp_root/m1.ts" "$drift"

# 2. a persisted field is added
awk '{ print; if ($0 ~ /^  thunk:/) print "  extra: Schema.String" }' \
  "$fixture" >"$tmp_root/m2.ts"
expect_reject "added field" "$tmp_root/m2.ts" "$drift"

# 3. a persisted field is deleted
grep -v '^  mode:' "$fixture" >"$tmp_root/m3.ts"
expect_reject "deleted field" "$tmp_root/m3.ts" "$drift"

# 4. two fields swap order within one struct
awk '
  /^  types:/ { held=$0; next }
  /^  mode:/  { print; if (held != "") { print held; held="" }; next }
  { print }
' "$fixture" >"$tmp_root/m4.ts"
expect_reject "reordered fields" "$tmp_root/m4.ts" "$drift"

# 5. a codec struct is renamed
sed 's/^const SuspendSchema =/const SuspendedSchema =/' "$fixture" >"$tmp_root/m5.ts"
expect_reject "renamed codec struct" "$tmp_root/m5.ts" "$drift"

# 6. a spread source is renamed — the shared-field route
sed 's/\.\.\.KeywordFields/...OtherFields/' "$fixture" >"$tmp_root/m6.ts"
expect_reject "renamed spread source" "$tmp_root/m6.ts" "$drift"

# 7. the struct constructor is renamed — partial extraction, not silence
sed 's/Schema\.Struct(/Schema.Shape(/g' "$fixture" >"$tmp_root/m7.ts"
expect_reject "renamed struct constructor" "$tmp_root/m7.ts" "$drift"

# 8. the document codec wrapper is renamed, so a whole struct disappears
sed 's/Schema\.toCodecJson(/Schema.toCodecJsonV2(/' "$fixture" >"$tmp_root/m8.ts"
expect_reject "renamed document codec wrapper" "$tmp_root/m8.ts" "$drift"

# 9. the extraction pattern stops matching entirely — the silent-failure mode
sed -e 's/^const /konst /' -e 's/^function /funk /' "$fixture" >"$tmp_root/m9.ts"
expect_reject "broken extraction pattern" "$tmp_root/m9.ts" 'extracted no codec structs'

# 10. the helper-created keyword struct loses its shared persisted fields
sed '/^    \.\.\.KeywordFields$/d' "$fixture" >"$tmp_root/m10.ts"
expect_reject "deleted keyword-helper spread" "$tmp_root/m10.ts" "$drift"

# 11. the helper-created scalar envelope discriminator is renamed
sed 's/Schema\.Struct({ type: Schema\.tag(type), value })/Schema.Struct({ kind: Schema.tag(type), value })/' \
  "$fixture" >"$tmp_root/m11.ts"
expect_reject "renamed scalar-envelope field" "$tmp_root/m11.ts" "$drift"

# 12. a quoted persisted key is added and must not be silently skipped
awk '{ print; if ($0 ~ /^  payload:/) print "  \"future-key\": Schema.String" }' \
  "$fixture" >"$tmp_root/m12.ts"
expect_reject "added quoted field" "$tmp_root/m12.ts" "$drift"

# 13. off-pin bytes without --dry-run must be refused outright
if "$gate" "$baseline" >"$tmp_root/m13.log" 2>&1; then
  printf 'FAIL gate compared off-pin bytes without --dry-run\n' >&2
  exit 1
fi
grep -Fq 'refusing to compare off-pin bytes' "$tmp_root/m13.log" || {
  printf 'FAIL off-pin refusal did not name its reason\n' >&2
  exit 1
}
printf 'PASS rejected: off-pin bytes without --dry-run\n'

# 14. the frozen table must not be overridable on-pin
if "$gate" --expect "$expected" "$baseline" >"$tmp_root/m14.log" 2>&1; then
  printf 'FAIL gate allowed --expect without --dry-run\n' >&2
  exit 1
fi
grep -Fq 'requires --dry-run' "$tmp_root/m14.log" || {
  printf 'FAIL --expect refusal did not name its reason\n' >&2
  exit 1
}
printf 'PASS rejected: --expect without --dry-run\n'

# 15. no argument at all must fail, not default to something
if "$gate" >"$tmp_root/m15.log" 2>&1; then
  printf 'FAIL gate succeeded with no source supplied\n' >&2
  exit 1
fi
grep -Fq 'SC-REP-FIELD-PIN cannot be confirmed' "$tmp_root/m15.log" || {
  printf 'FAIL missing-source failure did not name the unconfirmable obligation\n' >&2
  exit 1
}
printf 'PASS rejected: no source supplied\n'

printf 'PASS schema field gate reacts to 12/12 specified source mutations\n'
printf 'PASS schema field gate enforces 3/3 invocation-safety refusals\n'
printf 'NOTE detector receipt only; says nothing about rc.112 semantics or payload types\n'
