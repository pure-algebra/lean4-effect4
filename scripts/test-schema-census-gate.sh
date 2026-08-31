#!/usr/bin/env bash
# Exercises whether `scripts/check-schema-census.sh` reacts to specified drift.
#
# This exercises the DETECTOR, not the census. It runs against a synthetic
# fixture, so a pass here says nothing about Effect's real tag set, payloads,
# or semantics; it says only that the ten named detector mutations cannot
# return a vacuous success.
set -euo pipefail

repo_root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd -P)"
gate="$repo_root/scripts/check-schema-census.sh"
fixture="$repo_root/test/fixtures/schema-census/reference.ts"
tmp_parent="${TMPDIR:-/tmp}"
tmp_parent="${tmp_parent%/}"
tmp_root="$(mktemp -d "$tmp_parent/effect4-census-gate.XXXXXX")"
fixture_before="$tmp_root/fixture.before"

cleanup() {
  local status=$?
  set +e
  if [[ -f "$fixture_before" ]] && ! cmp -s -- "$fixture_before" "$fixture"; then
    printf 'FAIL fixture changed while the gate tests ran\n' >&2
    status=1
  fi
  case "$tmp_root" in
    "$tmp_parent"/effect4-census-gate.*) rm -rf -- "$tmp_root" ;;
    *) printf 'FAIL refusing to remove unexpected path: %s\n' "$tmp_root" >&2; status=1 ;;
  esac
  exit "$status"
}
trap cleanup EXIT

[[ -x "$gate" ]] || { printf 'FAIL gate is not executable: %s\n' "$gate" >&2; exit 1; }
[[ -f "$fixture" ]] || { printf 'FAIL fixture is missing: %s\n' "$fixture" >&2; exit 1; }
cp -- "$fixture" "$fixture_before"

# Every case below must FAIL the gate except the baseline.
expect_reject() {
  local name="$1" candidate="$2" signal="$3"
  local log="$tmp_root/$name.log"
  if "$gate" --dry-run "$candidate" >"$log" 2>&1; then
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
if ! "$gate" --dry-run "$baseline" >"$tmp_root/baseline.log" 2>&1; then
  printf 'FAIL the unmutated fixture did not pass the gate\n' >&2
  cat "$tmp_root/baseline.log" >&2
  exit 1
fi
grep -Fq 'remains OPEN' "$tmp_root/baseline.log" || {
  printf 'FAIL a dry run must state that SC-REP-CENSUS-PIN remains open\n' >&2
  exit 1
}
printf 'PASS baseline fixture accepted, and reported as closing nothing\n'

# 1. a tag disappears from the source
sed 's/makeKeywordSchema("Void")/makeKeywordSchema("Voyd")/' "$fixture" >"$tmp_root/m1.ts"
expect_reject "renamed tag" "$tmp_root/m1.ts" 'the type union and the codec disagree'

# 2. a tag is added to the source
sed 's|  makeKeywordSchema("Null"),|  makeKeywordSchema("Null"),\n  makeKeywordSchema("Bogus"),|' \
  "$fixture" >"$tmp_root/m2.ts"
expect_reject "added tag" "$tmp_root/m2.ts" 'the type union and the codec disagree'

# 3. a tag is deleted outright
grep -v 'Schema.tag("Union")' "$fixture" >"$tmp_root/m3.ts"
expect_reject "deleted tag" "$tmp_root/m3.ts" 'the type union and the codec disagree'

# 3b. a 23rd member added to the closed union only
sed 's/^  | Union$/  | Union\n  | Newthing/' "$fixture" >"$tmp_root/m3b.ts"
expect_reject "23rd union member, codec unchanged" "$tmp_root/m3b.ts" \
  'the type union and the codec disagree'

# 3c. a 23rd member added to BOTH the union and the codec.
# This is the one that defeated the call-site-only extractor.
sed 's/^  | Union$/  | Union\n  | Newthing/' "$fixture" \
  | sed 's|^const UnionSchema.*|&\nconst NewthingSchema = Schema.Struct({ _tag: Schema.tag("Newthing") })|' \
  >"$tmp_root/m3c.ts"
expect_reject "23rd member in union and codec" "$tmp_root/m3c.ts" 'tag census drift'

# 3d. family membership must not be erased by merging the two alphabets.
# This exact mutant passed the previous combined-set detector.
sed 's/^  | Union$/  | Union\n  | Filter/' "$fixture" >"$tmp_root/m3d.ts"
expect_reject "check tag copied into representation family" "$tmp_root/m3d.ts" \
  'source union families overlap'

# 4. the extraction pattern stops matching — the silent-failure mode
sed 's/Schema\.tag(/Schema.renamedTag(/g; s/makeKeywordSchema(/renamedKeyword(/g' \
  "$fixture" >"$tmp_root/m4.ts"
expect_reject "broken extraction pattern" "$tmp_root/m4.ts" 'extracted no codec tags'

# 4b. the closed union declaration is renamed away
sed 's/^export type Representation =/export type Repr =/' "$fixture" >"$tmp_root/m4b.ts"
expect_reject "union declaration renamed" "$tmp_root/m4b.ts" 'extracted no Representation union members'

# 5. off-pin bytes without --dry-run must be refused outright
if "$gate" "$baseline" >"$tmp_root/m5.log" 2>&1; then
  printf 'FAIL gate compared off-pin bytes without --dry-run\n' >&2
  exit 1
fi
grep -Fq 'refusing to compare off-pin bytes' "$tmp_root/m5.log" || {
  printf 'FAIL off-pin refusal did not name its reason\n' >&2
  exit 1
}
printf 'PASS rejected: off-pin bytes without --dry-run\n'

# 6. no argument at all must fail, not default to something
if "$gate" >"$tmp_root/m6.log" 2>&1; then
  printf 'FAIL gate succeeded with no source supplied\n' >&2
  exit 1
fi
grep -Fq 'SC-REP-CENSUS-PIN cannot be confirmed' "$tmp_root/m6.log" || {
  printf 'FAIL missing-source failure did not name the unconfirmable obligation\n' >&2
  exit 1
}
printf 'PASS rejected: no source supplied\n'

printf 'PASS schema census gate reacts to 10/10 specified lexical defects\n'
