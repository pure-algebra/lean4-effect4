#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd -P)"
gate="$repo_root/scripts/check-schema-structural-assurance.sh"
generator="$repo_root/scripts/generate-schema-structural-assurance.sh"
projection="$repo_root/generated/schema-structural-assurance.tsv"
contract="$repo_root/test/contracts/schema-payload.contract.md"

tmp_parent="${TMPDIR:-/tmp}"
tmp_parent="${tmp_parent%/}"
tmp_root="$(mktemp -d "$tmp_parent/effect4-schema-structural-reaction.XXXXXX")"
cleanup() {
  local cleanup_rc=$?
  set +e
  case "$tmp_root" in
    "$tmp_parent"/effect4-schema-structural-reaction.*) rm -rf -- "$tmp_root" ;;
    *) printf 'FAIL refusing to remove unexpected path: %s\n' "$tmp_root" >&2; cleanup_rc=1 ;;
  esac
  exit "$cleanup_rc"
}
trap cleanup EXIT

[[ -x "$gate" && -x "$generator" ]] || {
  printf 'FAIL Schema structural assurance scripts are not executable\n' >&2; exit 1; }

sed 's/SCHEMA-PG-PAYLOAD\/SC-REP-03-RECURSOR/SCHEMA-PG-PAYLOAD\/SC-REP-03-RECURSOR-STALE/' \
  "$projection" >"$tmp_root/stale.tsv"
if "$gate" --dry-run "$tmp_root/stale.tsv" >"$tmp_root/stale.log" 2>&1; then
  printf 'FAIL Schema structural assurance gate accepted stale generated output\n' >&2
  exit 1
fi
grep -Fq 'stale generated Schema structural assurance projection' "$tmp_root/stale.log" || {
  printf 'FAIL stale projection mutant lacked the drift signal\n' >&2; cat "$tmp_root/stale.log" >&2; exit 1; }
printf 'PASS rejected Schema structural assurance mutant: stale-generated-output\n'

{ printf 'required-closed\n'; cat "$contract"; } >"$tmp_root/manual-closure.md"
if "$generator" --dry-run-contract "$tmp_root/manual-closure.md" \
    >"$tmp_root/manual.tsv" 2>"$tmp_root/manual.log"; then
  printf 'FAIL Schema generator accepted a manual closure override\n' >&2
  exit 1
fi
grep -Fq 'manual required-closed override' "$tmp_root/manual.log" || {
  printf 'FAIL manual-closure mutant lacked the circularity signal\n' >&2; cat "$tmp_root/manual.log" >&2; exit 1; }
printf 'PASS rejected Schema structural assurance mutant: manual-closure-override\n'

if EFFECT4_SCHEMA_STRUCTURAL_PIN="$projection" "$generator" \
    >"$tmp_root/override.tsv" 2>"$tmp_root/override.log"; then
  printf 'FAIL Schema generator accepted an environment source override\n' >&2
  exit 1
fi
grep -Fq 'rejects source override variable' "$tmp_root/override.log" || {
  printf 'FAIL source-override mutant lacked the fixed-input signal\n' >&2; cat "$tmp_root/override.log" >&2; exit 1; }
printf 'PASS rejected Schema structural assurance mutant: environment-source-override\n'

"$gate"
printf 'PASS Schema structural assurance gate reacts to 3/3 stale/manual/override defects\n'

