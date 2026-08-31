#!/usr/bin/env bash
# Bounded detector-reaction suite for the generated DATA-PG-ROW assurance join.
set -euo pipefail

repo_root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd -P)"
gate="$repo_root/scripts/check-data-row-assurance.sh"
generator="$repo_root/scripts/generate-data-row-assurance.sh"
projection="$repo_root/generated/data-row-assurance.tsv"
fixture_root="$repo_root/test/fixtures/data-row-assurance"

tmp_parent="${TMPDIR:-/tmp}"
tmp_parent="${tmp_parent%/}"
tmp_root="$(mktemp -d "$tmp_parent/effect4-data-row-assurance-reaction.XXXXXX")"

cleanup() {
  local cleanup_rc=$?
  set +e
  case "$tmp_root" in
    "$tmp_parent"/effect4-data-row-assurance-reaction.*) rm -rf -- "$tmp_root" ;;
    *)
      printf 'FAIL refusing to remove unexpected path: %s\n' "$tmp_root" >&2
      cleanup_rc=1
      ;;
  esac
  exit "$cleanup_rc"
}
trap cleanup EXIT

[[ -x "$gate" ]] || { printf 'FAIL gate is not executable: %s\n' "$gate" >&2; exit 1; }
[[ -x "$generator" ]] || { printf 'FAIL generator is not executable: %s\n' "$generator" >&2; exit 1; }
[[ -f "$projection" && ! -L "$projection" ]] || {
  printf 'FAIL fixed generated Data.Row projection is absent, not regular, or a symlink\n' >&2
  exit 1
}

lake_bin="$(command -v lake || true)"
[[ -n "$lake_bin" ]] || { printf 'FAIL lake is unavailable\n' >&2; exit 1; }

expect_lean_reject() {
  local label="$1"
  local fixture="$2"
  local signal="$3"
  local log="$tmp_root/$label.log"
  if (
      cd -- "$repo_root"
      unset LEAN_PATH LEAN_SRC_PATH
      "$lake_bin" env lean "$fixture"
    ) >"$log" 2>&1; then
    printf 'FAIL Data.Row assurance checker accepted mutant: %s\n' "$label" >&2
    exit 1
  fi
  grep -Fq 'data-row assurance mismatch' "$log" || {
    printf 'FAIL mutant did not reach the Data.Row assurance checker: %s\n' "$label" >&2
    cat "$log" >&2
    exit 1
  }
  grep -Fq "$signal" "$log" || {
    printf 'FAIL mutant lacked expected detector signal (%s): %s\n' "$signal" "$label" >&2
    cat "$log" >&2
    exit 1
  }
  if grep -Eq 'unknown (constant|identifier)|declaration uses .sorry|unexpected token' "$log"; then
    printf 'FAIL mutant was rejected by an unrelated elaboration failure: %s\n' "$label" >&2
    cat "$log" >&2
    exit 1
  fi
  printf 'PASS rejected Data.Row assurance mutant: %s\n' "$label"
}

expect_lean_reject extra-public-declaration \
  "$fixture_root/ExtraDeclaration.lean" 'owned declaration census'
expect_lean_reject missing-public-declaration \
  "$fixture_root/MissingDeclaration.lean" 'missing declaration'
expect_lean_reject declaration-owner-drift \
  "$fixture_root/OwnerDrift.lean" 'owner drift'

sed 's/DATA-PG-ROW\/IDENTITY/DATA-PG-ROW\/IDENTITY-STALE/' \
  "$projection" >"$tmp_root/stale.tsv"
if "$gate" --dry-run "$tmp_root/stale.tsv" >"$tmp_root/stale.log" 2>&1; then
  printf 'FAIL Data.Row assurance gate accepted stale generated output\n' >&2
  exit 1
fi
grep -Fq 'stale generated Data.Row assurance projection' "$tmp_root/stale.log" || {
  printf 'FAIL stale-output mutant lacked the drift detector signal\n' >&2
  cat "$tmp_root/stale.log" >&2
  exit 1
}
printf 'PASS rejected Data.Row assurance mutant: stale-generated-output\n'

sed 's/`required-open`/`required-closed`/g' \
  "$repo_root/test/contracts/data-row.contract.md" >"$tmp_root/manual-closure.md"
if cmp -s -- "$repo_root/test/contracts/data-row.contract.md" \
    "$tmp_root/manual-closure.md"; then
  printf 'FAIL manual-closure fixture did not mutate the authored Data.Row contract\n' >&2
  exit 1
fi
if "$generator" --dry-run-contract "$tmp_root/manual-closure.md" \
    >"$tmp_root/manual-closure.tsv" 2>"$tmp_root/manual-closure.log"; then
  printf 'FAIL Data.Row assurance generator accepted a manual closure override\n' >&2
  exit 1
fi
grep -Fq 'manual required-closed override' "$tmp_root/manual-closure.log" || {
  printf 'FAIL manual-closure mutant lacked the circularity detector signal\n' >&2
  cat "$tmp_root/manual-closure.log" >&2
  exit 1
}
printf 'PASS rejected Data.Row assurance mutant: manual-closure-override\n'

"$gate"

printf 'PASS Data.Row assurance gate reacts to 5/5 extra/missing/owner/stale/manual-closure defects\n'
printf 'PASS all 10 DATA-PG-ROW edges are closed; ENV-PG-CONTEXT/ENV-KEY-INTERP remains open\n'
