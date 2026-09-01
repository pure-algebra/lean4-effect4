#!/usr/bin/env bash
# Detector-reaction suite for FIBER-PG-REPRESENTATIVE assurance.
set -euo pipefail

repo_root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd -P)"
gate="$repo_root/scripts/check-fiber-assurance.sh"
generator="$repo_root/scripts/generate-fiber-assurance.sh"
projection="$repo_root/generated/fiber-assurance.tsv"
fixture_root="$repo_root/test/fixtures/fiber-assurance"

tmp_parent="${TMPDIR:-/tmp}"
tmp_parent="${tmp_parent%/}"
tmp_root="$(mktemp -d "$tmp_parent/effect4-fiber-assurance-reaction.XXXXXX")"

cleanup() {
  local cleanup_rc=$?
  set +e
  case "$tmp_root" in
    "$tmp_parent"/effect4-fiber-assurance-reaction.*) rm -rf -- "$tmp_root" ;;
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
  printf 'FAIL fixed generated Fiber projection is absent, not regular, or a symlink\n' >&2
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
    printf 'FAIL Fiber assurance checker accepted mutant: %s\n' "$label" >&2
    exit 1
  fi
  grep -Fq 'fiber assurance mismatch' "$log" || {
    printf 'FAIL mutant did not reach the Fiber assurance checker: %s\n' "$label" >&2
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
  printf 'PASS rejected Fiber assurance mutant: %s\n' "$label"
}

expect_lean_reject extra-public-declaration \
  "$fixture_root/ExtraDeclaration.lean" 'owned declaration census'
expect_lean_reject missing-public-declaration \
  "$fixture_root/MissingDeclaration.lean" 'missing declaration'
expect_lean_reject duplicate-public-declaration \
  "$fixture_root/DuplicateDeclaration.lean" 'duplicate owned declaration census'
expect_lean_reject declaration-owner-drift \
  "$fixture_root/OwnerDrift.lean" 'owner drift'

sed 's/FIBER-PG-REPRESENTATIVE\/IDENTITY/FIBER-PG-REPRESENTATIVE\/IDENTITY-STALE/' \
  "$projection" >"$tmp_root/stale.tsv"
if "$gate" --dry-run "$tmp_root/stale.tsv" >"$tmp_root/stale.log" 2>&1; then
  printf 'FAIL Fiber assurance gate accepted stale generated output\n' >&2
  exit 1
fi
grep -Fq 'stale generated Fiber assurance projection' "$tmp_root/stale.log" || {
  printf 'FAIL stale-output mutant lacked the drift detector signal\n' >&2
  cat "$tmp_root/stale.log" >&2
  exit 1
}
printf 'PASS rejected Fiber assurance mutant: stale-generated-output\n'

sed 's/`required-open`/`required-closed`/g' \
  "$repo_root/docs/FIBER-DAG.md" >"$tmp_root/manual-closure.md"
if cmp -s -- "$repo_root/docs/FIBER-DAG.md" "$tmp_root/manual-closure.md"; then
  printf 'FAIL manual-closure fixture did not mutate the authored Fiber graph\n' >&2
  exit 1
fi
if "$generator" --dry-run-dag "$tmp_root/manual-closure.md" \
    >"$tmp_root/manual-closure.tsv" 2>"$tmp_root/manual-closure.log"; then
  printf 'FAIL Fiber assurance generator accepted a manual closure override\n' >&2
  exit 1
fi
grep -Fq 'manual required-closed override' "$tmp_root/manual-closure.log" || {
  printf 'FAIL manual-closure mutant lacked the circularity detector signal\n' >&2
  cat "$tmp_root/manual-closure.log" >&2
  exit 1
}
printf 'PASS rejected Fiber assurance mutant: manual-closure-override\n'

"$gate"

printf 'PASS Fiber assurance gate reacts to 6/6 extra/missing/duplicate/owner/stale/manual-closure defects\n'
printf 'PASS all 7 required FIBER-PG-REPRESENTATIVE edges are closed from evidence\n'
