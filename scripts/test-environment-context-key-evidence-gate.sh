#!/usr/bin/env bash
# Bounded detector-reaction suite for the generated Context Key assurance join.
set -euo pipefail

repo_root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd -P)"
gate="$repo_root/scripts/check-environment-context-key-evidence.sh"
fixture_root="$repo_root/test/fixtures/environment-context-key-evidence"
projection="$repo_root/generated/environment-context-key-assurance.tsv"
generator="$repo_root/scripts/generate-environment-context-key-evidence.sh"
tmp_parent="${TMPDIR:-/tmp}"
tmp_parent="${tmp_parent%/}"
tmp_root="$(mktemp -d "$tmp_parent/effect4-context-key-reaction.XXXXXX")"

cleanup() {
  local cleanup_status=$?
  set +e
  case "$tmp_root" in
    "$tmp_parent"/effect4-context-key-reaction.*) rm -rf -- "$tmp_root" ;;
    *)
      printf 'FAIL refusing to remove unexpected path: %s\n' "$tmp_root" >&2
      cleanup_status=1
      ;;
  esac
  exit "$cleanup_status"
}
trap cleanup EXIT

[[ -x "$gate" ]] || { printf 'FAIL gate is not executable: %s\n' "$gate" >&2; exit 1; }
[[ -x "$generator" ]] || { printf 'FAIL generator is not executable: %s\n' "$generator" >&2; exit 1; }
[[ -f "$projection" && ! -L "$projection" ]] || {
  printf 'FAIL fixed generated projection is absent, not regular, or a symlink\n' >&2
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
    printf 'FAIL context-key evidence checker accepted mutant: %s\n' "$label" >&2
    exit 1
  fi
  grep -Fq 'environment context-key evidence mismatch' "$log" || {
    printf 'FAIL mutant did not reach the Context Key evidence checker: %s\n' "$label" >&2
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
  printf 'PASS rejected Context Key evidence mutant: %s\n' "$label"
}

expect_lean_reject extra-public-declaration \
  "$fixture_root/ExtraDeclaration.lean" 'owned declaration census'
expect_lean_reject missing-public-declaration \
  "$fixture_root/MissingDeclaration.lean" 'missing declaration'
expect_lean_reject declaration-owner-drift \
  "$fixture_root/OwnerDrift.lean" 'owner drift'

cp -- "$projection" "$tmp_root/stale.tsv"
sed 's/ENV-LEAF-KEY-IDENTITY/ENV-LEAF-KEY-IDENTITY-STALE/' \
  "$projection" >"$tmp_root/stale.tsv"
if "$gate" --dry-run "$tmp_root/stale.tsv" >"$tmp_root/stale.log" 2>&1; then
  printf 'FAIL context-key evidence gate accepted stale generated output\n' >&2
  exit 1
fi
grep -Fq 'stale generated context-key assurance projection' "$tmp_root/stale.log" || {
  printf 'FAIL stale-output mutant lacked the drift detector signal\n' >&2
  cat "$tmp_root/stale.log" >&2
  exit 1
}
printf 'PASS rejected Context Key evidence mutant: stale-generated-output\n'

sed 's/`status = generated`/`status = generated`; `required-closed`/' \
  "$repo_root/PORT-MANIFEST.md" >"$tmp_root/manual-closure.md"
if "$generator" --dry-run-manifest "$tmp_root/manual-closure.md" \
    >"$tmp_root/manual-closure.tsv" 2>"$tmp_root/manual-closure.log"; then
  printf 'FAIL context-key evidence generator accepted a manual closure override\n' >&2
  exit 1
fi
grep -Fq 'manual required-closed override' "$tmp_root/manual-closure.log" || {
  printf 'FAIL manual-closure mutant lacked the circularity detector signal\n' >&2
  cat "$tmp_root/manual-closure.log" >&2
  exit 1
}
printf 'PASS rejected Context Key evidence mutant: manual-closure-override\n'

"$gate"

printf 'PASS Context Key evidence gate reacts to 5/5 extra/missing/owner/stale/manual-closure defects\n'
printf 'NOTE local identity/order-bridge receipts only; ENV-KEY-INTERP and DATA-PG-ROW/ORDER remain open\n'
