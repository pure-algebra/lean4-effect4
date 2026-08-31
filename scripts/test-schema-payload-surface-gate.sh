#!/usr/bin/env bash
# Bounded reaction test for the elaborated Schema payload surface checker.
# Exactly four declaration-shape mutants are exercised.  Each source is valid
# Lean through its mutant declaration and must be rejected by the shared Meta
# checker, not by a source proof or lexical scrape.
set -euo pipefail

repo_root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd -P)"
gate="$repo_root/scripts/check-schema-payload-surface.sh"
fixture_root="$repo_root/test/fixtures/schema-payload-surface"
tmp_parent="${TMPDIR:-/tmp}"
tmp_parent="${tmp_parent%/}"
tmp_root="$(mktemp -d "$tmp_parent/effect4-payload-surface.XXXXXX")"

cleanup() {
  local cleanup_status=$?
  set +e
  case "$tmp_root" in
    "$tmp_parent"/effect4-payload-surface.*) rm -rf -- "$tmp_root" ;;
    *)
      printf 'FAIL refusing to remove unexpected path: %s\n' "$tmp_root" >&2
      cleanup_status=1
      ;;
  esac
  exit "$cleanup_status"
}
trap cleanup EXIT

[[ -x "$gate" ]] || { printf 'FAIL gate is not executable: %s\n' "$gate" >&2; exit 1; }

lake_bin="$(command -v lake || true)"
[[ -n "$lake_bin" ]] || { printf 'FAIL lake is unavailable\n' >&2; exit 1; }

expect_surface_reject() {
  local label="$1"
  local fixture="$2"
  local signal="$3"
  local log="$tmp_root/$label.log"
  [[ -f "$fixture" && ! -L "$fixture" ]] || {
    printf 'FAIL mutation fixture is absent, not regular, or a symlink: %s\n' "$fixture" >&2
    exit 1
  }
  if (
      cd -- "$repo_root"
      unset LEAN_PATH LEAN_SRC_PATH
      "$lake_bin" env lean "$fixture"
    ) >"$log" 2>&1; then
    printf 'FAIL surface checker accepted mutant: %s\n' "$label" >&2
    cat "$log" >&2
    exit 1
  fi
  grep -Fq 'schema payload surface mismatch' "$log" || {
    printf 'FAIL mutant did not reach the surface checker: %s\n' "$label" >&2
    cat "$log" >&2
    exit 1
  }
  grep -Fq "$signal" "$log" || {
    printf 'FAIL mutant lacked its expected detector signal (%s): %s\n' "$signal" "$label" >&2
    cat "$log" >&2
    exit 1
  }
  if grep -Eq 'unknown (constant|identifier)|declaration uses .sorry|unexpected token' "$log"; then
    printf 'FAIL mutant was rejected by an unrelated elaboration failure: %s\n' "$label" >&2
    cat "$log" >&2
    exit 1
  fi
  printf 'PASS rejected by elaborated surface checker: %s\n' "$label"
}

expect_surface_reject \
  ordinary-extra-constructor \
  "$fixture_root/ExtraConstructor.lean" \
  'constructor names/order'

expect_surface_reject \
  uninhabited-extra-constructor \
  "$fixture_root/ExtraUninhabited.lean" \
  'constructor names/order'

expect_surface_reject \
  constructor-permutation \
  "$fixture_root/ConstructorPermutation.lean" \
  'constructor names/order'

expect_surface_reject \
  field-type-drift \
  "$fixture_root/FieldTypeDrift.lean" \
  'type: expected'

# Import-boundary reaction: `Schema.Value` is a declaration-free breadth stub,
# so declaration lookup cannot see this edge.  The mutant is killed only by
# inspecting the environment's imported-module list.
value_import_log="$tmp_root/forbidden-value-import.log"
if (
    cd -- "$repo_root"
    unset LEAN_PATH LEAN_SRC_PATH
    "$lake_bin" build Effect4.Schema.Value >/dev/null
    "$lake_bin" env lean "$fixture_root/ForbiddenValueImport.lean"
  ) >"$value_import_log" 2>&1; then
  printf 'FAIL imported-module checker accepted declaration-free Schema.Value edge\n' >&2
  cat "$value_import_log" >&2
  exit 1
fi
grep -Fq \
  'forbidden upward module Effect4.Schema.Value is present in the imported-module list' \
  "$value_import_log" || {
  printf 'FAIL Schema.Value mutant was not rejected for the intended module-import reason\n' >&2
  cat "$value_import_log" >&2
  exit 1
}
if grep -Eq 'unknown (constant|identifier)|declaration uses .sorry|unexpected token' \
    "$value_import_log"; then
  printf 'FAIL Schema.Value mutant was rejected by an unrelated elaboration failure\n' >&2
  cat "$value_import_log" >&2
  exit 1
fi
printf 'PASS rejected by imported-module checker: declaration-free Schema.Value edge\n'

# The production gate has no argument or environment route by which a caller
# can substitute one of the synthetic sources for the fixed real files.
if "$gate" "$fixture_root/ExtraConstructor.lean" >"$tmp_root/arg-override.log" 2>&1; then
  printf 'FAIL production gate accepted a positional source override\n' >&2
  exit 1
fi
grep -Fq 'source is not overridable' "$tmp_root/arg-override.log" || {
  printf 'FAIL positional override refusal did not name the source boundary\n' >&2
  cat "$tmp_root/arg-override.log" >&2
  exit 1
}
printf 'PASS production source is not positionally overridable\n'

if EFFECT4_SCHEMA_PAYLOAD_SURFACE_SOURCE="$fixture_root/ExtraConstructor.lean" \
    "$gate" >"$tmp_root/env-override.log" 2>&1; then
  printf 'FAIL production gate accepted an environment source override\n' >&2
  exit 1
fi
grep -Fq 'rejects source override variable' "$tmp_root/env-override.log" || {
  printf 'FAIL environment override refusal did not name the source boundary\n' >&2
  cat "$tmp_root/env-override.log" >&2
  exit 1
}
printf 'PASS production source is not environment-overridable\n'

printf 'PASS schema payload surface checker kills exactly 4/4 specified shape mutants\n'
printf 'PASS payload import-boundary checker kills 1/1 declaration-free module mutant\n'
printf 'PASS production gate enforces 2/2 source-override refusals\n'
printf 'NOTE declaration-surface receipt only; no admission or wire-semantic claim\n'
