#!/usr/bin/env bash
# Kernel-environment gate for the contracted Schema payload declaration surface.
#
# This gate has no source override.  It checks the repository's fixed Lean
# module, then checks that D2–D3 elaborate from `Effect4.Schema.Payload` alone,
# that this module owns exactly the allocated public carrier/alias set, that no
# D7 declaration leaks through that boundary, and that every frozen D7 public
# declaration remains owned by `Effect4.Schema.Check`.  It does not establish
# payload admission or wire semantics.
set -euo pipefail

repo_root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd -P)"
surface_test="$repo_root/Effect4Test/Schema/PayloadSurface.lean"
payload_boundary="$repo_root/test/fixtures/schema-payload-surface/RequiredPayloadBoundary.lean"
ownership_test="$repo_root/test/fixtures/schema-payload-surface/RequiredOwnership.lean"

if [[ $# -ne 0 ]]; then
  printf 'FAIL schema payload surface gate accepts no arguments; its source is not overridable\n' >&2
  exit 2
fi

for override_name in \
    EFFECT4_SCHEMA_PAYLOAD_SURFACE_SOURCE \
    EFFECT4_SCHEMA_PAYLOAD_BOUNDARY_SOURCE \
    EFFECT4_SCHEMA_PAYLOAD_OWNERSHIP_SOURCE; do
  if [[ -n "${!override_name-}" ]]; then
    printf 'FAIL schema payload surface gate rejects source override variable %s\n' \
      "$override_name" >&2
    exit 2
  fi
done

for required in "$surface_test" "$payload_boundary" "$ownership_test"; do
  [[ -f "$required" && ! -L "$required" ]] || {
    printf 'FAIL required fixed gate source is absent, not regular, or a symlink: %s\n' \
      "$required" >&2
    exit 1
  }
done

lake_bin="$(command -v lake || true)"
[[ -n "$lake_bin" ]] || { printf 'FAIL lake is unavailable\n' >&2; exit 1; }

run_fixed_source() {
  local source="$1"
  (
    cd -- "$repo_root"
    unset LEAN_PATH LEAN_SRC_PATH
    "$lake_bin" env lean "$source"
  )
}

run_fixed_module() {
  local module="$1"
  (
    cd -- "$repo_root"
    unset LEAN_PATH LEAN_SRC_PATH
    "$lake_bin" build "$module"
  )
}

run_fixed_module Effect4Test.Schema.PayloadSurface
printf 'PASS elaborated payload carrier shapes match the contracted declaration surface\n'

run_fixed_module Effect4.Schema.Payload
run_fixed_source "$payload_boundary"
printf 'PASS D2-D3 elaborate from Effect4.Schema.Payload alone with an exact public carrier/alias census\n'
printf 'PASS every frozen D7 public declaration is unreachable through the Payload-only boundary\n'

run_fixed_module Effect4.Schema.Check
run_fixed_source "$ownership_test"
printf 'PASS declaration owners follow Check -> Document -> Representation -> Payload -> Data.Json\n'
printf 'PASS every frozen D7 public declaration is owned by Effect4.Schema.Check\n'

printf 'PASS schema payload surface gate\n'
