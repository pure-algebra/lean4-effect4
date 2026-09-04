#!/usr/bin/env bash
# Exercise exact implementation admissions against compiled declarations.
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
project_root="$(cd "${1:-$repo_root}" && pwd)"
tmp_root="$(mktemp -d "${TMPDIR:-/tmp}/effect4-trust-boundaries.XXXXXX")"
trap 'rm -rf -- "$tmp_root"' EXIT

{
  printf 'import Test.Schema.StructuralAssurance\n'
  cat "$project_root/Test/Audit/AxiomGate.lean"
  cat "$repo_root/Test/fixtures/trust-gate/implementation-boundaries.lean.txt"
} > "$tmp_root/ImplementationBoundaries.lean"

cd "$project_root"
lake env lean "$tmp_root/ImplementationBoundaries.lean"
