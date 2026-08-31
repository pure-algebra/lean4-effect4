#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
tmp_root="$(mktemp -d "${TMPDIR:-/tmp}/effect4-test-trust.XXXXXX")"
project_root="$tmp_root/project"
audit_source="$project_root/Effect4Test/Audit/AxiomGate.lean"
audit_original="$tmp_root/AxiomGate.lean"

cleanup() {
  rm -rf -- "$tmp_root"
}
trap cleanup EXIT

mkdir -p "$project_root"
cp "$repo_root/lakefile.toml" "$repo_root/lake-manifest.json" \
  "$repo_root/lean-toolchain" "$repo_root/Effect4.lean" \
  "$repo_root/Effect4Test.lean" "$project_root/"
cp -R "$repo_root/Effect4" "$repo_root/Effect4Test" "$project_root/"
cp "$audit_source" "$audit_original"

build_log="$tmp_root/build.log"

expect_acceptance() {
  local label="$1"
  if ! (cd "$project_root" && lake build) >"$build_log" 2>&1; then
    echo "trust-gate self-test unexpectedly rejected $label" >&2
    tail -80 "$build_log" >&2
    exit 1
  fi
  echo "PASS trust gate accepted $label"
}

expect_rejection() {
  local fixture="$1"
  local expected_modifier="$2"
  local label="$3"
  cp "$audit_original" "$audit_source"
  printf '\n' >>"$audit_source"
  sed -n '1,$p' "$fixture" >>"$audit_source"
  if (cd "$project_root" && lake build) >"$build_log" 2>&1; then
    echo "trust-gate self-test unexpectedly accepted $label" >&2
    exit 1
  fi
  if ! grep -Fq "contains an authored \`$expected_modifier\` declaration modifier" "$build_log"; then
    echo "trust-gate self-test rejected $label for an unexpected reason" >&2
    tail -80 "$build_log" >&2
    exit 1
  fi
  echo "PASS planted $label rejected"
}

expect_acceptance "the unmodified source tree"

cp "$audit_original" "$audit_source"
printf '\n' >>"$audit_source"
sed -n '1,$p' "$repo_root/test/fixtures/trust-gate/benign.lean.txt" >>"$audit_source"
expect_acceptance "comment and string trust vocabulary"

expect_rejection "$repo_root/test/fixtures/trust-gate/partial.lean.txt" partial \
  "partial declaration"
expect_rejection "$repo_root/test/fixtures/trust-gate/unsafe.lean.txt" unsafe \
  "unsafe declaration"

cp "$audit_original" "$audit_source"
expect_acceptance "restored source tree"
