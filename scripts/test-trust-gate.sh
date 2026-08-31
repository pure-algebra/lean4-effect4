#!/usr/bin/env bash
# Exercises whether the source trust gate rejects authored `partial` and
# `unsafe` declaration modifiers.
#
# The detector is an elaboration-time check in the root aggregator
# `Effect4Test.lean`, which Lake builds LAST. Any earlier module that fails to
# build therefore prevents the detector from running at all, and the gate would
# report neither a pass nor a real failure — it would simply never look. That
# matters during the breaker/builder red phase, when a frozen battery is
# deliberately unbuildable.
#
# So this gate does not tolerate a red module; it EXCISES the declared red
# modules from its throwaway probe copy, after first verifying that they are
# exactly the modules that fail. The planted-declaration assertions then run
# against a genuinely green tree, which is the only state in which they mean
# anything.
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
tmp_root="$(mktemp -d "${TMPDIR:-/tmp}/effect4-test-trust.XXXXXX")"
project_root="$tmp_root/project"
audit_source="$project_root/Effect4Test/Audit/AxiomGate.lean"
audit_original="$tmp_root/AxiomGate.lean"
known_red="$repo_root/test/fixtures/trust-gate/known-red.txt"

cleanup() {
  rm -rf -- "$tmp_root"
}
trap cleanup EXIT

mkdir -p "$project_root"
cp "$repo_root/lakefile.toml" "$repo_root/lake-manifest.json" \
  "$repo_root/lean-toolchain" "$repo_root/Effect4.lean" \
  "$repo_root/Effect4Test.lean" "$project_root/"
cp -R "$repo_root/Effect4" "$repo_root/Effect4Test" "$project_root/"

build_log="$tmp_root/build.log"

# Lake reports failing targets as "- <Module>" lines after its summary marker.
failing_targets() {
  awk '''
    /^Some required targets logged failures:/ { collecting = 1; next }
    collecting && /^- / { print substr($0, 3); next }
    collecting && $0 !~ /^- / { collecting = 0 }
  ''' "$1" | LC_ALL=C sort -u
}

declared_red="$( { [[ -f "$known_red" ]] && grep -v '''^[[:space:]]*#''' "$known_red" \
  | grep -v '''^[[:space:]]*$''' || true; } | LC_ALL=C sort -u )"

# --- 0. establish that the declared red set is exactly the failing set ------
(cd "$project_root" && lake build) >"$build_log" 2>&1 || true
observed_red="$(failing_targets "$build_log")"

# The root aggregator fails whenever anything it imports fails. It is a
# consequence of a declared red module, never an independent one.
if [[ -n "$declared_red" ]]; then
  observed_red="$(printf '''%s\n''' "$observed_red" | grep -v '''^Effect4Test$''' || true)"
fi

if [[ "$observed_red" != "$declared_red" ]]; then
  echo "FAIL the declared red set does not match the modules that actually fail" >&2
  echo "--- failing but not declared in test/fixtures/trust-gate/known-red.txt ---" >&2
  comm -23 <(printf '''%s\n''' "$observed_red") <(printf '''%s\n''' "$declared_red") >&2
  echo "--- declared red but actually green; remove the stale entry ---" >&2
  comm -13 <(printf '''%s\n''' "$observed_red") <(printf '''%s\n''' "$declared_red") >&2
  tail -60 "$build_log" >&2
  exit 1
fi

# --- 1. excise the declared red modules from the probe copy ----------------
excised=0
if [[ -n "$declared_red" ]]; then
  while IFS= read -r module; do
    [[ -n "$module" ]] || continue
    relative="${module//.//}.lean"
    target="$project_root/$relative"
    if [[ ! -f "$target" ]]; then
      echo "FAIL declared red module has no source file: $relative" >&2
      exit 1
    fi
    rm -f -- "$target"
    excised=$((excised + 1))
    echo "NOTE excised declared red module from the probe copy: $module"
  done <<<"$declared_red"
  # The root aggregator may still import what was removed.
  while IFS= read -r module; do
    [[ -n "$module" ]] || continue
    grep -v "^import ${module}$" "$project_root/Effect4Test.lean" \
      >"$project_root/Effect4Test.lean.tmp"
    mv "$project_root/Effect4Test.lean.tmp" "$project_root/Effect4Test.lean"
  done <<<"$declared_red"
fi

cp "$audit_source" "$audit_original"

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
  printf '''\n''' >>"$audit_source"
  sed -n '''1,$p''' "$fixture" >>"$audit_source"
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
printf '''\n''' >>"$audit_source"
sed -n '''1,$p''' "$repo_root/test/fixtures/trust-gate/benign.lean.txt" >>"$audit_source"
expect_acceptance "comment and string trust vocabulary"

expect_rejection "$repo_root/test/fixtures/trust-gate/partial.lean.txt" partial \
  "partial declaration"
expect_rejection "$repo_root/test/fixtures/trust-gate/unsafe.lean.txt" unsafe \
  "unsafe declaration"

cp "$audit_original" "$audit_source"
expect_acceptance "restored source tree"

if [[ "$excised" -gt 0 ]]; then
  echo "NOTE $excised declared red module(s) were excised before testing; the trust"
  echo "NOTE property is therefore unverified FOR THOSE MODULES until they build"
fi
