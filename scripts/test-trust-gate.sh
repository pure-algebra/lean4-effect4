#!/usr/bin/env bash
# Exercises whether the trust gate rejects what it claims to reject: authored
# trust tokens in the source (`partial`, `unsafe`, `sorry`, `native_decide` —
# the last two also when hidden inside an `example`, which leaves no constant
# for the declaration pass to see), a bodyless `opaque`, and an unadmitted
# `Classical.choice` dependency.
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
# The probe copy must resolve the pinned `effects` dependency without a
# network fetch; reuse the packages Lake already checked out here.
if [[ -d "$repo_root/.lake/packages" ]]; then
  mkdir -p "$project_root/.lake"
  cp -R "$repo_root/.lake/packages" "$project_root/.lake/"
fi
# And the build artifacts, so the control build is a replay rather than 243
# modules from scratch. Lake's traces are content hashes, so anything the copy
# gets wrong is rebuilt rather than believed: the speedup is free of trust.
if [[ -d "$repo_root/.lake/build" ]]; then
  mkdir -p "$project_root/.lake"
  cp -R "$repo_root/.lake/build" "$project_root/.lake/"
  # ... with one exception. The audit root is the thing under test, and its
  # artifact must never be replayed: `#effect4_axiom_gate` reads the source
  # tree and `known-red.txt` directly, neither of which is in Lake's trace, so
  # a replayed olean would report a verdict about the repository rather than
  # about this probe. Delete it and let it re-elaborate every time.
  rm -f "$project_root/.lake/build/lib/lean/Effect4Test.olean" \
        "$project_root/.lake/build/lib/lean/Effect4Test.olean.hash" \
        "$project_root/.lake/build/lib/lean/Effect4Test.ilean" \
        "$project_root/.lake/build/lib/lean/Effect4Test.ilean.hash" \
        "$project_root/.lake/build/lib/lean/Effect4Test.trace" \
        "$project_root/.lake/build/ir/Effect4Test.c" \
        "$project_root/.lake/build/ir/Effect4Test.c.hash" \
        "$project_root/.lake/build/ir/Effect4Test.setup.json"
fi

# The module-closure half of the gate reads the declared-red set from the tree
# it is auditing, and treats a missing file as a defect rather than an empty
# set. Step 0 below runs against the repository's own set; after the excision
# the probe's set is emptied, because by then the modules it names are gone.
probe_known_red="$project_root/test/fixtures/trust-gate/known-red.txt"
mkdir -p "$project_root/test/fixtures/trust-gate"
cp "$known_red" "$probe_known_red"

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
# The RED-INCLUSIVE target, not the default one. `lake build` builds
# `Effect4TestGreen` — the audit root and its import closure — which by
# construction excludes a declared red module, so it could never observe one
# failing. `Effect4Test` is the glob over every module under `Effect4Test/`,
# which is what this step has to look at.
(cd "$project_root" && lake build Effect4Test) >"$build_log" 2>&1 || true
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

# The probe tree is all green now, so its declared-red set is empty by
# construction. The header stays because the file must exist.
cat >"$probe_known_red" <<'PROBE_KNOWN_RED'
# Written by scripts/test-trust-gate.sh. The probe copy excises every declared
# red module before the planted-declaration assertions run, so by then the tree
# is all green and this set is empty.
PROBE_KNOWN_RED

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

# Plant a fixture in the audit source and require the build to fail with the
# exact diagnostic named. A rejection for the wrong reason is a failure: the
# point is that the gate saw what was planted, not that something broke.
expect_rejection_matching() {
  local fixture="$1"
  local expected_message="$2"
  local label="$3"
  cp "$audit_original" "$audit_source"
  printf '''\n''' >>"$audit_source"
  sed -n '''1,$p''' "$fixture" >>"$audit_source"
  if (cd "$project_root" && lake build) >"$build_log" 2>&1; then
    echo "trust-gate self-test unexpectedly accepted $label" >&2
    exit 1
  fi
  if ! grep -Fq "$expected_message" "$build_log"; then
    echo "trust-gate self-test rejected $label for an unexpected reason" >&2
    echo "--- expected to find: $expected_message" >&2
    tail -80 "$build_log" >&2
    exit 1
  fi
  echo "PASS planted $label rejected"
}

expect_rejection() {
  local fixture="$1"
  local expected_token="$2"
  local label="$3"
  expect_rejection_matching "$fixture" \
    "contains an authored \`$expected_token\` trust token" "$label"
}

expect_acceptance "the unmodified source tree"

cp "$audit_original" "$audit_source"
printf '''\n''' >>"$audit_source"
sed -n '''1,$p''' "$repo_root/test/fixtures/trust-gate/benign.lean.txt" >>"$audit_source"
expect_acceptance "comments, strings, and numeric projections"

expect_rejection "$repo_root/test/fixtures/trust-gate/partial.lean.txt" partial \
  "partial declaration"
expect_rejection "$repo_root/test/fixtures/trust-gate/unsafe.lean.txt" unsafe \
  "unsafe declaration"
expect_rejection "$repo_root/test/fixtures/trust-gate/sorry.lean.txt" sorry \
  "sorry in a named theorem"
# The one that says finding #1 is closed: an `example` leaves no constant, so
# only the source pass can see this.
expect_rejection "$repo_root/test/fixtures/trust-gate/example-sorry.lean.txt" sorry \
  "sorry inside an example"
expect_rejection "$repo_root/test/fixtures/trust-gate/native-decide.lean.txt" native_decide \
  "native_decide"
# `opaque` is not a token check: the bodied form is admitted and the keyword is
# the same, so this is the declaration pass reading the synthesised value.
expect_rejection_matching "$repo_root/test/fixtures/trust-gate/opaque.lean.txt" \
  "plantedBodylessOpaque is an \`opaque\` with no body" \
  "bodyless opaque"

cp "$audit_original" "$audit_source"
field_source="$project_root/Effect4/Target/TypeScript/EffectfulField.lean"
cp "$field_source" "$tmp_root/EffectfulField.lean"
printf '\n' >>"$field_source"
cat "$repo_root/test/fixtures/trust-gate/unadmitted-choice.lean.txt" >>"$field_source"
if (cd "$project_root" && lake build) >"$build_log" 2>&1; then
  echo "trust-gate self-test unexpectedly accepted an unadmitted choice dependency" >&2
  exit 1
fi
if ! grep -Fq 'declaration Effect4.Target.TypeScript.EffectfulField.plantedUnadmittedChoice reaches unexpected axiom Classical.choice' "$build_log"; then
  echo "trust-gate self-test rejected the choice dependency for an unexpected reason" >&2
  tail -80 "$build_log" >&2
  exit 1
fi
echo "PASS unadmitted choice dependency in the field-renderer module rejected"
cp "$tmp_root/EffectfulField.lean" "$field_source"
expect_acceptance "restored source tree"

# Reuse the built probe project for lexical failures that Lean compilation
# would otherwise reject before the source detector gets to inspect them.
"$repo_root/scripts/test-source-trust-tokenizer.sh" "$project_root"
"$repo_root/scripts/test-trust-boundaries.sh" "$project_root"
(cd "$project_root" && lake env lean \
  "$repo_root/test/fixtures/trust-gate/expr-equality.lean.txt")

if [[ "$excised" -gt 0 ]]; then
  echo "NOTE $excised declared red module(s) were excised before testing; the trust"
  echo "NOTE property is therefore unverified FOR THOSE MODULES until they build"
fi
