#!/usr/bin/env bash
# Exercises whether the trust gate rejects what it claims to reject: authored
# trust tokens in the source (`partial`, `unsafe`, `sorry`, `native_decide`,
# `axiom` — some of them hidden inside an `example`, which leaves no constant
# for the declaration pass to see), a bodyless `opaque`, an unadmitted
# `Classical.choice` dependency, and a hand-spelled name got up to look like an
# auxiliary of an admitted declaration.
#
# ## The design: one root elaboration per case, no rebuild
#
# `#effect4_axiom_gate` reads two things from two different places.
#
# * The SOURCES it tokenizes and closes over come from the project root it
#   finds by walking up from the file being elaborated (`findProjectRoot`),
#   then walking `Effect4/` and `Effect4Test/` under it.
# * The DECLARATIONS it inspects come from whatever oleans `LEAN_PATH`
#   provides, and it audits only constants that belong to some module — a
#   constant declared in the file being elaborated has no module and is never
#   audited.
#
# So a planted defect needs a rebuild only when it has to be a *declaration*.
# For a source token it does not: copy the sources to a scratch tree, append
# the fixture there, and run `lake env lean <scratch>/Effect4Test.lean` from the
# real project. The gate walks the scratch sources and reads the real build.
# One `lean` invocation, about three seconds, and nothing is compiled.
#
# For the three cases that ARE declarations — the bodyless `opaque`, the
# unadmitted `Classical.choice`, and the forged auxiliary — the fixture is a
# whole module. It is compiled alone (it imports `Effect4` and nothing else),
# dropped into a scratch olean directory, imported by the scratch root, and the
# root is run with that directory ahead of the real `LEAN_PATH`. One module
# compiles, not two hundred and forty-five.
#
# Nothing here is replayed: every case is a fresh elaboration of the root,
# which re-reads the scratch sources and `known-red.txt` each time. The default
# `lake build` is a different matter — its verdict is as fresh as the root's
# last elaboration, and this script, not that build, is the authority.
#
# ## The red phase
#
# The repository deliberately permits a frozen breaker battery to be red before
# its builder lands, and step 0 checks the declared set in both directions
# against the real tree. Neither direction needs a copy: a declared module that
# has gone green fails `lake build <module>`, and an undeclared red module is
# refused by the closure gate itself — either it is reachable from the audit
# root, in which case `lake build Effect4TestGreen` fails, or it is not, in
# which case the gate names it.
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
tmp_root="$(mktemp -d "${TMPDIR:-/tmp}/effect4-test-trust.XXXXXX")"
probe="$tmp_root/project"
probe_log="$tmp_root/probe.log"
known_red="$repo_root/test/fixtures/trust-gate/known-red.txt"
fixtures="$repo_root/test/fixtures/trust-gate"
audit_source="$probe/Effect4Test/Audit/AxiomGate.lean"
planted_lib="$tmp_root/lib"
real_build_lib="$repo_root/.lake/build/lib/lean"
planted_module=""

cleanup() {
  rm -rf -- "$tmp_root"
}
trap cleanup EXIT

rejected=0
accepted=0
run_start="$(date +%s)"
step_start="$run_start"

step_begin() {
  step_start="$(date +%s)"
}

step_end() {
  printf 'TIME %-52s %3ss\n' "$1" "$(( $(date +%s) - step_start ))"
}

# --- 0. the real tree, incrementally -----------------------------------------

step_begin
if ! (cd "$repo_root" && lake build Effect4TestGreen) >"$probe_log" 2>&1; then
  echo "FAIL the default green target does not build; the gate has nothing to say" >&2
  tail -60 "$probe_log" >&2
  exit 1
fi
echo "PASS default green target builds and its axiom gate accepts the real tree"
accepted=$((accepted + 1))
step_end "step 0a  lake build Effect4TestGreen"

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

step_begin
if [[ -n "$declared_red" ]]; then
  # One invocation, exactly the declared modules. A module that has gone green
  # builds and is absent from the failing set, which is the "stale entry"
  # direction. The other direction — an undeclared red module — is the closure
  # gate's own job, and step 0a just ran it.
  # shellcheck disable=SC2086
  (cd "$repo_root" && lake build $declared_red) >"$probe_log" 2>&1 || true
  observed_red="$(failing_targets "$probe_log")"
  if [[ "$observed_red" != "$declared_red" ]]; then
    echo "FAIL the declared red set does not match the modules that actually fail" >&2
    echo "--- declared red but actually green; remove the stale entry ---" >&2
    comm -13 <(printf '''%s\n''' "$observed_red") <(printf '''%s\n''' "$declared_red") >&2
    tail -60 "$probe_log" >&2
    exit 1
  fi
  echo "PASS every module declared red in known-red.txt is still red"
else
  echo "PASS no module is declared red"
fi
accepted=$((accepted + 1))
step_end "step 0b  declared red set is still red"

# --- 1. the scratch source tree ----------------------------------------------

step_begin
mkdir -p "$probe/test/fixtures/trust-gate"
# `lean-toolchain` so that elan resolves the same compiler when a planted
# module is compiled from inside the scratch tree.
cp "$repo_root/Effect4.lean" "$repo_root/Effect4Test.lean" \
  "$repo_root/lean-toolchain" "$probe/"
cp -R "$repo_root/Effect4" "$repo_root/Effect4Test" "$probe/"

# A search root that is the real build directory plus room for one more module.
# It has to be a mirror rather than a prefix on LEAN_PATH: Lean picks the FIRST
# search root that has a directory named after the module's root and then maps
# every `Effect4Test.*` module under it, so a scratch directory containing only
# `Effect4Test/Planted.olean` would shadow all 245 real oleans. Symlinks, so
# nothing is copied and nothing in the real build directory is written.
mkdir -p "$planted_lib/Effect4Test"
for entry in "$real_build_lib"/*; do
  base="$(basename "$entry")"
  [[ "$base" == "Effect4Test" ]] && continue
  ln -s "$entry" "$planted_lib/$base"
done
for entry in "$real_build_lib"/Effect4Test/*; do
  ln -s "$entry" "$planted_lib/Effect4Test/$(basename "$entry")"
done
# The gate reads the declared-red set from the tree it is auditing, and treats
# a missing file as a defect rather than an empty set. The scratch tree is the
# real one, red modules included, so it gets the real set.
cp "$known_red" "$probe/test/fixtures/trust-gate/known-red.txt"
cp "$audit_source" "$tmp_root/AxiomGate.lean"
cp "$probe/Effect4Test.lean" "$tmp_root/Effect4Test.lean"
real_lean_path="$(cd "$repo_root" && lake env printenv LEAN_PATH)"
step_end "step 1   copy sources to the scratch tree"

restore_probe() {
  cp "$tmp_root/AxiomGate.lean" "$audit_source"
  cp "$tmp_root/Effect4Test.lean" "$probe/Effect4Test.lean"
  if [[ -n "$planted_module" ]]; then
    rm -f "$planted_lib/Effect4Test/${planted_module}.olean" \
          "$planted_lib/Effect4Test/${planted_module}.ilean" \
          "$probe/Effect4Test/${planted_module}.lean"
    planted_module=""
  fi
}

# Lean requires imports before anything else, so a planted module is spliced in
# after the last one rather than appended.
add_root_import() {
  awk -v line="import $1" '''
    { lines[NR] = $0; if ($0 ~ /^import /) last = NR }
    END { for (i = 1; i <= NR; i++) { print lines[i]; if (i == last) print line } }
  ''' "$probe/Effect4Test.lean" >"$probe/Effect4Test.lean.new"
  mv "$probe/Effect4Test.lean.new" "$probe/Effect4Test.lean"
}

run_probe_root() {
  (cd "$repo_root" && LEAN_PATH="$planted_lib:$real_lean_path" \
    lean "$probe/Effect4Test.lean") >"$probe_log" 2>&1
}

expect_acceptance() {
  local label="$1"
  step_begin
  if ! run_probe_root; then
    echo "FAIL trust gate unexpectedly rejected $label" >&2
    tail -60 "$probe_log" >&2
    exit 1
  fi
  echo "PASS trust gate accepted $label"
  accepted=$((accepted + 1))
  step_end "         accept: $label"
}

expect_rejection_matching() {
  local expected_message="$1"
  local label="$2"
  step_begin
  if run_probe_root; then
    echo "FAIL trust gate unexpectedly accepted $label" >&2
    exit 1
  fi
  if ! grep -Fq "$expected_message" "$probe_log"; then
    echo "FAIL trust gate rejected $label for an unexpected reason" >&2
    echo "--- expected to find: $expected_message" >&2
    tail -60 "$probe_log" >&2
    exit 1
  fi
  echo "PASS planted $label rejected"
  rejected=$((rejected + 1))
  step_end "         reject: $label"
}

# --- 2. planted source tokens ------------------------------------------------
#
# Appended to a source file in the scratch tree. The gate tokenizes it; nothing
# compiles it, which is the point — a `sorry` inside an `example` compiles with
# a warning and leaves no constant behind.

plant_token_fixture() {
  restore_probe
  printf '''\n''' >>"$audit_source"
  cat "$fixtures/$1" >>"$audit_source"
}

expect_token_rejection() {
  local fixture="$1"
  local token="$2"
  local label="$3"
  plant_token_fixture "$fixture"
  expect_rejection_matching \
    "contains an authored \`$token\` trust token" "$label"
}

step_begin
plant_token_fixture benign.lean.txt
step_end "step 2   plant the benign fixture"
expect_acceptance "comments, strings, projections, a bodied opaque, and \`admit\`"

expect_token_rejection partial.lean.txt partial "partial declaration"
expect_token_rejection unsafe.lean.txt unsafe "unsafe declaration"
expect_token_rejection sorry.lean.txt sorry "sorry in a named theorem"
# The one that says finding L1 is closed: an `example` leaves no constant, so
# only the source pass can see this.
expect_token_rejection example-sorry.lean.txt sorry "sorry inside an example"
expect_token_rejection native-decide.lean.txt native_decide "native_decide"
expect_token_rejection axiom.lean.txt axiom "axiom declaration"

# --- 3. planted declarations -------------------------------------------------
#
# These three are not tokens, so each is a whole module: compiled alone, its
# olean placed ahead of the real build, and imported by the scratch root.

# Compile one fixture as a whole module and hang it off the scratch root. The
# module name is what the source path, the olean path and the import have to
# agree on; the namespace inside the fixture is its own business, and two of
# them deliberately declare into somebody else's.
plant_module_fixture() {
  local fixture="$1"
  local module="$2"
  restore_probe
  planted_module="$module"
  cp "$fixtures/$fixture" "$probe/Effect4Test/${module}.lean"
  # From inside the scratch tree, so that `lean` derives the module name
  # `Effect4Test.<module>` from the path relative to its root.
  if ! (cd "$probe" && LEAN_PATH="$real_lean_path" lean \
      -o "$planted_lib/Effect4Test/${module}.olean" \
      "Effect4Test/${module}.lean") >"$probe_log" 2>&1; then
    echo "FAIL the planted module $fixture does not compile" >&2
    tail -60 "$probe_log" >&2
    exit 1
  fi
  add_root_import "Effect4Test.${module}"
}

step_begin
plant_module_fixture opaque.lean.txt PlantedOpaque
step_end "step 3a  compile the bodyless-opaque module"
expect_rejection_matching \
  "Effect4Test.PlantedOpaque.plantedBodylessOpaque is an \`opaque\` with no body" \
  "bodyless opaque"

step_begin
plant_module_fixture unadmitted-choice.lean.txt PlantedChoice
step_end "step 3b  compile the unadmitted-choice module"
expect_rejection_matching \
  "declaration Effect4Test.Audit.PlantedChoice.plantedUnadmittedChoice reaches unexpected axiom Classical.choice" \
  "unadmitted Classical.choice dependency"

# The cross-module admission attack. `Skeleton.render` is exactly admitted and
# its real equation lemmas live in another module, so the gate has to inherit
# its admission across that boundary. This module spells `render.proof_1` by
# hand — Lean reserves nothing about that name and declares it without
# complaint — and the gate must still refuse it.
step_begin
plant_module_fixture forged-auxiliary.lean.txt PlantedAuxiliary
step_end "step 3c  compile the forged-auxiliary module"
expect_rejection_matching \
  "declaration Effect4.Target.EffectV4.Skeleton.render.proof_1 reaches unexpected axiom Classical.choice" \
  "hand-spelled auxiliary of an admitted declaration"

restore_probe

# --- 4. the narrow harnesses -------------------------------------------------

step_begin
"$repo_root/scripts/test-source-trust-tokenizer.sh" "$repo_root"
step_end "step 4a  source tokenizer fixtures"

step_begin
"$repo_root/scripts/test-trust-boundaries.sh" "$repo_root"
step_end "step 4b  exact implementation admissions"

step_begin
(cd "$repo_root" && lake env lean "$fixtures/expr-equality.lean.txt")
step_end "step 4c  Expr equality probes"

printf 'PASS trust gate: %d planted defects rejected, %d accepted, %ss\n' \
  "$rejected" "$accepted" "$(( $(date +%s) - run_start ))"
