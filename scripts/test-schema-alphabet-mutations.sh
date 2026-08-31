#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd -P)"
tmp_parent="$(cd -- "${TMPDIR:-/tmp}" && pwd -P)"
tmp_root="$(mktemp -d "$tmp_parent/effect4-schema-alphabet-mutations.XXXXXX")"
baseline_root="$tmp_root/baseline"
mutant_root="$tmp_root/mutant"
before_manifest="$tmp_root/checkout-before.blobs"
after_manifest="$tmp_root/checkout-after.blobs"
checkout_verified=0

fail() {
  printf 'FAIL %s\n' "$*" >&2
  exit 1
}

case "$tmp_root" in
  "$tmp_parent"/effect4-schema-alphabet-mutations.*) ;;
  *) fail "temporary directory did not match its validated parent: $tmp_root" ;;
esac

snapshot_checkout() {
  local output="$1"
  (
    cd -- "$repo_root"
    local path digest
    for path in \
      Effect4/Schema/Representation.lean \
      Effect4Test/Schema/RepresentationContract.lean \
      Effect4Test/Schema/SubAlphabetContract.lean \
      Effect4Test/Counterexamples/Schema/SemanticTagSeparation.lean \
      Effect4Test/Counterexamples/Schema/WireSpellingDrift.lean \
      scripts/test-schema-alphabet-mutations.sh; do
      [[ -f "$path" ]] || fail "required Schema source or battery is absent: $path"
      digest="$(git hash-object "$path")"
      printf '%s  %s\n' "$digest" "$path"
    done
  ) | LC_ALL=C sort >"$output"
}

verify_checkout_unchanged() {
  snapshot_checkout "$after_manifest"
  if ! cmp -s -- "$before_manifest" "$after_manifest"; then
    printf 'FAIL Schema source or frozen battery changed while mutation tests ran\n' >&2
    diff -u -- "$before_manifest" "$after_manifest" >&2 || true
    exit 1
  fi
  checkout_verified=1
  printf 'PASS Schema source and frozen batteries byte-unchanged\n'
}

cleanup() {
  local status=$?
  set +e
  if [[ "$checkout_verified" -eq 0 && -f "$before_manifest" ]]; then
    snapshot_checkout "$after_manifest"
    if ! cmp -s -- "$before_manifest" "$after_manifest"; then
      printf 'FAIL Schema source or frozen battery changed while mutation tests ran\n' >&2
      diff -u -- "$before_manifest" "$after_manifest" >&2 || true
      status=1
    fi
  fi
  case "$tmp_root" in
    "$tmp_parent"/effect4-schema-alphabet-mutations.*) rm -rf -- "$tmp_root" ;;
    *)
      printf 'FAIL refusing to remove unexpected temporary path: %s\n' "$tmp_root" >&2
      status=1
      ;;
  esac
  exit "$status"
}
trap cleanup EXIT

copy_project() {
  local destination="$1"
  mkdir -p -- "$destination"
  local item
  for item in \
    Effect4 Effect4Test \
    lakefile.toml lake-manifest.json lean-toolchain \
    Effect4.lean Effect4Test.lean; do
    if [[ -e "$repo_root/$item" ]]; then
      cp -R -- "$repo_root/$item" "$destination/"
    fi
  done
}

run_source_build() {
  local project="$1"
  local log="$2"
  if ! (cd -- "$project" && lake build Effect4.Schema.Representation) \
      >"$log" 2>&1; then
    printf 'FAIL Schema alphabet mutant did not remain source-buildable\n' >&2
    tail -100 "$log" >&2
    exit 1
  fi
}

run_lean_pass() {
  local project="$1"
  local source_file="$2"
  local log="$3"
  if ! (cd -- "$project" && lake env lean "$source_file") >"$log" 2>&1; then
    printf 'FAIL unmodified Schema battery did not pass: %s\n' "$source_file" >&2
    tail -120 "$log" >&2
    exit 1
  fi
}

run_lean_killed() {
  local project="$1"
  local source_file="$2"
  local log="$3"
  shift 3
  local status signal
  set +e
  (cd -- "$project" && lake env lean "$source_file") >"$log" 2>&1
  status=$?
  set -e
  if [[ "$status" -eq 0 ]]; then
    fail "mutant survived frozen Schema battery: $source_file"
  fi
  for signal in "$@"; do
    if ! grep -Fq -- "$signal" "$log"; then
      printf 'FAIL Schema battery rejected mutant without expected signal: %s\n' \
        "$signal" >&2
      tail -120 "$log" >&2
      exit 1
    fi
  done
}

apply_mutant() {
  local name="$1"
  local patch_file="$tmp_root/$name.patch"
  case "$name" in
    representation-order)
      cat >"$patch_file" <<'PATCH'
diff --git a/Effect4/Schema/Representation.lean b/Effect4/Schema/Representation.lean
--- a/Effect4/Schema/Representation.lean
+++ b/Effect4/Schema/Representation.lean
@@ -40,9 +40,9 @@ API. A source edit that swaps two constructors can preserve the census and
 -/
 inductive RepresentationTag where
-  /-- An opaque declaration with a required representation and type parameters. -/
-  | declaration
   /-- A non-empty `$ref` into a document's references table. -/
   | reference
+  /-- An opaque declaration with a required representation and type parameters. -/
+  | declaration
   /-- A lazy boundary. Its persisted `checks` are exactly empty. -/
   | suspend
   /-- The `null` keyword. -/
PATCH
      ;;
    literal-order)
      cat >"$patch_file" <<'PATCH'
diff --git a/Effect4/Schema/Representation.lean b/Effect4/Schema/Representation.lean
--- a/Effect4/Schema/Representation.lean
+++ b/Effect4/Schema/Representation.lean
@@ -364,9 +364,9 @@ inductive LiteralKind where
   /-- A string literal. -/
   | string
-  /-- A finite number literal. Non-finite values are not persistable as literals. -/
-  | number
   /-- A bigint literal. -/
   | bigint
+  /-- A finite number literal. Non-finite values are not persistable as literals. -/
+  | number
   /-- A boolean literal. -/
   | boolean
 deriving DecidableEq, Repr, Inhabited
PATCH
      ;;
    duplicate-keyword-kind)
      cat >"$patch_file" <<'PATCH'
diff --git a/Effect4/Schema/Representation.lean b/Effect4/Schema/Representation.lean
--- a/Effect4/Schema/Representation.lean
+++ b/Effect4/Schema/Representation.lean
@@ -487,3 +487,18 @@
 end PropertyKeyKind
-
+/-- Counterfactual duplicate of the keyword-shaped part of RepresentationTag. -/
+inductive KeywordKind where
+  | null
+  | undefined
+  | void
+  | never
+  | unknown
+  | any
+  | string
+  | number
+  | boolean
+  | bigint
+  | symbol
+  | objectKeyword
+deriving DecidableEq, Repr, Inhabited
+
 end Effect4
PATCH
      ;;
    spelling-drift)
      cat >"$patch_file" <<'PATCH'
diff --git a/Effect4/Schema/Representation.lean b/Effect4/Schema/Representation.lean
--- a/Effect4/Schema/Representation.lean
+++ b/Effect4/Schema/Representation.lean
@@ -129,6 +129,6 @@ def tagName : RepresentationTag → String
   | .literal => "Literal"
   | .uniqueSymbol => "UniqueSymbol"
-  | .objectKeyword => "ObjectKeyword"
+  | .objectKeyword => "objectKeyword"
   | .enum => "Enum"
   | .templateLiteral => "TemplateLiteral"
   | .arrays => "Arrays"
@@ -162,6 +162,6 @@ def ofTagName : String → Option RepresentationTag
   | "Literal" => some .literal
   | "UniqueSymbol" => some .uniqueSymbol
-  | "ObjectKeyword" => some .objectKeyword
+  | "objectKeyword" => some .objectKeyword
   | "Enum" => some .enum
   | "TemplateLiteral" => some .templateLiteral
   | "Arrays" => some .arrays
PATCH
      ;;
    spelling-permutation)
      cat >"$patch_file" <<'PATCH'
diff --git a/Effect4/Schema/Representation.lean b/Effect4/Schema/Representation.lean
--- a/Effect4/Schema/Representation.lean
+++ b/Effect4/Schema/Representation.lean
@@ -92,5 +92,5 @@
 -/
 def census : List RepresentationTag :=
-  [.declaration, .reference, .suspend,
+  [.reference, .declaration, .suspend,
    .null, .undefined, .void, .never, .unknown, .any,
    .string, .number, .boolean, .bigint, .symbol,
@@ -108,4 +108,4 @@
 def tagName : RepresentationTag → String
-  | .declaration => "Declaration"
-  | .reference => "Reference"
+  | .declaration => "Reference"
+  | .reference => "Declaration"
   | .suspend => "Suspend"
@@ -140,4 +140,4 @@
 def ofTagName : String → Option RepresentationTag
-  | "Declaration" => some .declaration
-  | "Reference" => some .reference
+  | "Declaration" => some .reference
+  | "Reference" => some .declaration
   | "Suspend" => some .suspend
PATCH
      ;;
    *) fail "unknown Schema alphabet mutant: $name" ;;
  esac
  (cd -- "$mutant_root" && git apply --check "$patch_file") || \
    fail "could not apply $name mutant to the current Schema implementation"
  (cd -- "$mutant_root" && git apply "$patch_file")
}

reset_mutant() {
  if [[ -e "$mutant_root" ]]; then
    case "$mutant_root" in
      "$tmp_root"/*) rm -rf -- "$mutant_root" ;;
      *) fail "refusing to remove unexpected mutant path: $mutant_root" ;;
    esac
  fi
  cp -R -- "$baseline_root" "$mutant_root"
}

snapshot_checkout "$before_manifest"
copy_project "$baseline_root"

run_source_build "$baseline_root" "$tmp_root/baseline-build.log"
run_lean_pass "$baseline_root" \
  Effect4Test/Schema/RepresentationContract.lean \
  "$tmp_root/baseline-representation.log"
run_lean_pass "$baseline_root" \
  Effect4Test/Schema/SubAlphabetContract.lean \
  "$tmp_root/baseline-subalphabet.log"
run_lean_pass "$baseline_root" \
  Effect4Test/Counterexamples/Schema/SemanticTagSeparation.lean \
  "$tmp_root/baseline-semantic-separation.log"
run_lean_pass "$baseline_root" \
  Effect4Test/Counterexamples/Schema/WireSpellingDrift.lean \
  "$tmp_root/baseline-wire-spelling.log"
printf 'PASS baseline Schema alphabet source and frozen declaration batteries\n'

reset_mutant
apply_mutant representation-order
run_source_build "$mutant_root" "$tmp_root/representation-order-build.log"
run_lean_killed "$mutant_root" \
  Effect4Test/Schema/RepresentationContract.lean \
  "$tmp_root/representation-order-contract.log" \
  'RepresentationContract.lean:' \
  'RepresentationTag.rec'
printf 'PASS mutant 1/5 killed: RepresentationTag constructor-order swap\n'

reset_mutant
apply_mutant literal-order
run_source_build "$mutant_root" "$tmp_root/literal-order-build.log"
run_lean_killed "$mutant_root" \
  Effect4Test/Schema/SubAlphabetContract.lean \
  "$tmp_root/literal-order-contract.log" \
  'SubAlphabetContract.lean:' \
  'LiteralKind.rec'
printf 'PASS mutant 2/5 killed: LiteralKind constructor-order swap\n'

reset_mutant
apply_mutant duplicate-keyword-kind
run_source_build "$mutant_root" "$tmp_root/duplicate-keyword-kind-build.log"
run_lean_killed "$mutant_root" \
  Effect4Test/Counterexamples/Schema/SemanticTagSeparation.lean \
  "$tmp_root/duplicate-keyword-kind-witness.log" \
  'SemanticTagSeparation.lean:' \
  'Effect4.KeywordKind'
printf 'PASS mutant 3/5 killed: parallel Effect4.KeywordKind duplicate\n'

reset_mutant
apply_mutant spelling-drift
run_source_build "$mutant_root" "$tmp_root/spelling-drift-build.log"
run_lean_killed "$mutant_root" \
  Effect4Test/Schema/RepresentationContract.lean \
  "$tmp_root/spelling-drift-contract.log" \
  'RepresentationContract.lean:'
run_lean_killed "$mutant_root" \
  Effect4Test/Counterexamples/Schema/WireSpellingDrift.lean \
  "$tmp_root/spelling-drift-witness.log" \
  'WireSpellingDrift.lean:'
printf 'PASS mutant 4/5 killed: coordinated ObjectKeyword spelling drift\n'

reset_mutant
apply_mutant spelling-permutation
run_source_build "$mutant_root" "$tmp_root/spelling-permutation-build.log"
run_lean_killed "$mutant_root" \
  Effect4Test/Schema/RepresentationContract.lean \
  "$tmp_root/spelling-permutation-contract.log" \
  'RepresentationContract.lean:' \
  'RepresentationTag.declaration.tagName = "Declaration"' \
  'RepresentationTag.ofTagName "Declaration" = some RepresentationTag.declaration'
printf 'PASS mutant 5/5 killed: Declaration/Reference spelling permutation with matching census reorder\n'

verify_checkout_unchanged
printf '%s\n' \
  'PASS finite Schema alphabet mutation coverage: 5/5 specified mutants killed' \
  'NOTE bounded local receipt feeding the parent graph and attached leaves; not itself a proof graph or an exhaustive completeness claim'
