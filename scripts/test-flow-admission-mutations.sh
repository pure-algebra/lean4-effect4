#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd -P)"
tmp_parent="${TMPDIR:-/tmp}"
tmp_parent="${tmp_parent%/}"
tmp_root="$(mktemp -d "$tmp_parent/effect4-flow-mutations.XXXXXX")"
baseline_root="$tmp_root/baseline"
mutant_root="$tmp_root/mutant"
before_manifest="$tmp_root/source-before.blobs"
after_manifest="$tmp_root/source-after.blobs"
checkout_verified=0

fail() {
  printf 'FAIL %s\n' "$*" >&2
  exit 1
}

snapshot_checkout() {
  local output="$1"
  (
    cd -- "$repo_root"
    while IFS= read -r -d '' path; do
      local_path="${path#./}"
      if [[ -L "$path" ]]; then
        digest="$(printf 'symlink:%s' "$(readlink "$path")" | git hash-object --stdin)"
      else
        digest="$(git hash-object "$path")"
      fi
      printf '%s  %s\n' "$digest" "$local_path"
    done < <(find \
      Effect4/Flow \
      Effect4Test/Flow/AdmissionContract.lean \
      scripts/test-flow-admission-mutations.sh \
      \( -type f -o -type l \) -print0)
  ) | LC_ALL=C sort >"$output"
}

verify_checkout_unchanged() {
  snapshot_checkout "$after_manifest"
  if ! cmp -s -- "$before_manifest" "$after_manifest"; then
    printf 'FAIL Flow source or frozen battery changed while mutation tests ran\n' >&2
    diff -u -- "$before_manifest" "$after_manifest" >&2 || true
    exit 1
  fi
  checkout_verified=1
  printf 'PASS Flow source and frozen battery byte-unchanged\n'
}

cleanup() {
  local status=$?
  set +e
  if [[ "$checkout_verified" -eq 0 && -f "$before_manifest" ]]; then
    snapshot_checkout "$after_manifest"
    if ! cmp -s -- "$before_manifest" "$after_manifest"; then
      printf 'FAIL Flow source or frozen battery changed while mutation tests ran\n' >&2
      diff -u -- "$before_manifest" "$after_manifest" >&2 || true
      status=1
    fi
  fi
  case "$tmp_root" in
    "$tmp_parent"/effect4-flow-mutations.*) rm -rf -- "$tmp_root" ;;
    *) printf 'FAIL refusing to remove unexpected temporary path: %s\n' "$tmp_root" >&2; status=1 ;;
  esac
  exit "$status"
}
trap cleanup EXIT

copy_project() {
  local destination="$1"
  mkdir -p -- "$destination"
  local item
  for item in \
    Effect4 Effect4Test test scripts \
    lakefile.toml lake-manifest.json lean-toolchain \
    Effect4.lean Effect4Test.lean; do
    if [[ -e "$repo_root/$item" ]]; then
      cp -R -- "$repo_root/$item" "$destination/"
    fi
  done
}

run_build() {
  local project="$1"
  local log="$2"
  if ! (cd -- "$project" && lake build Effect4.Flow.Checked) >"$log" 2>&1; then
    printf 'FAIL mutant did not remain buildable\n' >&2
    tail -80 "$log" >&2
    exit 1
  fi
}

run_contract_pass() {
  local project="$1"
  local log="$2"
  if ! (cd -- "$project" && \
      lake env lean Effect4Test/Flow/AdmissionContract.lean) >"$log" 2>&1; then
    printf 'FAIL unmodified frozen Flow battery did not pass\n' >&2
    tail -100 "$log" >&2
    exit 1
  fi
}

run_contract_killed() {
  local project="$1"
  local log="$2"
  shift 2
  local status
  set +e
  (cd -- "$project" && \
    lake env lean Effect4Test/Flow/AdmissionContract.lean) >"$log" 2>&1
  status=$?
  set -e
  if [[ "$status" -eq 0 ]]; then
    fail "mutant survived the frozen Flow battery"
  fi
  local signal
  for signal in "$@"; do
    if ! grep -Fq -- "$signal" "$log"; then
      printf 'FAIL battery rejected mutant, but expected signal was absent: %s\n' "$signal" >&2
      tail -100 "$log" >&2
      exit 1
    fi
  done
}

apply_mutant() {
  local name="$1"
  local patch_file="$tmp_root/$name.patch"
  case "$name" in
    scan-order)
      cat >"$patch_file" <<'PATCH'
diff --git a/Effect4/Flow/Admission.lean b/Effect4/Flow/Admission.lean
--- a/Effect4/Flow/Admission.lean
+++ b/Effect4/Flow/Admission.lean
@@ -58,8 +58,8 @@ deriving DecidableEq, Repr
 
 /-- The exhaustive first-error scan order. -/
 def scan : List AdmissionClause := [
-  .alphabetMismatch,
   .duplicateBlockId,
+  .alphabetMismatch,
   .duplicateDecisionId,
   .nonCanonicalBlockOrder,
   .emptyRoots,
@@ -497,43 +497,43 @@ private theorem scan_nodup : scan.Nodup := by decide
 
 private def clausesBefore : AdmissionClause → List AdmissionClause
-  | .alphabetMismatch => []
-  | .duplicateBlockId => [.alphabetMismatch]
-  | .duplicateDecisionId => [.alphabetMismatch, .duplicateBlockId]
+  | .alphabetMismatch => [.duplicateBlockId]
+  | .duplicateBlockId => []
+  | .duplicateDecisionId => [.duplicateBlockId, .alphabetMismatch]
   | .nonCanonicalBlockOrder =>
-      [.alphabetMismatch, .duplicateBlockId, .duplicateDecisionId]
+      [.duplicateBlockId, .alphabetMismatch, .duplicateDecisionId]
   | .emptyRoots =>
-      [.alphabetMismatch, .duplicateBlockId, .duplicateDecisionId,
+      [.duplicateBlockId, .alphabetMismatch, .duplicateDecisionId,
        .nonCanonicalBlockOrder]
   | .duplicateRoot =>
-      [.alphabetMismatch, .duplicateBlockId, .duplicateDecisionId,
+      [.duplicateBlockId, .alphabetMismatch, .duplicateDecisionId,
        .nonCanonicalBlockOrder, .emptyRoots]
   | .nonCanonicalRootOrder =>
-      [.alphabetMismatch, .duplicateBlockId, .duplicateDecisionId,
+      [.duplicateBlockId, .alphabetMismatch, .duplicateDecisionId,
        .nonCanonicalBlockOrder, .emptyRoots, .duplicateRoot]
   | .entryNotRoot =>
-      [.alphabetMismatch, .duplicateBlockId, .duplicateDecisionId,
+      [.duplicateBlockId, .alphabetMismatch, .duplicateDecisionId,
        .nonCanonicalBlockOrder, .emptyRoots, .duplicateRoot,
        .nonCanonicalRootOrder]
   | .danglingRoot =>
-      [.alphabetMismatch, .duplicateBlockId, .duplicateDecisionId,
+      [.duplicateBlockId, .alphabetMismatch, .duplicateDecisionId,
        .nonCanonicalBlockOrder, .emptyRoots, .duplicateRoot,
        .nonCanonicalRootOrder, .entryNotRoot]
   | .danglingSuccessor =>
-      [.alphabetMismatch, .duplicateBlockId, .duplicateDecisionId,
+      [.duplicateBlockId, .alphabetMismatch, .duplicateDecisionId,
        .nonCanonicalBlockOrder, .emptyRoots, .duplicateRoot,
        .nonCanonicalRootOrder, .entryNotRoot, .danglingRoot]
   | .unknownOperation =>
-      [.alphabetMismatch, .duplicateBlockId, .duplicateDecisionId,
+      [.duplicateBlockId, .alphabetMismatch, .duplicateDecisionId,
        .nonCanonicalBlockOrder, .emptyRoots, .duplicateRoot,
        .nonCanonicalRootOrder, .entryNotRoot, .danglingRoot,
        .danglingSuccessor]
   | .entryTypeMismatch =>
-      [.alphabetMismatch, .duplicateBlockId, .duplicateDecisionId,
+      [.duplicateBlockId, .alphabetMismatch, .duplicateDecisionId,
        .nonCanonicalBlockOrder, .emptyRoots, .duplicateRoot,
        .nonCanonicalRootOrder, .entryNotRoot, .danglingRoot,
        .danglingSuccessor, .unknownOperation]
   | .termTypeMismatch =>
-      [.alphabetMismatch, .duplicateBlockId, .duplicateDecisionId,
+      [.duplicateBlockId, .alphabetMismatch, .duplicateDecisionId,
        .nonCanonicalBlockOrder, .emptyRoots, .duplicateRoot,
        .nonCanonicalRootOrder, .entryNotRoot, .danglingRoot,
        .danglingSuccessor, .unknownOperation, .entryTypeMismatch]
PATCH
      ;;
    dangling-successor)
      cat >"$patch_file" <<'PATCH'
diff --git a/Effect4/Flow/Block.lean b/Effect4/Flow/Block.lean
--- a/Effect4/Flow/Block.lean
+++ b/Effect4/Flow/Block.lean
@@ -62,7 +62,7 @@ namespace RawTerm
 /-- Direct graph successors named by a raw terminator, in source order. -/
 def successors : RawTerm → List BlockId
   | .ret => []
-  | .jump target => [target]
+  | .jump _ => []
   | .perform _ target => [target]
   | .choose _ left right => [left, right]
 
diff --git a/Effect4/Flow/Raw.lean b/Effect4/Flow/Raw.lean
--- a/Effect4/Flow/Raw.lean
+++ b/Effect4/Flow/Raw.lean
@@ -102,7 +102,7 @@ private def TermWF
   | .ret => block.inputTy = raw.resultTy
   | .jump target =>
       match lookupBlock raw target with
-      | none => False
+      | none => True
       | some targetBlock => targetBlock.inputTy = block.inputTy
   | .perform operation target =>
       match alphabet.lookup operation, lookupBlock raw target with
diff --git a/Effect4/Flow/Admission.lean b/Effect4/Flow/Admission.lean
--- a/Effect4/Flow/Admission.lean
+++ b/Effect4/Flow/Admission.lean
@@ -86,7 +86,7 @@ private def localTermWF
   | .ret => block.inputTy = raw.resultTy
   | .jump target =>
       match lookupBlock raw target with
-      | none => False
+      | none => True
       | some targetBlock => targetBlock.inputTy = block.inputTy
   | .perform operation target =>
       match alphabet.lookup operation, lookupBlock raw target with
@@ -284,7 +284,7 @@ private def termFailure? [DecidableEq Ty]
       else some (.typeMismatch raw.resultTy block.inputTy)
   | .jump target =>
       match lookupBlock raw target with
-      | none => some (.block target)
+      | none => none
       | some targetBlock =>
           if targetBlock.inputTy = block.inputTy then none
           else some (.typeMismatch block.inputTy targetBlock.inputTy)
PATCH
      ;;
    perform-answer)
      cat >"$patch_file" <<'PATCH'
diff --git a/Effect4/Flow/Raw.lean b/Effect4/Flow/Raw.lean
--- a/Effect4/Flow/Raw.lean
+++ b/Effect4/Flow/Raw.lean
@@ -106,9 +106,8 @@ private def TermWF
       | some targetBlock => targetBlock.inputTy = block.inputTy
   | .perform operation target =>
       match alphabet.lookup operation, lookupBlock raw target with
-      | some operation, some targetBlock =>
-          block.inputTy = alphabet.requestTy operation ∧
-          targetBlock.inputTy = alphabet.answerTy operation
+      | some operation, some _ =>
+          block.inputTy = alphabet.requestTy operation
       | _, _ => False
   | .choose _ left right =>
       match lookupBlock raw left, lookupBlock raw right with
diff --git a/Effect4/Flow/Admission.lean b/Effect4/Flow/Admission.lean
--- a/Effect4/Flow/Admission.lean
+++ b/Effect4/Flow/Admission.lean
@@ -90,9 +90,8 @@ private def localTermWF
       | some targetBlock => targetBlock.inputTy = block.inputTy
   | .perform operation target =>
       match alphabet.lookup operation, lookupBlock raw target with
-      | some operation, some targetBlock =>
-          block.inputTy = alphabet.requestTy operation ∧
-          targetBlock.inputTy = alphabet.answerTy operation
+      | some operation, some _ =>
+          block.inputTy = alphabet.requestTy operation
       | _, _ => False
   | .choose _ left right =>
       match lookupBlock raw left, lookupBlock raw right with
@@ -290,11 +289,8 @@ private def termFailure? [DecidableEq Ty]
       match alphabet.lookup operationId, lookupBlock raw target with
       | none, _ => some (.operation operationId)
       | _, none => some (.block target)
-      | some operation, some targetBlock =>
-          if block.inputTy = alphabet.requestTy operation then
-            if targetBlock.inputTy = alphabet.answerTy operation then none
-            else some (.typeMismatch
-              (alphabet.answerTy operation) targetBlock.inputTy)
+      | some operation, some _ =>
+          if block.inputTy = alphabet.requestTy operation then none
           else
             some (.typeMismatch
               (alphabet.requestTy operation) block.inputTy)
PATCH
      ;;
    *) fail "unknown mutant: $name" ;;
  esac
  (cd -- "$mutant_root" && git apply --check "$patch_file") || \
    fail "could not apply $name mutant to the current Flow implementation"
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

run_build "$baseline_root" "$tmp_root/baseline-build.log"
run_contract_pass "$baseline_root" "$tmp_root/baseline-contract.log"
printf 'PASS baseline build and frozen Flow battery\n'

reset_mutant
apply_mutant scan-order
run_build "$mutant_root" "$tmp_root/scan-order-build.log"
run_contract_killed "$mutant_root" "$tmp_root/scan-order-contract.log" \
  'AdmissionContract.lean:182:0: error' \
  'AdmissionContract.lean:548:0: error'
printf 'PASS mutant 1/3 killed: swapped first-error scan order\n'

reset_mutant
apply_mutant dangling-successor
run_build "$mutant_root" "$tmp_root/dangling-successor-build.log"
run_contract_killed "$mutant_root" "$tmp_root/dangling-successor-contract.log" \
  'AdmissionContract.lean:474:0: error' \
  'AdmissionContract.lean:580:0: error'
printf 'PASS mutant 2/3 killed: weakened dangling-jump admission\n'

reset_mutant
apply_mutant perform-answer
run_build "$mutant_root" "$tmp_root/perform-answer-build.log"
run_contract_killed "$mutant_root" "$tmp_root/perform-answer-contract.log" \
  'AdmissionContract.lean:508:0: error'
printf 'PASS mutant 3/3 killed: removed perform answer-target equality\n'

verify_checkout_unchanged
printf 'PASS finite Flow-admission mutation coverage: 3/3 specified mutants killed\n'
