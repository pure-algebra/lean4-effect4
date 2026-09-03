#!/usr/bin/env bash
# usage: EFFECT4_EFFECT_NODE_MODULES=<pinned node_modules> ./scripts/test-schema-typescript-generation-gate.sh
#
# Exercises whether `scripts/check-schema-typescript-generation.sh` reacts to
# specified drift. This exercises the DETECTOR, not the generator. A pass here
# says nothing about rc.112 Schema semantics; it says only that the eight named
# harness mutations cannot return a vacuous success, and that the three runtime
# receipts are actually executed rather than merely present.
set -euo pipefail

repo_root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd -P)"
gate="$repo_root/scripts/check-schema-typescript-generation.sh"
harness_dir="$repo_root/harness/schema-generation"

person="$harness_dir/Person.generated.ts"
corpus="$harness_dir/AllRepresentations.generated.ts"
two_roots="$harness_dir/TwoRoots.generated.ts"
runtime_check="$harness_dir/runtime-check.ts"
coverage_check="$harness_dir/coverage-runtime-check.ts"
multi_check="$harness_dir/multi-runtime-check.ts"
tsconfig="$harness_dir/tsconfig.json"
guarded=("$person" "$corpus" "$two_roots" "$runtime_check" "$coverage_check"
  "$multi_check" "$tsconfig")

tmp_parent="${TMPDIR:-/tmp}"
tmp_parent="${tmp_parent%/}"
tmp_root="$(mktemp -d "$tmp_parent/effect4-schema-generation-gate.XXXXXX")"

restore_all() {
  local path
  for path in "${guarded[@]}"; do
    cp -- "$tmp_root/before/$(basename "$path")" "$path"
  done
}

cleanup() {
  local status=$?
  set +e
  local path
  if [[ -d "$tmp_root/before" ]]; then
    restore_all
    for path in "${guarded[@]}"; do
      if ! cmp -s -- "$tmp_root/before/$(basename "$path")" "$path"; then
        printf 'FAIL harness file was not restored: %s\n' "$path" >&2
        status=1
      fi
    done
  fi
  case "$tmp_root" in
    "$tmp_parent"/effect4-schema-generation-gate.*) rm -rf -- "$tmp_root" ;;
    *) printf 'FAIL refusing to remove unexpected path: %s\n' "$tmp_root" >&2; status=1 ;;
  esac
  exit "$status"
}
trap cleanup EXIT

[[ -x "$gate" ]] || { printf 'FAIL gate is not executable: %s\n' "$gate" >&2; exit 1; }
for path in "${guarded[@]}"; do
  [[ -f "$path" && ! -L "$path" ]] || {
    printf 'FAIL harness input is absent, not regular, or a symlink: %s\n' "$path" >&2
    exit 1
  }
done

mkdir -p "$tmp_root/before"
for path in "${guarded[@]}"; do
  cp -- "$path" "$tmp_root/before/$(basename "$path")"
done

if ! "$gate" >"$tmp_root/baseline.log" 2>&1; then
  printf 'FAIL the unmutated harness did not pass the gate\n' >&2
  cat "$tmp_root/baseline.log" >&2
  exit 1
fi
printf 'PASS baseline harness accepted\n'

# Rewrites one guarded file through sed, runs the gate, and requires both a
# nonzero exit and the signal owned by the stage that should have caught it.
expect_reject() {
  local name="$1" target="$2" signal="$3"
  shift 3
  local log="$tmp_root/$name.log"
  local original="$tmp_root/before/$(basename "$target")"
  sed "$@" -- "$original" >"$target"
  if cmp -s -- "$original" "$target"; then
    printf 'FAIL mutant %s did not change %s; the mutation is vacuous\n' "$name" "$target" >&2
    restore_all
    exit 1
  fi
  if "$gate" >"$log" 2>&1; then
    printf 'FAIL gate accepted a mutant it must reject: %s\n' "$name" >&2
    cat "$log" >&2
    restore_all
    exit 1
  fi
  if ! grep -Fq -- "$signal" "$log"; then
    printf 'FAIL %s was rejected, but the expected signal was absent: %s\n' "$name" "$signal" >&2
    cat "$log" >&2
    restore_all
    exit 1
  fi
  restore_all
  printf 'PASS rejected: %s\n' "$name"
}

# 1. the committed document fixture drifts from what Lean emits
expect_reject 'document fixture byte drift' "$person" 'Person.generated.ts differ' \
  -e 's/"Ada"/"Bob"/'

# 2. the committed 22-constructor corpus drifts from what Lean emits
expect_reject 'corpus fixture byte drift' "$corpus" 'AllRepresentations.generated.ts differ' \
  -e 's/"case\/Declaration"/"case\/DeclaratioN"/'

# 3. the committed two-root multi-document drifts from what Lean emits
expect_reject 'multi-document fixture byte drift' "$two_roots" 'TwoRoots.generated.ts differ' \
  -e 's/"shared"/"sharee"/'

# 4. a document runtime assertion is deleted
expect_reject 'deleted document runtime assertion' "$runtime_check" \
  'runtime-check.ts must keep exactly 6 assertions' \
  -e '/generated document lost a property signature/d'

# 5. a corpus runtime assertion is deleted
expect_reject 'deleted corpus runtime assertion' "$coverage_check" \
  'coverage-runtime-check.ts must keep exactly 2 assertions' \
  -e '/check constructor coverage drift/d'

# 6. a multi-document runtime assertion is deleted
expect_reject 'deleted multi-document runtime assertion' "$multi_check" \
  'multi-runtime-check.ts must keep exactly 4 assertions' \
  -e '/generated multi-document references table changed size/d'

# 7. a document runtime assertion is inverted, so it must fire on correct bytes
expect_reject 'inverted document runtime assertion' "$runtime_check" \
  'generated associated data changed' \
  -e 's/adaObject\["name"\] !== "Ada"/adaObject["name"] === "Ada"/'

# 8. a checked file leaves the project, shrinking the language-service file set
expect_reject 'corpus runtime check left the project' "$tsconfig" \
  'language service did not report 6 clean v4 files' \
  -e '/"\.\/coverage-runtime-check\.ts",/d'

if ! "$gate" >"$tmp_root/restored.log" 2>&1; then
  printf 'FAIL the restored harness no longer passes the gate\n' >&2
  cat "$tmp_root/restored.log" >&2
  exit 1
fi
printf 'PASS restored harness accepted\n'

printf 'PASS schema TypeScript generation gate reacts to 8/8 specified harness mutations\n'
printf 'NOTE detector receipt only; says nothing about rc.112 Schema semantics\n'
