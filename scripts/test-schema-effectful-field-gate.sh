#!/usr/bin/env bash
# usage: EFFECT4_EFFECT_NODE_MODULES=<pinned node_modules> ./scripts/test-schema-effectful-field-gate.sh
#
# Exercises whether `scripts/check-schema-effectful-field.sh` reacts to
# specified drift. This exercises the DETECTOR, not the field API. A pass here
# says nothing about rc.112 semantics; it says only that the five named
# harness mutations cannot return a vacuous success, and that each is caught at
# the stage that owns it.
set -euo pipefail

repo_root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd -P)"
gate="$repo_root/scripts/check-schema-effectful-field.sh"
harness_dir="$repo_root/harness/schema-effectful-field"

api="$harness_dir/api.ts"
floating="$harness_dir/floating.tail.ts"
driver="$harness_dir/check.mjs"
generator="$harness_dir/Generate.lean"
guarded=("$api" "$floating" "$driver" "$generator")

tmp_parent="${TMPDIR:-/tmp}"
tmp_parent="${tmp_parent%/}"
tmp_root="$(mktemp -d "$tmp_parent/effect4-effectful-field-gate.XXXXXX")"

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
    "$tmp_parent"/effect4-effectful-field-gate.*) rm -rf -- "$tmp_root" ;;
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
  if ! grep -Fq -- 'schema effectful-field harness: host oracle rejected the field API' "$log"; then
    printf 'FAIL %s was rejected without the gate naming its own refusal\n' "$name" >&2
    cat "$log" >&2
    restore_all
    exit 1
  fi
  restore_all
  printf 'PASS rejected: %s\n' "$name"
}

# 1. the service write disappears, so read-before-write is no longer performed
expect_reject 'dropped service write' "$api" 'runtime failed' \
  -e '/yield\* service\.writeEmail(source, value)/d'

# 2. the read row widens its error type, breaking the exact directional rows
expect_reject 'widened read error row' "$api" 'direct TypeScript rejected fixture' \
  -e 's/Effect\.Effect<string, ReadEmailError, UserFieldPolicy>/Effect.Effect<string, ReadEmailError | WriteEmailError, UserFieldPolicy>/'

# 3. the floating mutant stops floating, so its named diagnostic disappears
expect_reject 'silenced floatingEffect mutant' "$floating" 'unexpected effect-tsgo result' \
  -e 's/^email\.replace/export const kept = email.replace/'

# 4. the expected diagnostic list is edited to name the wrong diagnostic
expect_reject 'changed expected diagnostic list' "$driver" 'unexpected effect-tsgo result' \
  -e 's/\["missingEffectError"\]/["floatingEffect"]/'

# 5. the Lean-generated module binds a method the pinned service does not have
expect_reject 'corrupted Lean-generated api' "$generator" 'Lean-generated TypeScript rejected' \
  -e 's/methodName := "readEmail"/methodName := "readMail"/'

if ! "$gate" >"$tmp_root/restored.log" 2>&1; then
  printf 'FAIL the restored harness no longer passes the gate\n' >&2
  cat "$tmp_root/restored.log" >&2
  exit 1
fi
printf 'PASS restored harness accepted\n'

printf 'PASS schema effectful-field gate reacts to 5/5 specified harness mutations\n'
printf 'NOTE detector receipt only; says nothing about rc.112 semantics or field denotation\n'
