#!/usr/bin/env bash
# Byte-for-byte drift gate for the TypeScript estate's generated files,
# ts/eff/{eff,json,profile}.gen.ts: the tracked files must be exactly what
# scripts/generate-ts-eff.sh writes from the current Lean environment.
#
#   ./scripts/check-ts-eff.sh
#
# ## Stamp (rule 9)
#
# The key is this script, the generator script, the toolchain, the Lake trace of
# `Tools.TsGen` (Lake's hash of that module's source together with the traces of
# everything it imports: the World reader, the native table, the reader's heads,
# the codegen profile), the two files the generator reads at run time
# (`lakefile.toml` for the typescript revision in the address,
# `src/Effect4/Codegen/Print.lean` for the head cross-check), and the three tracked
# `.gen.ts` files themselves — so a hand edit of a generated file is a miss and a
# failure, and a sweep with nothing changed under any of these re-runs nothing.
set -euo pipefail

repo_root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd -P)"
. "$repo_root/scripts/lib/portable.sh"
. "$repo_root/scripts/lib/stamp.sh"

gate=ts-eff
generator="$repo_root/scripts/generate-ts-eff.sh"
files=(eff.gen.ts json.gen.ts profile.gen.ts)
cd "$repo_root"

[[ -x "$generator" ]] || { printf 'FAIL %s: %s is not executable\n' "$gate" "$generator" >&2; exit 1; }
for f in "${files[@]}"; do
  [[ -f "ts/eff/$f" && ! -L "ts/eff/$f" ]] || {
    printf 'FAIL %s: ts/eff/%s is absent, not regular, or a symlink\n' "$gate" "$f" >&2
    exit 1
  }
done

# The trace must describe the current sources, so build before keying.
build_log="$(mktemp "${TMPDIR:-/tmp}/effect4-ts-eff-build.XXXXXX")"
if ! lake build Tools.TsGen >"$build_log" 2>&1; then
  printf 'FAIL %s: lake build Tools.TsGen failed\n' "$gate" >&2
  cat "$build_log" >&2
  rm -f "$build_log"
  exit 1
fi
rm -f "$build_log"

key="$(stamp_key \
  "${BASH_SOURCE[0]}" "$generator" \
  "$repo_root/lean-toolchain" "$repo_root/lakefile.toml" \
  "$repo_root/src/Effect4/Codegen/Print.lean" \
  "$stamp_build_lib/Tools/TsGen.trace" \
  "$repo_root/ts/eff/eff.gen.ts" "$repo_root/ts/eff/json.gen.ts" "$repo_root/ts/eff/profile.gen.ts")"
if stamp_hit "$gate" "$key"; then
  stamp_report "$gate" "$key"
  exit 0
fi

tmp_parent="${TMPDIR:-/tmp}"
tmp_parent="${tmp_parent%/}"
tmp_root="$(mktemp -d "$tmp_parent/effect4-ts-eff-check.XXXXXX")"
cleanup() {
  local cleanup_rc=$?
  set +e
  case "$tmp_root" in
    "$tmp_parent"/effect4-ts-eff-check.*) rm -rf -- "$tmp_root" ;;
    *) printf 'FAIL refusing to remove unexpected path: %s\n' "$tmp_root" >&2; cleanup_rc=1 ;;
  esac
  exit "$cleanup_rc"
}
trap cleanup EXIT

summary="$("$generator" "$tmp_root" | sed -n '1p')"
for f in "${files[@]}"; do
  if ! cmp -s -- "$tmp_root/$f" "ts/eff/$f"; then
    printf 'FAIL %s: ts/eff/%s is not what Lean emits; run ./scripts/generate-ts-eff.sh\n' "$gate" "$f" >&2
    diff -u -- "ts/eff/$f" "$tmp_root/$f" >&2 | head -60 || true
    exit 1
  fi
done

printf 'PASS %s: ts/eff/{eff,json,profile}.gen.ts are what Lean emits; %s\n' "$gate" "$summary"
stamp_write "$gate" "$key" "$summary"
