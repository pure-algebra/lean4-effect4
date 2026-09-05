#!/usr/bin/env bash
# The TypeScript reader against Lean's reader over the printed corpus.
#
# `Tools.Corpus` writes 400 generated programs and the wire corpus as `.ts` (the printer's
# bytes) with, beside each, the JSON of the program Lean's own reader gets back after the
# printer (`Api.roundTrip`). `ts/eff/check.ts` reads every `.ts` with `readTypeScript` and
# must produce the same bytes; the truth lane's exported files (`harness/truth/generated`)
# are read too, with the same oracles by name. `bun test` runs the pinned cases.
#
#   scripts/check-ts-eff-corpus.sh
#
# Host lane: needs `bun` and the pinned install under ts/eff/node_modules
# (`bun install --frozen-lockfile` runs when it is absent).
#
# ## Stamp (rule 9)
#
# The key is this script, the toolchain, the Lake trace of `Tools.Corpus` (its source and the
# traces of the generator, the printer, the reader and the JSON writer it imports), every
# source of the TypeScript package (the hand-written and the generated files, the tests, the
# pins), the truth lane's files, and the bun version. A pass with the same key is the same
# verdict.
set -euo pipefail

repo_root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd -P)"
. "$repo_root/scripts/lib/portable.sh"
. "$repo_root/scripts/lib/stamp.sh"

gate=ts-eff-corpus
cd "$repo_root"

bun_cmd="$(command -v bun || command -v bun.exe || true)"
[ -n "$bun_cmd" ] || { printf 'FAIL %s: bun is not on PATH (host lane)\n' "$gate" >&2; exit 1; }
bun_path() {
  case "$bun_cmd" in *.exe) wslpath -w "$1" ;; *) printf '%s' "$1" ;; esac
}
bun_version="$("$bun_cmd" --version)"

build_log="$(mktemp "${TMPDIR:-/tmp}/effect4-ts-eff-corpus-build.XXXXXX")"
if ! lake build Tools.Corpus >"$build_log" 2>&1; then
  printf 'FAIL %s: lake build Tools.Corpus failed\n' "$gate" >&2
  cat "$build_log" >&2
  rm -f "$build_log"
  exit 1
fi
rm -f "$build_log"

key="$(stamp_key \
  "${BASH_SOURCE[0]}" "$repo_root/lean-toolchain" \
  "$stamp_build_lib/Tools/Corpus.trace" \
  "$repo_root"/ts/eff/*.ts "$repo_root/ts/eff/test" \
  "$repo_root/ts/eff/package.json" "$repo_root/ts/eff/bun.lock" "$repo_root/ts/eff/tsconfig.json" \
  "$repo_root/harness/truth/generated" \
  "$(stamp_fact bun "$bun_version")")"
if stamp_hit "$gate" "$key"; then
  stamp_report "$gate" "$key"
  exit 0
fi

tmp_parent="${TMPDIR:-/tmp}"
tmp_parent="${tmp_parent%/}"
tmp_root="$(mktemp -d "$tmp_parent/effect4-ts-eff-corpus.XXXXXX")"
cleanup() {
  local cleanup_rc=$?
  set +e
  case "$tmp_root" in
    "$tmp_parent"/effect4-ts-eff-corpus.*) rm -rf -- "$tmp_root" ;;
    *) printf 'FAIL refusing to remove unexpected path: %s\n' "$tmp_root" >&2; cleanup_rc=1 ;;
  esac
  exit "$cleanup_rc"
}
trap cleanup EXIT

corpus_line="$(lean_run tools/Tools/Corpus.lean "$tmp_root" 400 4)"

cd "$repo_root/ts/eff"
if [[ ! -d node_modules ]]; then
  "$bun_cmd" install --frozen-lockfile >"$tmp_root/install.log" 2>&1 || {
    printf 'FAIL %s: bun install --frozen-lockfile failed\n' "$gate" >&2
    cat "$tmp_root/install.log" >&2
    exit 1
  }
fi

check_out="$tmp_root/check.log"
if ! "$bun_cmd" run check.ts "$(bun_path "$tmp_root")" "$(bun_path "$repo_root/harness/truth/generated")" --oracle "$(bun_path "$tmp_root")" >"$check_out" 2>&1; then
  printf 'FAIL %s: the reader disagrees with Lean on the corpus\n' "$gate" >&2
  cat "$check_out" >&2
  exit 1
fi
check_line="$(sed -n '1p' "$check_out")"

test_out="$tmp_root/test.log"
if ! "$bun_cmd" test >"$test_out" 2>&1; then
  printf 'FAIL %s: bun test failed\n' "$gate" >&2
  cat "$test_out" >&2
  exit 1
fi
test_line="$(grep -E '^ *[0-9]+ pass' "$test_out" | head -1 | sed 's/^ *//')"

summary="$check_line; bun test: $test_line; corpus: $corpus_line"
printf 'PASS %s: %s\n' "$gate" "$summary"
stamp_write "$gate" "$key" "$summary"
