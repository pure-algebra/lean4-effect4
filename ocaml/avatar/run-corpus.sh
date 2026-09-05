#!/usr/bin/env bash
# Round five: run every corpus program on both faces and compare.
# rc.112 is the reference wherever no Lean golden exists, which is every corpus program.
#
# Dune owns the avatar library module order and the three executable modes.
# This driver adds the corpus/rc.112 comparison over those binaries.
set -uo pipefail
here=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
# <repo>/ocaml/avatar -> <repo>. The estate lived under `workshop/OCaml5/` until 2026-09-04.
repo=$(CDPATH= cd -- "$here/../.." && pwd)
. "$repo/ocaml/tools/lib/toolchain.sh"
effect4_toolchain || exit 1
(cd "$repo/ocaml" && dune build avatar) || exit 1
bin=${AVATAR_BIN:-$repo/ocaml/_build/default/avatar}
scratch_parent=${A0_BUILD:-${TMPDIR:-/tmp}}
mkdir -p "$scratch_parent"
out=$(mktemp -d "$scratch_parent/effect4-corpus.XXXXXX")
trap 'rm -rf -- "$out"' EXIT
masks="$repo/ocaml/server/generated/traces/masks.tsv"
face=${AVATAR_CORPUS_OUT:-$here/out/corpus}
mkdir -p "$out/corpus_rc" "$out/corpus_hosts" "$face"
node_modules="$(effect4_node_path "${EFFECT4_EFFECT_NODE_MODULES:-$repo/ts/eff/node_modules}")"

progs=$(grep '^prog ' "$here/corpus/programs.txt" | awk '{print $2}')
avatar_ok=0; avatar_bad=0; rc_ok=0; rc_skip=0; rc_bad=0
: > "$out/corpus-skips.txt"
for p in $progs; do
  if EFFECT4_FAMILY=corpus EFFECT4_PROGRAM="$p" timeout 20 "$OCAMLRUN" "$bin/avatar_main.bc" \
       > "$face/$p.ocaml.tsv" 2>/dev/null; then avatar_ok=$((avatar_ok+1))
  else avatar_bad=$((avatar_bad+1)); echo "AVATAR-FAIL $p"; fi
  EFFECT4_FAMILY=corpus EFFECT4_PROGRAM="$p" timeout 20 "$bin/avatar_main.exe" \
    > "$out/corpus_hosts/$p.native.tsv" 2>/dev/null
  EFFECT4_FAMILY=corpus EFFECT4_PROGRAM="$p" timeout 20 "$NODE" "$(effect4_node_path "$bin/avatar_main.bc.js")" \
    > "$out/corpus_hosts/$p.jsoo.tsv" 2>/dev/null
  if ( cd "$here" && EFFECT4_PROGRAM="$p" EFFECT4_CORPUS=corpus/programs.txt EFFECT4_EFFECT_NODE_MODULES="$node_modules" \
         timeout 8 "$NODE" corpus_rc112.mjs ) > "$out/corpus_rc/$p.tsv" 2>"$out/corpus_hosts/$p.err"; then
    rc_ok=$((rc_ok+1))
  elif grep -q "no rc.112 surface" "$out/corpus_hosts/$p.err" 2>/dev/null; then
    rc_skip=$((rc_skip+1)); rm -f "$out/corpus_rc/$p.tsv"
    echo "$p	no-rc112-surface	$(head -1 "$out/corpus_hosts/$p.err")" >> "$out/corpus-skips.txt"
  else
    rc_bad=$((rc_bad+1)); rm -f "$out/corpus_rc/$p.tsv"
    echo "RC112-FAIL $p: $(head -1 "$out/corpus_hosts/$p.err")"
    echo "$p	rc112-did-not-terminate	$(head -1 "$out/corpus_hosts/$p.err")" >> "$out/corpus-skips.txt"
  fi
done
echo "avatar ok=$avatar_ok bad=$avatar_bad ; rc112 ok=$rc_ok skipped=$rc_skip nonterminating=$rc_bad"

echo "=== three OCaml hosts"
hosts_ok=0; hosts_bad=0
for p in $progs; do
  if cmp -s "$face/$p.ocaml.tsv" "$out/corpus_hosts/$p.native.tsv" &&
     cmp -s "$face/$p.ocaml.tsv" "$out/corpus_hosts/$p.jsoo.tsv"; then hosts_ok=$((hosts_ok+1))
  else hosts_bad=$((hosts_bad+1)); echo "hosts $p DISAGREE"; fi
done
echo "hosts agree: $hosts_ok, disagree: $hosts_bad"

echo "=== avatar vs rc.112, every mask"
python3 "$here/compare.py" --masks "$masks" --goldens "$out/corpus_rc" \
  --face "$face" --suffix .ocaml.tsv --reference rc112 \
  --known "$here/corpus/known-divergences.tsv"

compare_status=$?
[ "$compare_status" -eq 0 ] && [ "$avatar_bad" -eq 0 ] && [ "$hosts_bad" -eq 0 ] && [ "$rc_ok" -gt 0 ]
