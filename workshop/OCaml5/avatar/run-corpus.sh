#!/usr/bin/env bash
# Round five: run every corpus program on both faces and compare.
# rc.112 is the reference wherever no Lean golden exists, which is every corpus program.
set -uo pipefail
here=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
repo=$(CDPATH= cd -- "$here/../../.." && pwd)
out=${A0_BUILD:-/private/tmp/claude-501/-Users-pooks-Dev-lean4-effect4/d87ba830-2e63-4750-815f-2679b36f870a/scratchpad/a0}
oc=${OCAML5_BIN:-/Users/pooks/.opam/default/bin}
masks="$repo/generated/traces/masks.tsv"
rm -rf "$out/corpus_rc" "$out/corpus_hosts"
mkdir -p "$out/corpus_rc" "$out/corpus_hosts" "$here/out/corpus"
cd "$out/build"

progs=$(grep '^prog ' "$here/corpus/programs.txt" | awk '{print $2}')
avatar_ok=0; avatar_bad=0; rc_ok=0; rc_skip=0; rc_bad=0
: > "$out/corpus-skips.txt"
for p in $progs; do
  if EFFECT4_FAMILY=corpus EFFECT4_PROGRAM="$p" timeout 20 "$oc/ocamlrun" ./avatar.byte \
       > "$here/out/corpus/$p.ocaml.tsv" 2>/dev/null; then avatar_ok=$((avatar_ok+1))
  else avatar_bad=$((avatar_bad+1)); echo "AVATAR-FAIL $p"; fi
  EFFECT4_FAMILY=corpus EFFECT4_PROGRAM="$p" timeout 20 ./avatar.native \
    > "$out/corpus_hosts/$p.native.tsv" 2>/dev/null
  EFFECT4_FAMILY=corpus EFFECT4_PROGRAM="$p" timeout 20 node avatar.js \
    > "$out/corpus_hosts/$p.jsoo.tsv" 2>/dev/null
  if ( cd "$here" && EFFECT4_PROGRAM="$p" EFFECT4_CORPUS=corpus/programs.txt \
         timeout 8 node corpus_rc112.mjs ) > "$out/corpus_rc/$p.tsv" 2>"$out/corpus_hosts/$p.err"; then
    rc_ok=$((rc_ok+1))
  elif grep -q "no rc.112 surface" "$out/corpus_hosts/$p.err" 2>/dev/null; then
    rc_skip=$((rc_skip+1)); rm -f "$out/corpus_rc/$p.tsv"
    echo "$p	no-rc112-surface	$(head -1 "$out/corpus_hosts/$p.err")" >> "$out/corpus-skips.txt"
  else
    rc_bad=$((rc_bad+1)); rm -f "$out/corpus_rc/$p.tsv"
    echo "$p	rc112-did-not-terminate	$(head -1 "$out/corpus_hosts/$p.err")" >> "$out/corpus-skips.txt"
  fi
done
echo "avatar ok=$avatar_ok bad=$avatar_bad ; rc112 ok=$rc_ok skipped=$rc_skip nonterminating=$rc_bad"

echo "=== three OCaml hosts"
hosts_ok=0; hosts_bad=0
for p in $progs; do
  if cmp -s "$here/out/corpus/$p.ocaml.tsv" "$out/corpus_hosts/$p.native.tsv" &&
     cmp -s "$here/out/corpus/$p.ocaml.tsv" "$out/corpus_hosts/$p.jsoo.tsv"; then hosts_ok=$((hosts_ok+1))
  else hosts_bad=$((hosts_bad+1)); echo "hosts $p DISAGREE"; fi
done
echo "hosts agree: $hosts_ok, disagree: $hosts_bad"

echo "=== avatar vs rc.112, every mask"
python3 "$here/compare.py" --masks "$masks" --goldens "$out/corpus_rc" \
  --face "$here/out/corpus" --suffix .ocaml.tsv --reference rc112 \
  --known "$here/corpus/known-divergences.tsv"
