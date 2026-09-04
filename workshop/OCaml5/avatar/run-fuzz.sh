#!/usr/bin/env bash
# Round five, deliverable 2: run P5's generated corpus
# (`workshop/OCaml5/fuzz/corpus/`, spike P5 round four) on both faces.
# P5 renders each random program to an OCaml fixture and a TypeScript one; the OCaml half is
# linked into `avatar-fuzz.byte` as the `fuzz` family, the TypeScript half runs over rc.112
# through `fuzz_rc112_tail.ts`. Neither P5's files nor anything under `harness/` is edited.
set -uo pipefail
here=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
repo=$(CDPATH= cd -- "$here/../../.." && pwd)
out=${A0_BUILD:-/private/tmp/claude-501/-Users-pooks-Dev-lean4-effect4/d87ba830-2e63-4750-815f-2679b36f870a/scratchpad/a0}
oc=${OCAML5_BIN:-/Users/pooks/.opam/default/bin}
fuzz="$repo/workshop/OCaml5/fuzz/corpus"
masks="$repo/generated/traces/masks.tsv"
[ -f "$fuzz/index.tsv" ] || { echo "SKIP no P5 corpus at $fuzz"; exit 0; }

rm -rf "$out/fuzzbuild" "$out/fuzzts" "$out/fuzz_rc" "$here/out/fuzz"
mkdir -p "$out/fuzzbuild" "$out/fuzzts" "$out/fuzz_rc" "$here/out/fuzz"
cp "$here"/*.ml "$out/fuzzbuild/"; cp "$out/build/corpus_data.ml" "$out/fuzzbuild/"
cp "$fuzz/corpus_fixture.ml" "$out/fuzzbuild/"
( cd "$out/fuzzbuild" && "$oc/ocamlc" -o avatar-fuzz.byte deep_fibers.ml avatar_trace.ml \
    fibers_fixture.ml store_fixtures.ml extra_fixture.ml corpus_dsl.ml corpus_data.ml \
    corpus_run.ml corpus_fixture.ml fuzz_register.ml avatar_main.ml ) || exit 1
cp "$fuzz/corpus-fixture.ts" "$here/fuzz_rc112_tail.ts" "$out/fuzzts/"
ln -sfn "${EFFECT4_EFFECT_NODE_MODULES:-$HOME/Dev/foldlab/library/effects/node_modules}" \
  "$out/fuzzts/node_modules"
echo '{"type":"module"}' > "$out/fuzzts/package.json"

a_ok=0; a_bad=0; r_ok=0; r_bad=0
for p in $(awk -F'\t' 'NR>1{print $1}' "$fuzz/index.tsv"); do
  tape=$(cat "$fuzz/$p/tape" 2>/dev/null)
  if ( cd "$out/fuzzbuild" && EFFECT4_FAMILY=fuzz EFFECT4_PROGRAM="$p" EFFECT4_TAPE="$tape" \
         timeout 15 "$oc/ocamlrun" ./avatar-fuzz.byte ) > "$here/out/fuzz/$p.ocaml.tsv" 2>/dev/null
  then a_ok=$((a_ok+1)); else a_bad=$((a_bad+1)); rm -f "$here/out/fuzz/$p.ocaml.tsv"; fi
  if ( cd "$out/fuzzts" && EFFECT4_PROGRAM="$p" EFFECT4_TAPE="$tape" \
         timeout 15 node --experimental-strip-types --no-warnings fuzz_rc112_tail.ts ) \
       > "$out/fuzz_rc/$p.tsv" 2>/dev/null
  then r_ok=$((r_ok+1)); else r_bad=$((r_bad+1)); rm -f "$out/fuzz_rc/$p.tsv"; fi
done
echo "fuzz: avatar ok=$a_ok bad=$a_bad ; rc112 ok=$r_ok bad=$r_bad"
python3 "$here/compare.py" --masks "$masks" --goldens "$out/fuzz_rc" \
  --face "$here/out/fuzz" --suffix .ocaml.tsv --reference rc112 \
  --known "$here/corpus/known-fuzz-divergences.tsv"
