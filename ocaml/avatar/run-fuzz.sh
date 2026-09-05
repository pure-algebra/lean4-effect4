#!/usr/bin/env bash
# Round five, deliverable 2: run P5's generated corpus
# (`ocaml/probes/fuzz/corpus/`, spike P5 round four) on both faces.
# P5 renders each random program to an OCaml fixture and a TypeScript one; the OCaml half is
# linked into `avatar-fuzz.byte` as the `fuzz` family, the TypeScript half runs over rc.112
# through `fuzz_rc112_tail.ts`. Neither P5's files nor anything under `harness/` is edited.
set -uo pipefail
here=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
# <repo>/ocaml/avatar -> <repo>. The estate lived under `workshop/OCaml5/` until 2026-09-04.
repo=$(CDPATH= cd -- "$here/../.." && pwd)
 . "$repo/ocaml/tools/lib/toolchain.sh"
effect4_toolchain || exit 1
fuzz="$repo/ocaml/probes/fuzz/corpus"
masks="$repo/ocaml/server/generated/traces/masks.tsv"
[ -f "$fuzz/index.tsv" ] || { echo "SKIP no P5 corpus at $fuzz"; exit 0; }
(cd "$repo/ocaml" && dune build avatar/effect4_avatar.cma) || exit 1
bin="$repo/ocaml/_build/default/avatar"
scratch_parent=${A0_BUILD:-${TMPDIR:-/tmp}}
mkdir -p "$scratch_parent"
out=$(mktemp -d "$scratch_parent/effect4-fuzz.XXXXXX")
trap 'rm -rf -- "$out"' EXIT
mkdir -p "$out/fuzzbuild" "$out/fuzzts" "$out/fuzz_rc" "$here/out/fuzz"
cp "$fuzz/corpus_fixture.ml" "$here/fuzz_register.ml" "$here/avatar_main.ml" "$out/fuzzbuild/"
# Link dune's library: the module inventory and dependency order have one owner.
( cd "$out/fuzzbuild" && "$OCAMLC" -I "$bin/.effect4_avatar.objs/byte" -linkall \
    "$bin/effect4_avatar.cma" corpus_fixture.ml fuzz_register.ml avatar_main.ml \
    -o avatar-fuzz.byte ) || exit 1
if [ "${1:-}" = --build-only ]; then echo 'PASS fuzz driver links the dune avatar library'; exit 0; fi
cp "$fuzz/corpus-fixture.ts" "$here/fuzz_rc112_tail.ts" "$out/fuzzts/"
ln -sfn "${EFFECT4_EFFECT_NODE_MODULES:-$repo/ts/eff/node_modules}" \
  "$out/fuzzts/node_modules"
echo '{"type":"module"}' > "$out/fuzzts/package.json"

a_ok=0; a_bad=0; r_ok=0; r_bad=0
for p in $(awk -F'\t' 'NR>1{print $1}' "$fuzz/index.tsv"); do
  tape=$(cat "$fuzz/$p/tape" 2>/dev/null)
  if ( cd "$out/fuzzbuild" && EFFECT4_FAMILY=fuzz EFFECT4_PROGRAM="$p" EFFECT4_TAPE="$tape" \
         timeout 15 "$OCAMLRUN" ./avatar-fuzz.byte ) > "$here/out/fuzz/$p.ocaml.tsv" 2>/dev/null
  then a_ok=$((a_ok+1)); else a_bad=$((a_bad+1)); rm -f "$here/out/fuzz/$p.ocaml.tsv"; fi
  if ( cd "$out/fuzzts" && EFFECT4_PROGRAM="$p" EFFECT4_TAPE="$tape" \
         timeout 15 "$NODE" --experimental-strip-types --no-warnings fuzz_rc112_tail.ts ) \
       > "$out/fuzz_rc/$p.tsv" 2>/dev/null
  then r_ok=$((r_ok+1)); else r_bad=$((r_bad+1)); rm -f "$out/fuzz_rc/$p.tsv"; fi
done
echo "fuzz: avatar ok=$a_ok bad=$a_bad ; rc112 ok=$r_ok bad=$r_bad"
python3 "$here/compare.py" --masks "$masks" --goldens "$out/fuzz_rc" \
  --face "$here/out/fuzz" --suffix .ocaml.tsv --reference rc112 \
  --known "$here/corpus/known-fuzz-divergences.tsv"
