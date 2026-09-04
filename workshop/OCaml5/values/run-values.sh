#!/bin/sh
# O3 (values) witness runner. Compiles every w_*.ml in this directory for four
# hosts and writes one TSV of `key<TAB>value` rows per host into ./out/.
#
#   native   ocamlopt 5.1.1, run directly
#   byte     ocamlc 5.1.1, run under ocamlrun
#   jsoo     js_of_ocaml 5.7.1, --target-env=nodejs, default use-js-string=true
#   jsoo-nostr  the same with --disable use-js-string (the MlBytes representation)
#
# Build products go to a scratch directory, never into the repository.
set -eu

OCAMLC=${OCAMLC:-/Users/pooks/.opam/default/bin/ocamlc}
OCAMLOPT=${OCAMLOPT:-/Users/pooks/.opam/default/bin/ocamlopt}
OCAMLRUN=${OCAMLRUN:-/Users/pooks/.opam/default/bin/ocamlrun}
JSOO=${JSOO:-/Users/pooks/Dev/effect4_of_ocaml/_build/toolchains/ocaml5-jsoo-5.7.1/_build/default/vendor/js_of_ocaml-compiler.5.7.1/compiler/bin-js_of_ocaml/js_of_ocaml.exe}
NODE=${NODE:-node}

HERE=$(cd "$(dirname "$0")" && pwd)
BUILD=${BUILD:-/private/tmp/claude-501/-Users-pooks-Dev-lean4-effect4/d87ba830-2e63-4750-815f-2679b36f870a/scratchpad/o3/build}
OUT="$HERE/out"

mkdir -p "$BUILD" "$OUT"

for src in "$HERE"/w_*.ml; do
  base=$(basename "$src" .ml)
  cp "$src" "$BUILD/$base.ml"
  ( cd "$BUILD"
    "$OCAMLOPT" -w -a -o "$base.native" "$base.ml" >/dev/null
    "$OCAMLC"   -w -a -o "$base.byte"   "$base.ml" >/dev/null
    "$JSOO" compile --target-env=nodejs "$base.byte" -o "$base.js"
    "$JSOO" compile --target-env=nodejs --disable use-js-string "$base.byte" -o "$base.nostr.js"
    ./"$base.native"           > "$OUT/$base.native.tsv"
    "$OCAMLRUN" "$base.byte"   > "$OUT/$base.byte.tsv"
    "$NODE" "$base.js"         > "$OUT/$base.jsoo.tsv"
    "$NODE" "$base.nostr.js"   > "$OUT/$base.jsoo-nostr.tsv" )
  echo "ran $base"
done

# The js_of_ocaml-only representation probe: `p_jsrepr.js` overrides caml_hash
# so that an arbitrary OCaml value can be described from JavaScript. There is no
# native or bytecode row -- on those hosts the answer is the header layout of
# mlvalues.h, already witnessed through Obj by w_block.ml.
cp "$HERE/p_jsrepr.ml" "$HERE/p_jsrepr.js" "$BUILD/"
( cd "$BUILD"
  "$OCAMLC" -w -a -o p_jsrepr.byte p_jsrepr.ml >/dev/null
  "$JSOO" compile --target-env=nodejs p_jsrepr.js p_jsrepr.byte -o p_jsrepr.out.js 2>/dev/null
  "$JSOO" compile --target-env=nodejs --disable use-js-string p_jsrepr.js p_jsrepr.byte \
      -o p_jsrepr.nostr.js 2>/dev/null
  "$NODE" p_jsrepr.out.js   > "$OUT/p_jsrepr.jsoo.tsv"
  "$NODE" p_jsrepr.nostr.js > "$OUT/p_jsrepr.jsoo-nostr.tsv" )
echo "ran p_jsrepr (jsoo only)"
paste "$OUT/p_jsrepr.jsoo.tsv" "$OUT/p_jsrepr.jsoo-nostr.tsv" \
| awk -F'\t' 'BEGIN{printf "key\tjsoo\tjsoo-nostr\n"} {printf "%s\t%s\t%s\n", $1, $2, $4}' \
  > "$OUT/p_jsrepr.tsv"

# The comparison report: one line per key whose four hosts do not all agree.
{
  printf 'witness\tkey\tnative\tbyte\tjsoo\tjsoo-nostr\n'
  for src in "$HERE"/w_*.ml; do
    base=$(basename "$src" .ml)
    paste "$OUT/$base.native.tsv" "$OUT/$base.byte.tsv" \
          "$OUT/$base.jsoo.tsv" "$OUT/$base.jsoo-nostr.tsv" \
    | awk -F'\t' -v w="$base" '{ printf "%s\t%s\t%s\t%s\t%s\t%s\n", w, $1, $2, $4, $6, $8 }'
  done
} > "$OUT/all.tsv"

awk -F'\t' 'NR==1 || !($3==$4 && $4==$5 && $5==$6)' "$OUT/all.tsv" > "$OUT/differ.tsv"
echo "rows: $(( $(wc -l < "$OUT/all.tsv") - 1 )), differing: $(( $(wc -l < "$OUT/differ.tsv") - 1 ))"

# Finally, check that Value.lean transcribed the rows it claims to have transcribed.
if command -v python3 >/dev/null 2>&1; then
  ( cd "$HERE/../../.." && python3 workshop/OCaml5/values/check-transcription.py )
fi
