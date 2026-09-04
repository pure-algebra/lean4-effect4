#!/bin/sh
# P6: build and run the OCaml 5 + js_of_ocaml `Await` witnesses.
# OCaml 5.1.1 from the opam `default` switch; the js_of_ocaml 5.7.1 compiler prebuilt by
# effect4_of_ocaml's scripts/build-effects5-toolchain.mjs (no opam mutation, no network).
# `-no-check-prims` lets ocamlc link externals whose only implementation is JavaScript.
set -eu
here=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
out=${P6_BUILD:-/private/tmp/claude-501/-Users-pooks-Dev-lean4-effect4/d87ba830-2e63-4750-815f-2679b36f870a/scratchpad/p6}
oc=${OCAML5_BIN:-/Users/pooks/.opam/default/bin}/ocamlc
jsoo=${JSOO5_BIN:-/Users/pooks/Dev/effect4_of_ocaml/_build/toolchains/ocaml5-jsoo-5.7.1/_build/default/vendor/js_of_ocaml-compiler.5.7.1/compiler/bin-js_of_ocaml/js_of_ocaml.exe}
mkdir -p "$out"
cp "$here/p6_runtime.js" "$here/p6_await.ml" "$here/p6_double.ml" "$out/"
cd "$out"
for m in p6_await p6_double; do
  "$oc" -no-check-prims -o "$m.byte" "$m.ml"
  "$jsoo" compile --enable effects --target-env=nodejs p6_runtime.js "$m.byte" -o "$m.js" 2>/dev/null
  node "$m.js" > "$here/$m.out"
done
# Negative control: the same bytecode without --enable effects.
"$jsoo" compile --target-env=nodejs p6_runtime.js p6_await.byte -o p6_await_noeffects.js 2>/dev/null
node p6_await_noeffects.js > "$here/p6_await-noeffects.out" 2>&1 || true
echo "$out"
