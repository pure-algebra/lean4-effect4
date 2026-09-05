#!/bin/sh
# P6: build and run the OCaml 5 + js_of_ocaml `Await` witnesses.
# OCaml 5.1.1 from the opam `default` switch; the js_of_ocaml 5.7.1 compiler prebuilt by
# effect4_of_ocaml's scripts/build-effects5-toolchain.mjs (no opam mutation, no network).
# `-no-check-prims` lets ocamlc link externals whose only implementation is JavaScript.
set -eu
here=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
out=${P6_BUILD:-/private/tmp/claude-501/-Users-pooks-Dev-lean4-effect4/d87ba830-2e63-4750-815f-2679b36f870a/scratchpad/p6}
. "$here/../../tools/lib/toolchain.sh"
effect4_toolchain || exit 1
oc=$OCAMLC
jsoo=$JSOO
mkdir -p "$out"
cp "$here/p6_runtime.js" "$here/p6_await.ml" "$here/p6_double.ml" "$out/"
cd "$out"
for m in p6_await p6_double; do
  "$oc" -no-check-prims -o "$m.byte" "$m.ml"
  "$jsoo" compile --enable effects --target-env=nodejs p6_runtime.js "$m.byte" -o "$m.js" 2>/dev/null
  "$NODE" "$m.js" > "$here/$m.out"
done
# Negative control: the same bytecode without --enable effects.
"$jsoo" compile --target-env=nodejs p6_runtime.js p6_await.byte -o p6_await_noeffects.js 2>/dev/null
"$NODE" p6_await_noeffects.js > "$here/p6_await-noeffects.out" 2>&1 || true
echo "$out"
