#!/bin/sh
# Run one OCaml 5 effect-handler witness on three hosts and compare its rows.
#
# Spike O1 of docs/research/2026-09-03-ocaml5-deep-plan.md, ruling 7: "a witness is an
# OCaml source file run as bytecode, as native code where `ocamlopt` exists, and as
# js_of_ocaml output under Node; the row lists must agree with each other and with the
# Lean machine's rows".
#
#   usage: tools/run-witness.sh witnesses/w01-repeated.ml [...]
#
# A witness prints one tab-separated row per line, first cell the kind. The three row
# lists are printed and compared; the exit status is 0 when all three agree.
# Build products go under $O1_BUILD (default: the session scratchpad), never into the
# repository and never into the opam switches.

set -u

OCAMLC=${OCAMLC:-/Users/pooks/.opam/default/bin/ocamlc}
OCAMLOPT=${OCAMLOPT:-/Users/pooks/.opam/default/bin/ocamlopt}
OCAMLRUN=${OCAMLRUN:-/Users/pooks/.opam/default/bin/ocamlrun}
JSOO=${JSOO:-/Users/pooks/Dev/effect4_of_ocaml/_build/toolchains/ocaml5-jsoo-5.7.1/_build/default/vendor/js_of_ocaml-compiler.5.7.1/compiler/bin-js_of_ocaml/js_of_ocaml.exe}
NODE=${NODE:-node}
O1_BUILD=${O1_BUILD:-/private/tmp/claude-501/-Users-pooks-Dev-lean4-effect4/d87ba830-2e63-4750-815f-2679b36f870a/scratchpad/o1}

status=0

run_one() {
  src=$1
  name=$(basename "$src" .ml)
  dir="$O1_BUILD/$name"
  rm -rf "$dir"
  mkdir -p "$dir" || return 1
  cp "$src" "$dir/w.ml"

  echo "=== $name ==="

  # host 1: bytecode, executed by the bytecode interpreter (runtime/interp.c)
  ( cd "$dir" && "$OCAMLC" -w -a -o w.byte w.ml ) >"$dir/byte.build" 2>&1
  if [ $? -ne 0 ]; then
    echo "--- bytecode: BUILD FAILED"; sed -n '1,20p' "$dir/byte.build"; status=1; return 1
  fi
  ( cd "$dir" && "$OCAMLRUN" w.byte ) >"$dir/byte.rows" 2>"$dir/byte.err"
  byte_status=$?

  # host 2: native code (runtime/amd64.S, or arm64.S on this Mac)
  ( cd "$dir" && "$OCAMLOPT" -w -a -o w.native w.ml ) >"$dir/native.build" 2>&1
  if [ $? -ne 0 ]; then
    echo "--- native: BUILD FAILED"; sed -n '1,20p' "$dir/native.build"; status=1; return 1
  fi
  ( cd "$dir" && ./w.native ) >"$dir/native.rows" 2>"$dir/native.err"
  native_status=$?

  # host 3: js_of_ocaml 5.7.1 with the effects CPS transform, under node
  ( cd "$dir" && "$JSOO" compile --enable effects --target-env=nodejs w.byte -o w.js ) \
    >"$dir/jsoo.build" 2>&1
  if [ $? -ne 0 ]; then
    echo "--- jsoo: BUILD FAILED"; sed -n '1,20p' "$dir/jsoo.build"; status=1; return 1
  fi
  ( cd "$dir" && "$NODE" w.js ) >"$dir/jsoo.rows" 2>"$dir/jsoo.err"
  jsoo_status=$?

  for host in byte native jsoo; do
    eval "st=\$${host}_status"
    echo "--- $host (exit $st)"
    sed 's/^/    /' "$dir/$host.rows"
    if [ -s "$dir/$host.err" ]; then
      sed 's/^/    !! /' "$dir/$host.err"
    fi
  done

  if cmp -s "$dir/byte.rows" "$dir/native.rows" && cmp -s "$dir/byte.rows" "$dir/jsoo.rows"; then
    echo "AGREE $name"
  else
    echo "DISAGREE $name"
    diff "$dir/byte.rows" "$dir/native.rows" | sed 's/^/    byte-vs-native /'
    diff "$dir/byte.rows" "$dir/jsoo.rows" | sed 's/^/    byte-vs-jsoo   /'
    status=1
  fi
  echo
}

if [ $# -eq 0 ]; then
  echo "usage: $0 <witness.ml> [...]" >&2
  exit 2
fi

for f in "$@"; do
  run_one "$f"
done

exit $status
