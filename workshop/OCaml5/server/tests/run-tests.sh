#!/usr/bin/env bash
# Build `effect4d` on all three hosts and run every test, printing the counts.
#
#   tests/test_client.py       the protocol, on every request type, every committed golden,
#                              the committed avatar faces and a slice of the corpus, on all
#                              three hosts, plus TCP and a batch session
#   lib_test (byte + native)   the library surface with no wire (deliverable 4, OCaml half)
#   tests/node_module_demo.mjs the js_of_ocaml build `require`d from node (deliverable 4, JS
#                              half) -- the interesting one under `--enable effects`
#
# `W2_AVATAR_REV=<rev>` builds the avatar half from a git revision rather than the working
# tree; see `build-server.sh`.
set -euo pipefail
here=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
server=$(CDPATH= cd -- "$here/.." && pwd)
out=${W2_BUILD:-/private/tmp/claude-501/-Users-pooks-Dev-lean4-effect4/d87ba830-2e63-4750-815f-2679b36f870a/scratchpad/w2}
build="$out/build"
oc=${OCAML5_BIN:-/Users/pooks/.opam/default/bin}
corpus=${W2_CORPUS:-20}

bash "$server/build-server.sh"

echo
echo "=== the library surface, bytecode"
"$oc/ocamlrun" "$build/lib_test.byte"
echo
echo "=== the library surface, native"
"$build/lib_test.native"
echo
echo "=== the js_of_ocaml build, required as a node module"
node "$here/node_module_demo.mjs" "$build/effect4d.js"
echo
echo "=== the protocol, on all three hosts"
python3 "$here/test_client.py" --build "$build" --corpus "$corpus"
