#!/usr/bin/env bash
# Build `effect4d` with dune and run every test on every host this machine can reach.
#
#   tools/dune-test.sh                 # build, then: lib_test (bytecode, native), the node
#                                      # module demo, tests/test_client.py on every host
#   W2_CORPUS=40 tools/dune-test.sh    # a larger slice of the corpus in the test client
#   W2_HOSTS=bytecode,native ...       # only these hosts in the test client
#
# The node host needs a `node`. On a machine with node on the PATH (macOS, Linux) it is
# used as is. Under WSL, where node is not installed but the Windows node is reachable
# through interop, `node.exe` is used and every path handed to it is converted with
# `wslpath -w`; `W2_NODE=/path/to/node.exe` names it when it is not on the PATH.
set -euo pipefail
here=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
root=$(CDPATH= cd -- "$here/.." && pwd)
eval "$(opam env --switch=effect4 --set-switch)"
build="$root/_build/default/server"
status=0

echo "=== dune build (ocaml $(ocamlc -version), dune $(dune --version), js_of_ocaml $(js_of_ocaml --version))"
(cd "$root" && dune build)
for f in effect4d.byte effect4d.native effect4d.js effect4d.bc effect4d.exe effect4d_js.bc.js \
         tests/lib_test.bc tests/lib_test.exe; do
  [ -f "$build/$f" ] || { echo "MISSING $build/$f"; exit 1; }
done
echo "built: $build/{effect4d.byte,effect4d.native,effect4d.js}"

echo
echo "=== the library surface, bytecode"
ocamlrun "$build/tests/lib_test.bc" || status=1
echo
echo "=== the library surface, native"
"$build/tests/lib_test.exe" || status=1

# --- which node, and how it sees a path -------------------------------------------------
node_cmd=""
to_node() { printf '%s' "$1"; }
if [ -n "${W2_NODE:-}" ]; then
  node_cmd=$W2_NODE
elif command -v node > /dev/null 2>&1; then
  node_cmd=node
elif command -v node.exe > /dev/null 2>&1; then
  node_cmd=node.exe
fi
case "$node_cmd" in
  *.exe) to_node() { wslpath -w "$1"; } ;;
esac

echo
if [ -z "$node_cmd" ]; then
  echo "=== no node found: the js_of_ocaml host is not exercised (set W2_NODE)"
  hosts=${W2_HOSTS:-bytecode,native}
else
  echo "=== the js_of_ocaml build, required as a node module ($node_cmd)"
  "$node_cmd" "$(to_node "$here/tests/node_module_demo.mjs")" "$(to_node "$build/effect4d.js")" || status=1
  hosts=${W2_HOSTS:-bytecode,native,jsoo}
fi

echo
echo "=== the protocol, hosts: $hosts"
W2_NODE="$node_cmd" W2_JSOO="$(to_node "$build/effect4d.js")" \
  OCAML5_BIN="$(dirname "$(command -v ocamlrun)")" \
  python3 "$here/tests/test_client.py" --build "$build" --hosts "$hosts" \
    --corpus "${W2_CORPUS:-20}" || status=1

exit $status
