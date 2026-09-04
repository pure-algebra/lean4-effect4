#!/usr/bin/env bash
# Build `effect4d` with dune, in the `effect4` opam switch, from the ocaml
# workspace (the avatar library and the daemon, all three hosts).
#
#   tools/dune-build.sh                  # everything under ocaml
#   tools/dune-build.sh avatar           # the avatar alone
#   tools/dune-build.sh @server/runtest  # build, then run the OCaml library test
#
# Any argument is passed to `dune build`. The build lands in ocaml/_build.
set -euo pipefail
here=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
root=$(CDPATH= cd -- "$here/.." && pwd)
eval "$(opam env --switch=effect4 --set-switch)"
cd "$root"
echo "ocaml $(ocamlc -version), dune $(dune --version), js_of_ocaml $(js_of_ocaml --version), root $root"
dune build "$@"
