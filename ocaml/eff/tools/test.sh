#!/usr/bin/env bash
# The eff area in the repository's one dune workspace (effect4 opam switch).
set -euo pipefail
eval "$(opam env --switch=effect4 --set-switch)"
cd "$(dirname "$0")/../.."
dune build eff
dune test eff
