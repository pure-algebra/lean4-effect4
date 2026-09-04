#!/usr/bin/env bash
# Seat F3: render the named `Fibers.lean` defs through the syntax-level transpiler
# (`transpile-deep.lean`) and print the OCaml, or the residue table with `--residue`.
#
#   transpile-deep.sh insert enqueue drain arm disarm countdownWalk          # OCaml text
#   transpile-deep.sh --residue insert enqueue …                             # unknown forms
#   transpile-deep.sh stepDecision.fire stepDecision.flushAll               # a `where`-local
#
# Same olean fallback as `render-deep.sh`: `lake env` dies on a checkout without the pinned
# lean4-typescript revision, so `lean` runs over the built libs directly.
set -euo pipefail
here=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
repo=$(CDPATH= cd -- "$here/../../.." && pwd)
lean_run() {
  if ( cd "$repo" && lake env true ) > /dev/null 2>&1; then
    ( cd "$repo" && lake env lean --run workshop/OCaml5/avatar/transpile-deep.lean "$@" )
  else
    ( cd "$repo" && \
      LEAN_PATH=.lake/build/lib/lean:.lake/packages/effects/.lake/build/lib/lean:.lake/packages/hash/.lake/build/lib/lean:.lake/packages/typescript/.lake/build/lib/lean \
      lean --run workshop/OCaml5/avatar/transpile-deep.lean "$@" )
  fi
}
lean_run "$@"
