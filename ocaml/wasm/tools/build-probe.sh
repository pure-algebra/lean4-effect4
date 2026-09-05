#!/usr/bin/env bash
# Build `probe.ml` on four hosts, out of tree, and list the outputs.
#
#   wsl -e bash /mnt/c/.../ocaml/wasm/tools/build-probe.sh [effects-mode] [wasm-only]
#
# effects-mode defaults to `cps` (the mode this machine's node 22 can run; README §6);
# `wasm-only` as a second argument skips the effect4-switch half. The wasm build root is
# `<E4_WASM_BUILD>/probe/wasm-<mode>`, so the modes do not overwrite each other.
# native/bytecode/jsoo come from the pinned `effect4` switch, wasm from `effect4-wasm`;
# each switch gets its own build root, because a shared `_build` across two compilers is a
# full rebuild every time.
set -uo pipefail
here=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
mode=${1:-cps}
only=${2:-}
B=${E4_WASM_BUILD:-$HOME/Dev/e4-wasm}/probe

mk() { # mk <dir> <dune body>
  rm -rf "$1"; mkdir -p "$1"; cp "$here/probe.ml" "$1/"
  printf '(lang dune 3.17)\n(name e4_wasm_probe)\n' > "$1/dune-project"
  printf '%s\n' "$2" > "$1/dune"
}

mk "$B/wasm-$mode" "(executable
 (name probe)
 (modes wasm)
 (wasm_of_ocaml (flags (--effects=$mode)))
 (flags (:standard -w -a)))"
( eval "$(opam env --switch=effect4-wasm --set-switch)" && cd "$B/wasm-$mode" && dune build --root . 2>&1 ) \
  | sed 's/^/[wasm] /'

if [ "$only" != "wasm-only" ]; then
  mk "$B/jsoo" "(executable
 (name probe)
 (modes byte exe js)
 (js_of_ocaml (flags (--enable effects --target-env=nodejs)))
 (flags (:standard -w -a)))"
  ( eval "$(opam env --switch=effect4 --set-switch)" && cd "$B/jsoo" && dune build --root . 2>&1 ) \
    | sed 's/^/[jsoo] /'
fi

echo "=== outputs ==="
find "$B" -path '*/_build/default/*' \( -name 'probe.*' -o -name '*.assets' \) \
  -maxdepth 4 -printf '%y\t%s\t%p\n' | sort -k3
