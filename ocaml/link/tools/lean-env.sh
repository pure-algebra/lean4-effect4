# tools/lean-env.sh — sourced by the other tools: the Lean and OCaml environment of the
# link/ build, inside WSL. Every E4_* variable can be overridden from the environment.
#
#   E4_LINK_DIR    this directory's parent (ocaml/link/)
#   E4_REPO        the checkout holding lean-toolchain (two levels up: ocaml/link -> repo)
#   E4_BRIDGE_SRC  the Lean half of the link, in the repo's src tree (coordinator's file)
#   E4_LEAN_REPO   the Linux tree whose static libraries Bridge.o links against
#   E4_OUT         where Bridge.c / Bridge.o are compiled (Linux side, fast filesystem)
export PATH="$HOME/.elan/bin:$PATH"
E4_LINK_DIR=${E4_LINK_DIR:-$(CDPATH= cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)}
E4_REPO=${E4_REPO:-$(CDPATH= cd -- "$E4_LINK_DIR/../.." && pwd)}
E4_BRIDGE_SRC=${E4_BRIDGE_SRC:-$E4_REPO/src/OCaml5/Bridge.lean}
E4_LEAN_REPO=${E4_LEAN_REPO:-$HOME/Dev/lean4-effect4-linux}
E4_OUT=${E4_OUT:-$HOME/Dev/e4-link}
# elan resolves the toolchain from the repo's lean-toolchain; outside it, name it explicitly.
[ -f "$E4_REPO/lean-toolchain" ] || { echo "no lean-toolchain under $E4_REPO (E4_REPO wrong?)" >&2; exit 1; }
[ -f "$E4_BRIDGE_SRC" ] || { echo "no Bridge.lean at $E4_BRIDGE_SRC (moved?)" >&2; exit 1; }
export ELAN_TOOLCHAIN="$(cat "$E4_REPO/lean-toolchain")"
eval "$(opam env --switch=effect4 --set-switch)"
E4_LEAN_PREFIX=$(lean --print-prefix)
export LEAN_PATH="$E4_LEAN_REPO/.lake/build/lib/lean:$E4_LEAN_REPO/.lake/packages/effects/.lake/build/lib/lean:$E4_LEAN_REPO/.lake/packages/typescript/.lake/build/lib/lean:$E4_LEAN_REPO/.lake/packages/hash/.lake/build/lib/lean"
export E4_LINK_DIR E4_REPO E4_BRIDGE_SRC E4_LEAN_REPO E4_OUT E4_LEAN_PREFIX

# The four Lean static libraries, in link order (Bridge.o -> Effect4 -> its packages).
e4_lean_libs() {
  local lib
  for lib in "$E4_LEAN_REPO"/.lake/build/lib/lib*_Effect4.a \
             "$E4_LEAN_REPO"/.lake/packages/effects/.lake/build/lib/lib*_Effects.a \
             "$E4_LEAN_REPO"/.lake/packages/typescript/.lake/build/lib/lib*_TypeScript.a \
             "$E4_LEAN_REPO"/.lake/packages/hash/.lake/build/lib/lib*_Hash.a; do
    echo "$lib"
  done
}
