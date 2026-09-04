#!/usr/bin/env bash
# Build `effect4d` on all three hosts: bytecode, native, and js_of_ocaml `--enable effects`
# under node.
#
# The daemon links the avatar read-only. Seat W1 owns `ocaml/avatar/*`; this script
# copies those sources into the build directory beside the server's own and compiles one
# module list, in the same order `avatar/build-avatar.sh` uses for the avatar half. Nothing
# under `avatar/`, `harness/`, `scripts/` or `generated/` is written.
#
# There is no dune-project. The avatar is built by a plain `ocamlc <files>` list because the
# same bytecode has to be handed to a js_of_ocaml compiler that is not an opam package, and
# because `-no-check-prims` is needed to link the four JavaScript externals of
# `server_runtime.js` (the pattern of `ocaml/probes/promise/build-ocaml.sh`). A dune build
# would have to reproduce all of that through rules; a 90-line script says it once.
#
# Five modules are generated rather than written, so that nothing in the daemon's answers is
# a hand-made copy of something the estate already states:
#
#   corpus_data.ml         the corpus text, compiled in (there is no file to open under jsoo)
#   e4d_masks_data.ml      generated/traces/masks.tsv and the corpus's classified divergences
#   e4d_families_data.ml   the five families' OpSpec rows, out of the generated harness fixtures
#   e4d_armmap.ml          the avatar's own `effc` dispatch table, arm row names and citations,
#                          resolved against src/Effect4/Machine/*.lean
#   e4d_pins.ml            the rc.112 pin, the per-file digests, the build note
#
# `W2_AVATAR_REV` picks which avatar the daemon is built against:
#
#   unset      the working tree, and on a compile failure a second attempt at HEAD, with a
#              loud message saying which one was used. Seat W1 is porting the remaining Deep
#              modules into `avatar/deep_*.ml` and the tree can be mid-port; the daemon has to
#              stay buildable while that lands, and a build that silently used yesterday's
#              avatar would be worse than one that says so.
#   <rev>      that git revision, and no fallback.
#   tree       the working tree, and no fallback.
#
# SUPERSEDED by dune since 2026-09-04 (`server/dune`, BUILD-DUNE.md): build with
# `tools/dune-build.sh`, or `cd ocaml && dune build server`. Kept as the reference for what
# the shell build did. The toolchain now comes from the `effect4` opam switch on the PATH
# rather than a Mac prefix.
set -euo pipefail
here=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
# <repo>/ocaml/server -> <repo>. The estate lived under `workshop/OCaml5/` until 2026-09-04.
repo=$(CDPATH= cd -- "$here/../.." && pwd)
avatar="$here/../avatar"
out=${W2_BUILD:-${TMPDIR:-/tmp}/effect4-server-shell-build}
oc=${OCAML5_BIN:-$(dirname "$(command -v ocamlc || echo /nonexistent/ocamlc)")}
jsoo=${JSOO5_BIN:-$(command -v js_of_ocaml || echo /nonexistent/js_of_ocaml)}
traces="$repo/generated/traces"

build="$out/build"
mkdir -p "$build"

# stage_and_build <avatar revision, or the empty string for the working tree>
stage_and_build() {
  local W2_AVATAR_REV="$1"
  rm -f "$build"/*.ml "$build"/*.cm* "$build"/*.o "$build"/*.cmi

  # The avatar half. Seat W1 edits `avatar/*.ml` concurrently, so the working tree can be
  # mid-port when this runs. `W2_AVATAR_REV` builds against a git revision instead, which is
  # how the daemon is kept buildable while a port is in flight; unset, it uses the working
  # tree, which is what a checkpoint build wants.
  # The module list and its ORDER are the avatar's own: they are read out of the `modules=`
  # line of `avatar/build-avatar.sh`, minus the entry point and minus `corpus_data.ml`, which
  # is generated below. Reading them means a module seat W1 adds -- `deep_stores.ml`,
  # `deep_layer.ml`, and whatever the rest of the port brings -- is compiled in the order the
  # avatar declares, with no list here to fall out of date. Alphabetical order would already
  # be wrong: `deep_stores.ml` must precede `deep_layer.ml`.
  if [ -n "${W2_AVATAR_REV:-}" ]; then
  avatar_build=$(git -C "$repo" show "${W2_AVATAR_REV}:ocaml/avatar/build-avatar.sh")
  else
  avatar_build=$(cat "$avatar/build-avatar.sh")
  fi
  avatar_sources=$(printf '%s\n' "$avatar_build" | sed -n 's/^modules="\(.*\)"$/\1/p' \
    | tr ' ' '\n' | grep -v '^avatar_main\.ml$' | grep -v '^corpus_data\.ml$' | grep . | tr '\n' ' ')
  [ -n "$avatar_sources" ] || { echo "no modules= line in build-avatar.sh" >&2; return 1; }
  if [ -n "${W2_AVATAR_REV:-}" ]; then
  echo "=== avatar from ${W2_AVATAR_REV} (not the working tree)"
  for module in $avatar_sources; do
    git -C "$repo" show "${W2_AVATAR_REV}:ocaml/avatar/$module" > "$build/$module"
  done
  git -C "$repo" show "${W2_AVATAR_REV}:ocaml/avatar/corpus/programs.txt" \
    > "$build/programs.txt"
  corpus_text="$build/programs.txt"
  else
  for module in $avatar_sources; do cp "$avatar/$module" "$build/$module"; done
  corpus_text="$avatar/corpus/programs.txt"
  fi
  extra_avatar=""
  cp "$here"/*.ml "$build/"
  cp "$here/server_runtime.js" "$build/"
  cp "$here"/tests/*.ml "$build/" 2>/dev/null || true

  # --- generated: the corpus text ----------------------------------------------
  python3 - "$corpus_text" > "$build/corpus_data.ml" <<'PY'
import sys
print("(* Generated by build-server.sh from avatar/corpus/programs.txt. Do not edit. *)")
print("let text = {corpus|" + open(sys.argv[1]).read() + "|corpus}")
PY

  # --- generated: the mask table and the classified divergences ----------------
  python3 - "$traces/masks.tsv" "$avatar/corpus/known-divergences.tsv" \
  > "$build/e4d_masks_data.ml" <<'PY'
import sys
print("(* Generated by build-server.sh. Do not edit. *)")
print("(* generated/traces/masks.tsv *)")
print("let text = {masks|" + open(sys.argv[1]).read() + "|masks}")
print("(* ocaml/avatar/corpus/known-divergences.tsv *)")
print("let known_text = {known|" + open(sys.argv[2]).read() + "|known}")
PY

  # --- generated: the families, the arm map, the pins --------------------------
  python3 "$here/tools/gen_families.py" "$repo/harness/trace" > "$build/e4d_families_data.ml"
  # Every avatar module the daemon links, in the avatar's own order, so an arm that moves
  # from one module to another is still found.
  # Every Machine module, comma separated: the store arms cite `Stores.lean` and the layer
  # arms `Layer.lean` since seat W1's port, and a citation has to resolve wherever it points.
  # (`Effect4/Deep/*.lean` moved to `src/Effect4/Machine/*.lean` in "Prod cleanup 3".)
  deep_leans=$(printf '%s,' "$repo"/src/Effect4/Machine/*.lean | sed 's/,$//')
  python3 "$here/tools/gen_armmap.py" "$deep_leans" \
    $(for m in $avatar_sources; do printf '%s ' "$build/$m"; done) > "$build/e4d_armmap.ml"
  python3 "$here/tools/gen_pins.py" "$repo" "$build" "$avatar_sources$extra_avatar" \
  "$corpus_text" "$here" "$traces/masks.tsv" \
  "$("$oc/ocamlc" -version)" "$(node --version)" > "$build/e4d_pins.ml"

  cd "$build"

  # `corpus_data.ml` is generated, and goes where `build-avatar.sh` puts it: immediately
  # before `corpus_run.ml`, which reads it.
  avatar_modules=$(printf '%s ' $avatar_sources | sed 's/corpus_run\.ml/corpus_data.ml corpus_run.ml/')
  server_modules="e4d_json.ml e4d_wire.ml e4d_protocol.ml e4d_stream.ml e4d_alphabet.ml \
  e4d_server_loop.ml e4d_masks_data.ml e4d_families_data.ml e4d_armmap.ml \
  e4d_pins.ml e4d_reset.ml e4d_catalog.ml e4d_snapshot.ml effect4_daemon.ml"
  modules="$avatar_modules $server_modules"

  # `set -e` is suspended inside a function called as an `if` condition, so every compile
  # propagates its own failure: otherwise the fallback below would never fire.
  echo "=== bytecode"
  "$oc/ocamlc" -I +unix unix.cma -o effect4d.byte $modules effect4d.ml || return 1
  echo "=== native"
  "$oc/ocamlopt" -I +unix unix.cmxa -o effect4d.native $modules effect4d.ml || return 1
  echo "=== js_of_ocaml --enable effects"
  "$oc/ocamlc" -no-check-prims -o effect4d_js.byte $modules effect4d_js.ml || return 1
  "$jsoo" compile --enable effects --target-env=nodejs server_runtime.js effect4d_js.byte \
    -o effect4d.js 2>/dev/null || return 1

  echo "=== the OCaml library test (deliverable 4, the OCaml half)"
  if [ -f lib_test.ml ]; then
    "$oc/ocamlc" -o lib_test.byte $modules lib_test.ml || return 1
    "$oc/ocamlopt" -o lib_test.native $modules lib_test.ml || return 1
  fi

  echo "built in $build:"
  ls -1 effect4d.byte effect4d.native effect4d.js 2>/dev/null
}

case "${W2_AVATAR_REV:-}" in
  "")
    if stage_and_build "" > "$build/tree-build.log" 2>&1; then
      cat "$build/tree-build.log"
      echo "=== avatar: the working tree"
    else
      echo "=== avatar: the working tree DID NOT COMPILE, retrying at HEAD. The failure:" >&2
      grep -E "^(File|Error)" "$build/tree-build.log" | head -6 >&2
      stage_and_build HEAD
      echo "=== avatar: HEAD (the working tree did not compile; see $build/tree-build.log)" >&2
    fi ;;
  tree) stage_and_build "" ;;
  *)    stage_and_build "${W2_AVATAR_REV}" ;;
esac
