#!/usr/bin/env bash
# tools/build.sh — everything: Bridge.o from Bridge.lean (when it changed), the two flag
# files, then `dune build --root .` in link/.
#
#   bash tools/build.sh                 # build the library, the three drivers and the test
#   bash tools/build.sh --test          # ...and run the property tests
#   bash tools/build.sh --force-bridge  # recompile Bridge.o even if Bridge.lean is unchanged
#
# E4_BUILD_DIR moves dune's build directory (default: link/_build).
set -euo pipefail
here=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
force=""
run_tests=0
for a in "$@"; do
  case "$a" in
    --force-bridge) force=--force ;;
    --test) run_tests=1 ;;
    *) echo "unknown option: $a" >&2; exit 2 ;;
  esac
done
bash "$here/compile-bridge.sh" $force
bash "$here/lean-flags.sh"
source "$here/lean-env.sh"
cd "$E4_LINK_DIR"
build_dir=${E4_BUILD_DIR:-$E4_LINK_DIR/_build}
echo "--- dune build --root . (ocaml $(ocamlfind ocamlopt -version), dune $(dune --version), build dir $build_dir)"
dune build --root . --build-dir "$build_dir" 2>&1
for f in e4_demo.exe e4_bench.exe e4_probe.exe e4_test.exe; do
  [ -f "$build_dir/default/$f" ] || { echo "MISSING $build_dir/default/$f"; exit 1; }
done
echo "--- built: $build_dir/default/{e4_demo,e4_bench,e4_probe,e4_test}.exe"
if [ "$run_tests" = 1 ]; then
  echo "--- dune test"
  dune test --root . --build-dir "$build_dir" --force 2>&1
fi
