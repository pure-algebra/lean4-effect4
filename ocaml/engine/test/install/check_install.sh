#!/usr/bin/env bash
# check_install.sh -- the install metadata, checked from a project outside ocaml/ (plan E1,
# docs/research/2026-10-18-slices/README.md §4.5 and §9 ruling 4: names first, no release).
#
# What it is: the outside-consumer check. ./dune runs it under `dune test engine`, so
# `make check-ocaml` runs it. It installs every package of the workspace into a scratch prefix
# with `dune install`, copies consumer/ beside the prefix, outside ocaml/, and builds the copy as
# its own dune root. Every nested dune runs in a cleared environment: PATH, HOME, TMPDIR, and
# OCAMLPATH set to the prefix alone, so the copy sees the installed packages and the opam switch,
# never the workspace.
# The consumer's fixtures are directories: each `ok*/` builds `ok.exe`, which runs on
# consumer/program.json and must print its `ok.expected`; each `red*/` builds `red.exe`, which
# must fail with the line of its `red.expected`. A new control is a new directory.
# Usage: check_install.sh CONTEXT_ROOT CONSUMER INSTALLED_EXPECTED
#   CONTEXT_ROOT        the build context's root (%{workspace_root}: <build dir>/default)
#   CONSUMER            the outside project's sources (consumer/, data in the workspace)
#   INSTALLED_EXPECTED  what the prefix must hold, sorted: `bin/NAME` per executable, `package NAME`
#                       per lib/ directory, `library NAME` per library a dune-package declares
# Depends on: dune, the workspace's install alias (./dune makes it a dependency), and
#   DUNE_SOURCEROOT, which dune sets for every action.
#
# Behaviours:
#   I1 `dune install` fills the prefix with exactly INSTALLED_EXPECTED: one executable, bin/eff,
#      eight packages, and their ten libraries, the facade effect4_gen.effect4 and the
#      package-private closure effect4_gen.__private__.effect4_closure included, so no test
#      library installs under any name.                                               tested
#   I2 Each ok fixture builds against the prefix alone and prints its ok.expected. consumer/ok
#      links the installed kit, then checks and runs consumer/program.json. consumer/ok_facade
#      names R6.2's frozen paths through the public facade and runs one program.      tested
#   I3 The installed eff prints consumer/ok's two lines for `eff check` and `eff run`. tested
#   I4 Red controls: each red fixture's build fails, and its output holds the line of its
#      red.expected. consumer/red_test_library names the test library
#      effect4_disk_test_support. Eight are the facade's (R6.2): a coverage root named
#      through the facade and through Api_gen, a linkage root named through the facade, and each
#      sealed package (Built, Prepared, Checked, the tool Session, Memo) built or updated through
#      a facade alias. Three are the test lanes' (C5): the lanes' unit, effect4_lanes, linked
#      by name; a lane's facade, Todo_gen, named; and a lane's root named through Api_gen. Two
#      are the closure's (D1): a value the closure exports to the lanes, named through its
#      module Closure_gen, with the facade linked and with the closure linked by its private
#      name.                                                                           tested
#   The prefix and the copy share one temporary directory, removed on every exit.
#   Evidence: host-only, a finite run on this machine's switch; no theorem reaches it.
set -euo pipefail

if [ "$#" -ne 3 ]; then echo "usage: check_install.sh CONTEXT_ROOT CONSUMER INSTALLED_EXPECTED" >&2; exit 2; fi
context=$(cd "$1" && pwd)
build_dir=$(dirname "$context")
consumer=$(cd "$2" && pwd)
installed_expected=$(cd "$(dirname "$3")" && pwd)/$(basename "$3")
root=${DUNE_SOURCEROOT:?"check_install.sh runs as a dune action, which sets DUNE_SOURCEROOT"}

work=$(mktemp -d "${TMPDIR:-/tmp}/effect4-install.XXXXXX")
trap 'rm -rf "$work"' EXIT
prefix=$work/prefix

fail() {
  echo "FAIL $1"
  shift
  for log in "$@"; do echo "--- $log"; cat "$log"; done
  exit 1
}

# A cleared environment: dune exports INSIDE_DUNE, OCAMLPATH and DUNE_* to its actions, and a
# nested dune must see none of them.
clean() { env -i PATH="$PATH" HOME="$HOME" TMPDIR="${TMPDIR:-/tmp}" "$@"; }

# I1
clean dune install --root "$root" --build-dir "$build_dir" --prefix "$prefix" > "$work/install.log" 2>&1 \
  || fail "I1 dune install into the scratch prefix" "$work/install.log"
(cd "$prefix" && {
  for path in bin/*; do echo "$path"; done
  for path in lib/*; do echo "package ${path#lib/}"; done
  for path in lib/*/dune-package; do
    # A dune-package declares each library as `(library` with ` (name NAME)` on the next line.
    grep -A1 '^(library' "$path" | sed -n 's/^ (name \(.*\))$/library \1/p'
  done
}) | LC_ALL=C sort > "$work/installed"
diff "$installed_expected" "$work/installed" > "$work/installed.diff" \
  || fail "I1 the prefix holds exactly installed.expected" "$work/installed.diff"
echo "PASS I1 the prefix holds the $(grep -c '^bin/' "$work/installed") executable, $(grep -c '^package ' "$work/installed") packages and $(grep -c '^library ' "$work/installed") libraries of installed.expected"

cp -R "$consumer" "$work/consumer"
chmod -R u+w "$work/consumer"
outside() { clean OCAMLPATH="$prefix/lib" dune build --root "$work/consumer" --cache=disabled "$@"; }

# I2
oks=0
for dir in "$work"/consumer/ok*/; do
  name=$(basename "$dir")
  outside "./$name/ok.exe" > "$work/$name-build.log" 2>&1 \
    || fail "I2 $name builds against the prefix alone" "$work/$name-build.log"
  "$work/consumer/_build/default/$name/ok.exe" "$work/consumer/program.json" > "$work/$name.out" 2> "$work/$name.err" \
    || fail "I2 $name/ok.exe answers" "$work/$name.err"
  diff "$dir/ok.expected" "$work/$name.out" > "$work/$name.diff" || fail "I2 $name prints its ok.expected" "$work/$name.diff"
  echo "PASS I2 $name builds against the installed packages alone and prints its ok.expected"
  oks=$((oks + 1))
done
[ "$oks" -ge 1 ] || fail "I2 the consumer has an ok fixture"

# I3
{ "$prefix/bin/eff" check "$work/consumer/program.json"; "$prefix/bin/eff" run "$work/consumer/program.json"; } \
  > "$work/eff.out" 2> "$work/eff.err" || fail "I3 the installed eff answers" "$work/eff.err"
diff "$consumer/ok/ok.expected" "$work/eff.out" > "$work/eff.diff" || fail "I3 the installed eff prints ok/ok.expected" "$work/eff.diff"
echo "PASS I3 the installed eff answers check and run as the outside kit consumer does"

# I4, the red controls
reds=0
for dir in "$work"/consumer/red*/; do
  name=$(basename "$dir")
  line=$(cat "$dir/red.expected")
  if outside "./$name/red.exe" > "$work/$name.log" 2>&1; then
    fail "I4 red control $name: the outside project builds, and it must not" "$work/$name.log"
  fi
  grep -qF -- "$line" "$work/$name.log" || fail "I4 red control $name: the build fails, but not with its red.expected" "$work/$name.log"
  echo "PASS I4 red control $name: the build fails with: $line"
  reds=$((reds + 1))
done
[ "$reds" -ge 1 ] || fail "I4 the consumer has a red control"
