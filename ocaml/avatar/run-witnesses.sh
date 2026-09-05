#!/usr/bin/env bash
# Seat F1: the witness and clause report on the three OCaml hosts.
#
#   run-witnesses.sh
#
# Runs `avatar_witnesses` (bytecode, native, js_of_ocaml --enable effects) on the three
# hosts; requires the three reports byte-identical; writes the report to
# `out/witnesses.report.tsv`; and guards the entry counts against the Lean files
# (`src/Effect4/Machine/Clauses.lean` theorems = `Deep_clauses.count`,
# `src/Effect4/Machine/Witnesses.lean` theorems = `Deep_witnesses.count`, `deep_census.ml`
# identical to `Test/Audit/RuntimeCoverage.lean`).
#
# The binaries are dune's since 2026-09-04 (this script used to drive ocamlc/ocamlopt and a
# js_of_ocaml from a Mac toolchain directly). Build them first:
#
#   cd ocaml && dune build avatar        # -> ocaml/_build/default/avatar/
#
# The workspace build is preferred, the project-local `--root .` build
# (`avatar/_build/default/`) is the fallback, and `AVATAR_BIN` overrides both. The js host
# needs a `node`: on a machine with node on the PATH it is used as is; under WSL, where node
# is not installed but the Windows node is reachable through interop, `node.exe` is used and
# the path handed to it is converted with `wslpath -w`. `A0_NODE` names it otherwise; with
# no node at all the js host is skipped and the two-host comparison still runs.
#
# Exit 1 on: a missing binary, hosts that disagree, a count drift, a census drift, or a
# witness statement that FAILS. A clause that FAILS or is NOT PORTABLE is reported, not
# fatal: those are the report's rows (`docs/research/2026-09-04-seat-w1-deep-port.md`).
set -uo pipefail
here=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
# <repo>/ocaml/avatar -> <repo>. The estate lived under `workshop/OCaml5/` until 2026-09-04.
repo=$(CDPATH= cd -- "$here/../.." && pwd)
# Scratch for the three hosts' raw reports; only `out/witnesses.report.tsv` is kept in tree.
out=${A0_BUILD:-${TMPDIR:-/tmp}/effect4-avatar-witnesses}
mkdir -p "$out" "$here/out"
status=0
command -v ocamlrun > /dev/null 2>&1 || {
  echo "no ocamlrun on the PATH: eval \$(opam env --switch=effect4 --set-switch)" >&2; exit 1; }

bin=${AVATAR_BIN:-}
if [ -z "$bin" ]; then
  if   [ -x "$here/../_build/default/avatar/avatar_witnesses.exe" ]; then bin="$here/../_build/default/avatar"
  elif [ -x "$here/_build/default/avatar_witnesses.exe" ];           then bin="$here/_build/default"
  else echo "no avatar_witnesses.exe: build with 'dune build avatar' from ocaml/" >&2; exit 1; fi
fi
echo "binaries: $bin"

# --- which node, and how it sees a path -------------------------------------------------
node_cmd=""
to_node() { printf '%s' "$1"; }
if [ -n "${A0_NODE:-}" ]; then node_cmd=$A0_NODE
elif command -v node > /dev/null 2>&1; then node_cmd=node
elif command -v node.exe > /dev/null 2>&1; then node_cmd=node.exe
fi
case "$node_cmd" in *.exe) to_node() { wslpath -w "$1"; } ;; esac

ocamlrun "$bin/avatar_witnesses.bc" > "$out/byte.tsv"  || { echo "bytecode host failed"; exit 1; }
"$bin/avatar_witnesses.exe"         > "$out/native.tsv" || { echo "native host failed"; exit 1; }
if [ -n "$node_cmd" ]; then
  # node prints "\n"-terminated lines; the OCaml hosts do too, so the files compare directly.
  "$node_cmd" "$(to_node "$bin/avatar_witnesses.bc.js")" > "$out/jsoo.tsv" \
    || { echo "js_of_ocaml host failed"; exit 1; }
  if cmp -s "$out/byte.tsv" "$out/native.tsv" && cmp -s "$out/byte.tsv" "$out/jsoo.tsv"; then
    echo "hosts witnesses AGREE (bytecode = native = js_of_ocaml)"
  else
    echo "hosts witnesses DISAGREE"; status=1
  fi
else
  echo "no node found: the js_of_ocaml host is not exercised (set A0_NODE)"
  if cmp -s "$out/byte.tsv" "$out/native.tsv"; then echo "hosts witnesses AGREE (bytecode = native)"
  else echo "hosts witnesses DISAGREE"; status=1; fi
fi
cp "$out/byte.tsv" "$here/out/witnesses.report.tsv"

# The entry counts against the Lean files.
lean_clauses=$(grep -c '^theorem' "$repo/src/Effect4/Machine/Clauses.lean")
lean_witnesses=$(grep -c '^theorem' "$repo/src/Effect4/Machine/Witnesses.lean")
have_clauses=$(awk -F'\t' '$1=="clauses"{print $2}' "$out/byte.tsv")
have_witnesses=$(awk -F'\t' '$1=="witnesses"{print $2}' "$out/byte.tsv")
if [ "$lean_clauses" = "$have_clauses" ]; then echo "clauses: $have_clauses entries = $lean_clauses Clauses.lean theorems"
else echo "clauses: $have_clauses entries != $lean_clauses Clauses.lean theorems"; status=1; fi
if [ "$lean_witnesses" = "$have_witnesses" ]; then echo "witnesses: $have_witnesses entries = $lean_witnesses Witnesses.lean theorems"
else echo "witnesses: $have_witnesses entries != $lean_witnesses Witnesses.lean theorems"; status=1; fi
python3 "$here/extract-census.py" --check || status=1
python3 "$here/check-witness-names.py" "$out/byte.tsv" || status=1

grep -E '^clauses|^witnesses|^run-clauses|^park-guard' "$out/byte.tsv"
# Seat F2: the park guard/one-shot probe must be silent on every run.
if [ "$(awk -F'\t' '$1=="park-guard"{print $3}' "$out/byte.tsv")" != "0" ]; then
  echo "park-guard violations on the avatar"; status=1
fi
if [ "$(awk -F'\t' '$1=="witnesses"{print $6}' "$out/byte.tsv")" != "0" ]; then
  echo "witness statements FAIL on the avatar:"; grep -B1 '^  statement	FAILS' "$out/byte.tsv"; status=1
fi
if grep -q 'FAILS' "$out/byte.tsv"; then
  echo "clause or witness probe FAILS on the avatar"; status=1
fi
if [ "$(awk -F'\t' '$1=="run-clauses"{print $3}' "$out/byte.tsv")" -eq 0 ]; then
  echo "FAIL no census-joined run clause was exercised"; status=1
fi
# Seat F3: the Deep-file drift gate (`deep-pins.tsv`). A re-spelled arm under an unchanged
# theorem count is invisible to the counts above; the content hash is not. `DEEP_PIN=skip`
# reports without failing, for a checkout that is knowingly mid-re-diff.
if [ "${DEEP_PIN:-}" = "skip" ]; then "$here/pin-deep.sh" || true
else "$here/pin-deep.sh" || status=1; fi
exit $status
