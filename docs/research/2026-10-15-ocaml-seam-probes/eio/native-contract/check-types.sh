#!/bin/sh
# Negative controls for the exact installed Eio interfaces.
set -eu
probe_dir=$(CDPATH='' cd -- "$(dirname -- "$0")" && pwd)
build_dir=$(mktemp -d /private/tmp/effect4-native-flow-types.XXXXXX)
trap 'rm -rf "$build_dir"' EXIT HUP INT TERM
cp "$probe_dir/missing_method.ml" "$build_dir/missing_method.ml"
cp "$probe_dir/wrong_role.ml" "$build_dir/wrong_role.ml"
cd "$build_dir"
for sample in missing_method wrong_role; do
  if opam exec --switch=effect4 -- ocamlfind ocamlc -thread -package eio \
    -c "$sample.ml" > "$sample.log" 2>&1; then
    printf 'FAILED: %s compiles\n' "$sample"
    exit 1
  fi
  cat "$sample.log"
done
rg -q 'read_methods' missing_method.log
rg -q 'tag\(s\) `R' wrong_role.log
printf 'PASS native source dictionary rejects a missing method\n'
printf 'PASS native Flow consumer rejects a sink in the source position\n'
