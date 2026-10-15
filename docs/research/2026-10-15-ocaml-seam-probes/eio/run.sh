#!/bin/sh
# Standalone finite host probes. No repository build or installation.
set -eu
probe_dir=$(CDPATH='' cd -- "$(dirname -- "$0")" && pwd)
build_dir=$(mktemp -d /private/tmp/effect4-eio-probe.XXXXXX)
trap 'rm -rf "$build_dir"' EXIT HUP INT TERM
cp "$probe_dir/eio_probe.ml" "$build_dir/eio_probe.ml"
cp "$probe_dir/resource_probe.ml" "$build_dir/resource_probe.ml"
cp "$probe_dir/unsupported_resource.ml" "$build_dir/unsupported_resource.ml"
cd "$build_dir"
printf 'x' > input.txt
opam exec --switch=effect4 -- ocamlfind ocamlopt -thread \
  -package eio_main -linkpkg eio_probe.ml -o eio_probe
./eio_probe
opam exec --switch=effect4 -- ocamlfind ocamlopt -thread \
  -package eio -linkpkg resource_probe.ml -o resource_probe
./resource_probe
if opam exec --switch=effect4 -- ocamlfind ocamlc -thread -package eio \
    -c unsupported_resource.ml > unsupported-resource.log 2>&1; then
  printf 'FAILED: unsupported interface compiled\n'
  exit 1
fi
cat unsupported-resource.log
if ! grep -q 'Lookup' unsupported-resource.log; then
  printf 'FAILED: compiler refused for an unexpected reason\n'
  exit 1
fi
printf 'PASS compiler refuses a resource without the Lookup interface\n'
