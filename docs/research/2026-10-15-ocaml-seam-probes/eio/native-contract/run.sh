#!/bin/sh
# Native Eio provider tests, isolated from the repository build.
set -eu
probe_dir=$(CDPATH='' cd -- "$(dirname -- "$0")" && pwd)
build_dir=$(mktemp -d /private/tmp/effect4-native-flow.XXXXXX)
trap 'rm -rf "$build_dir"' EXIT HUP INT TERM
cp "$probe_dir/flow_probe.ml" "$build_dir/flow_probe.ml"
cd "$build_dir"
opam exec --switch=effect4 -- ocamlfind ocamlopt -thread \
  -package eio_main -linkpkg flow_probe.ml -o flow_probe
./flow_probe
