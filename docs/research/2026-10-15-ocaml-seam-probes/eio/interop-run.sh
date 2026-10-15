#!/bin/sh
# Probe installed interoperability libraries without a repository build.
set -eu
probe_dir=$(CDPATH='' cd -- "$(dirname -- "$0")" && pwd)
build_dir=$(mktemp -d /private/tmp/effect4-interop-probe.XXXXXX)
trap 'rm -rf "$build_dir"' EXIT HUP INT TERM
cp "$probe_dir/interop_probe.ml" "$build_dir/interop_probe.ml"
cd "$build_dir"
opam exec --switch=effect4 -- ocamlfind ocamlopt -thread \
  -package eio_main,domain-local-await,picos_std.structured,picos_mux.fifo,picos_mux.thread,picos_mux.multififo \
  -linkpkg interop_probe.ml -o interop_probe
./interop_probe
