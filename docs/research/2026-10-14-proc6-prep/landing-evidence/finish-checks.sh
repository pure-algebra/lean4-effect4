#!/bin/bash
set -euo pipefail
export PATH="/tmp/proc6-landing/bin:$PATH"
cd /Users/pooks/Dev/lean4-effect4-codex/ocaml
opam exec --switch=effect4 -- dune build 2>&1 | tee /tmp/proc6-landing/a-dune.log
cd /Users/pooks/Dev/lean4-effect4-codex
make -o ts/eff/node_modules -o harness/truth/node_modules -o apps/todo/node_modules check-compiler check-native check-ocaml check-truth check-host-protocol 2>&1 | tee /tmp/proc6-landing/a-gates.log
make -o ts/eff/node_modules -o harness/truth/node_modules -o apps/todo/node_modules gen-semantics 2>&1 | tee /tmp/proc6-landing/a-semantics.log
lake env lean -DwarningAsError=true /tmp/proc6-landing/p-audit.lean 2>&1 | tee /tmp/proc6-landing/a-final-goals.log
