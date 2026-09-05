#!/usr/bin/env bash
# Install the wasm toolchain into the `effect4-wasm` opam switch.
#
# The pinned `effect4` switch (OCaml 5.1.1, js_of_ocaml 5.7.1 — the modelled backend) is NOT
# touched: wasm_of_ocaml-compiler forces js_of_ocaml 6.x, which cannot coexist with the 5.7.1
# pin. Hence a second switch. See ocaml/wasm/README.md §"Trust boundary".
#
# Run:  wsl -e bash /mnt/c/Users/kokok/Dev/lean4-effect4/ocaml/wasm/tools/install-switch.sh
set -u

SWITCH=effect4-wasm
LOG=/tmp/e4-wasm-install.log

echo "=== $(date -Is) install-switch.sh start ===" | tee "$LOG"

if ! opam switch list --short 2>/dev/null | grep -qx "$SWITCH"; then
  echo "creating switch $SWITCH (ocaml-base-compiler.5.1.1)" | tee -a "$LOG"
  opam switch create "$SWITCH" ocaml-base-compiler.5.1.1 >>"$LOG" 2>&1 || {
    echo "FAILED to create switch; see $LOG"; exit 1; }
else
  echo "switch $SWITCH already exists" | tee -a "$LOG"
fi

eval "$(opam env --switch=$SWITCH --set-switch)"

echo "installing dune wasm_of_ocaml-compiler js_of_ocaml js_of_ocaml-ppx" | tee -a "$LOG"
opam install -y dune wasm_of_ocaml-compiler js_of_ocaml js_of_ocaml-ppx >>"$LOG" 2>&1
rc=$?
echo "opam install exit=$rc" | tee -a "$LOG"

echo "=== versions ===" | tee -a "$LOG"
opam list --switch=$SWITCH 2>/dev/null \
  | grep -E "^(dune|wasm_of_ocaml|js_of_ocaml|ocaml-base-compiler|ppxlib|cmdliner|conf-binaryen|ocaml )" \
  | tee -a "$LOG"
wasm-opt --version 2>&1 | tee -a "$LOG"

echo "=== $(date -Is) install-switch.sh done rc=$rc ===" | tee -a "$LOG"
exit $rc
