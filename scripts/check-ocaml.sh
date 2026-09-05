#!/usr/bin/env bash
# Stamped OCaml estate gates. Requires the effect4 switch; absent runtimes are a SKIP.
set -euo pipefail
repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
. "$repo_root/scripts/lib/portable.sh"
. "$repo_root/scripts/lib/stamp.sh"
gate="${1:?expected avatar-witnesses, daemon-protocol or dune-tests}"
case "$gate" in avatar-witnesses|daemon-protocol|dune-tests) ;; *) echo "FAIL unknown OCaml gate: $gate" >&2; exit 2;; esac
if command -v opam >/dev/null 2>&1; then
  eval "$(opam env --switch="${EFFECT4_OPAM_SWITCH:-effect4}" --set-switch 2>/dev/null)"
fi
if ! command -v ocamlrun >/dev/null 2>&1; then
  echo "SKIP $gate: requires ocamlrun from the effect4 opam switch; run opam env --switch=effect4 --set-switch"
  exit 0
fi
. "$repo_root/ocaml/tools/lib/toolchain.sh"
effect4_toolchain
command -v dune >/dev/null 2>&1 || { echo "FAIL $gate: dune is required in the effect4 switch" >&2; exit 1; }
cd "$repo_root"
inputs=()
while IFS= read -r file; do inputs+=("$file"); done < <(git ls-files --cached --others --exclude-standard ocaml src/Effect4/Machine src/OCaml5)
key="$(stamp_key scripts/check-ocaml.sh "${inputs[@]}" Test/Audit/RuntimeCoverage.lean \
  "$(stamp_fact ocaml "$(ocamlc -version)")" "$(stamp_fact dune "$(dune --version)")" \
  "$(stamp_fact jsoo "$(js_of_ocaml --version)")" \
  "$(stamp_fact node "$(node --version 2>/dev/null || node.exe --version 2>/dev/null || echo absent)")")"
if stamp_hit "$gate" "$key"; then stamp_report "$gate" "$key"; exit 0; fi
case "$gate" in
  avatar-witnesses) (cd ocaml && dune build avatar); bash ocaml/avatar/run-witnesses.sh ;;
  daemon-protocol) bash ocaml/server/tools/dune-test.sh ;;
  dune-tests) (cd ocaml && dune build && dune test eff gen) ;;
esac
stamp_write "$gate" "$key" 'the requested OCaml checks passed'
echo "PASS $gate: the requested OCaml checks passed"
