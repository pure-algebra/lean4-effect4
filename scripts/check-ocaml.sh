#!/usr/bin/env bash
# Stamped OCaml estate gates. Requires the effect4 switch; absent runtimes are a SKIP.
#
# A gate that is red for a declared reason is declared in the one policy file,
# `Test/fixtures/trust-gate/known-red.txt`, as a `# gate: <name>` entry under a
# `# reason:` line -- not special-cased here. This script runs the gate either
# way and asks `scripts/lib/known-red.sh` what its result means: `red as
# declared` passes, an `UNEXPECTED PASS` refuses (the entry has outlived its red
# phase and must be removed deliberately), an undeclared failure refuses exactly
# as before, and a gate the host cannot run is `not built`. No stamp is written
# for a declared-red gate: there is no pass to cache.
set -euo pipefail
repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
. "$repo_root/scripts/lib/portable.sh"
. "$repo_root/scripts/lib/stamp.sh"
. "$repo_root/scripts/lib/known-red.sh"
gate="${1:?expected gen-check, engine-tests or dune-tests}"
case "$gate" in gen-check|engine-tests|dune-tests) ;; *) echo "FAIL unknown OCaml gate: $gate" >&2; exit 2;; esac
known_red_policy="$repo_root/Test/fixtures/trust-gate/known-red.txt"
known_red_load "$known_red_policy"
known_red_results="$(mktemp "${TMPDIR:-/tmp}/effect4-ocaml-known-red.XXXXXX")"
trap 'rm -f -- "$known_red_results"' EXIT
if command -v opam >/dev/null 2>&1; then
  eval "$(opam env --switch="${EFFECT4_OPAM_SWITCH:-effect4}" --set-switch 2>/dev/null)"
fi
if ! command -v ocamlrun >/dev/null 2>&1; then
  if known_red_declared gate "$gate"; then
    printf 'gate %s missing\n' "$gate" >"$known_red_results"
    known_red_judge "$known_red_results" gate || true
  fi
  echo "SKIP $gate: requires ocamlrun from the effect4 opam switch; run opam env --switch=effect4 --set-switch"
  exit 0
fi
. "$repo_root/ocaml/tools/lib/toolchain.sh"
effect4_toolchain
command -v dune >/dev/null 2>&1 || { echo "FAIL $gate: dune is required in the effect4 switch" >&2; exit 1; }
cd "$repo_root"
inputs=()
while IFS= read -r file; do inputs+=("$file"); done < <(git ls-files --cached --others --exclude-standard ocaml src/Effect4 src/OCaml5)
key="$(stamp_key scripts/check-ocaml.sh scripts/lib/known-red.sh \
  Test/fixtures/trust-gate/known-red.txt "${inputs[@]}" Test/Audit/RuntimeCoverage.lean \
  "$(stamp_fact ocaml "$(ocamlc -version)")" "$(stamp_fact dune "$(dune --version)")" \
  "$(stamp_fact jsoo "$(js_of_ocaml --version)")" \
  "$(stamp_fact node "$(node --version 2>/dev/null || node.exe --version 2>/dev/null || echo absent)")")"
if stamp_hit "$gate" "$key"; then stamp_report "$gate" "$key"; exit 0; fi
run_gate() {
  case "$gate" in
    # `&&`, not `;`: `set -e` does not reach into a function called as an `if`
    # condition, and a failed `dune build` must still stop the gate there.
    gen-check) bash ocaml/engine/tools/gen-check.sh ;;
    engine-tests) (cd ocaml && dune test engine) ;;
    dune-tests) (cd ocaml && dune build && dune test eff gen) ;;
  esac
}
# Rule 6: the gate's own diagnostic, never a summary of it, so nothing is captured.
if run_gate; then observed=pass; else observed=fail; fi
printf 'gate %s %s\n' "$gate" "$observed" >"$known_red_results"
if known_red_declared gate "$gate"; then
  if known_red_judge "$known_red_results" gate; then
    echo "PASS $gate: red as declared in Test/fixtures/trust-gate/known-red.txt -- $(known_red_reason gate "$gate")"
    exit 0
  fi
  echo "FAIL $gate: it is declared red in Test/fixtures/trust-gate/known-red.txt but passed; \
remove the entry deliberately rather than leaving the declaration to mask the next real failure" >&2
  exit 1
fi
if [ "$observed" != pass ]; then
  echo "FAIL $gate: the requested OCaml checks failed" >&2
  exit 1
fi
stamp_write "$gate" "$key" 'the requested OCaml checks passed'
echo "PASS $gate: the requested OCaml checks passed"
