#!/usr/bin/env bash
# Shared shell library for the gates and generators. Source it, never run it:
#
#   . "$(dirname "${BASH_SOURCE[0]}")/lib/portable.sh"
#
# It holds the two portability shims the sweep needs -- the authoring machine is
# macOS and the CI runner is Ubuntu, and `shasum -a 256` and `sed -i ''` exist on
# only one of them (survey finding H36) -- and the one Lean runner that refuses
# to swallow a diagnostic (rule 6 of docs/research/2026-09-03-refactor-plan.md).
#
# `sha256` prints the digest alone, in lowercase hex, with no filename and no
# trailing space, so a caller may embed it directly after `sha256=`; the goldens
# and ledgers under generated/ carry those bytes, and both back ends agree on
# them.

# sha256 [file]   the SHA-256 of `file`, or of standard input when given none.
sha256() {
  local digest
  if command -v sha256sum >/dev/null 2>&1; then
    digest="$(sha256sum "$@")"
  elif command -v shasum >/dev/null 2>&1; then
    digest="$(shasum -a 256 "$@")"
  else
    echo "FAIL neither sha256sum nor shasum is available" >&2
    return 1
  fi
  printf '%s\n' "${digest%% *}"
}

# sed_inplace <expression> <file>...   edit files in place under either sed.
# GNU sed reads BSD's mandatory empty backup suffix as the next input file, and
# BSD sed refuses `-i` without one, so the two spellings cannot be shared.
sed_inplace() {
  local expression="$1"; shift
  if sed --version >/dev/null 2>&1; then
    sed -i -e "$expression" "$@"        # GNU
  else
    sed -i '' -e "$expression" "$@"     # BSD
  fi
}

# lean_run <lean-file> [argument...]
#
# Runs `lake env lean --run <lean-file> [argument...]` in the current directory
# and writes what Lean printed, minus lake's `manifest out of date` warning, to
# this function's standard output -- so a caller may capture it, redirect it to
# a golden, or read it line by line exactly as before.
#
# On a non-zero exit it prints
#
#   FAIL <script>: lean --run <lean-file> <arguments> failed (exit <n>)
#
# followed by everything Lean printed, on standard error, and returns Lean's
# status. Lean writes its *errors to standard output*, so the older
# `lake env lean --run ... | grep -v ...` spelling lost them entirely whenever
# the caller captured or discarded that stream: `check-lowering-property.sh` and
# `test-lowering-mutations.sh` both exited 1 with an empty log while
# `Property.lean` had a missing-cases error.
#
# Set PORTABLE_SCRIPT_NAME to name the gate in the FAIL line; it defaults to the
# basename of $0.
lean_run() {
  local lean_file="$1"; shift
  local out err status
  out="$(mktemp "${TMPDIR:-/tmp}/effect4-lean-out.XXXXXX")"
  err="$(mktemp "${TMPDIR:-/tmp}/effect4-lean-err.XXXXXX")"
  lake env lean --run "$lean_file" "$@" >"$out" 2>"$err" && status=0 || status=$?
  if [ "$status" -ne 0 ]; then
    printf 'FAIL %s: lean --run %s %s failed (exit %s)\n' \
      "${PORTABLE_SCRIPT_NAME:-$(basename -- "$0")}" "$lean_file" "$*" "$status" >&2
    cat "$out" "$err" >&2
    rm -f "$out" "$err"
    return "$status"
  fi
  # grep, not sed: grep terminates a final line that has none, and the committed
  # projections were generated with that behaviour. Exit 1 means "every line was
  # the warning", which is not an error; anything above 1 is.
  grep -v '^warning: manifest out of date' "$out" || [ "$?" -eq 1 ]
  status=$?
  rm -f "$out" "$err"
  return "$status"
}
