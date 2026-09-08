#!/usr/bin/env bash
# Shared reader and judge for the one declared-red policy file,
# `Test/fixtures/trust-gate/known-red.txt`. Source it, never run it:
#
#   . "$(dirname "${BASH_SOURCE[0]}")/lib/known-red.sh"
#   known_red_load
#
# ## The format, and why it is comments
#
# The file is a list of targets that are INTENTIONALLY red, one per line, with
# blank lines and `#` comments ignored. Two comment forms are structured:
#
#   # reason: <text>   the named failure reason of every entry below it, until
#                      the next `# reason:` line. An entry reached with no
#                      reason in force is a defect: the load refuses.
#   # gate: <name>     a sweep gate (`scripts/sweep.sh`'s table) rather than a
#                      Lean module. The bare lines stay Lean module names.
#
# Both are ordinary `#` comments, and that is the whole point of the choice.
# `Test/Audit/AxiomGate.lean` (`declaredRedModules`) and
# `scripts/test-trust-gate.sh` already drop every line whose first non-space
# character is `#`, so reasons and gate entries were added with NO change to
# either existing parser, and every module entry's text is byte-for-byte the one
# those two parsers read before. A second tab-separated column would have needed
# an edit inside the Lean audit root, which is a rebuild of the whole battery
# tree for a policy change.
#
# ## The policy
#
# One observed result per entry -- `fail`, `pass`, or `missing` (no build
# product, no source, or a skipped gate) -- gives one verdict:
#
#   declared   + fail     `red as declared`      accepted
#   declared   + pass     `UNEXPECTED PASS`      REFUSES. The entry has outlived
#                                                its red phase and must be
#                                                removed deliberately; it is
#                                                never masked.
#   declared   + missing  `not built`            accepted, reported
#   undeclared + fail     `UNDECLARED FAILURE`   REFUSES, exactly as today
#   undeclared + pass     (not reported)         green
#
# Every entry is judged on its own evidence. A known case that fails accepts
# nothing but itself: it never turns a sibling failure, or a whole build, into
# an accepted one.

# The parsed policy, as three parallel arrays (bash 3.2 has no associative
# arrays and the authoring machine is macOS; see lib/portable.sh).
KNOWN_RED_KIND=()
KNOWN_RED_TARGET=()
KNOWN_RED_REASON=()
KNOWN_RED_PATH=""

known_red_trim() {
  local s="$1"
  s="${s#"${s%%[![:space:]]*}"}"
  s="${s%"${s##*[![:space:]]}"}"
  printf '%s' "$s"
}

known_red_default_file() {
  local lib_dir
  lib_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
  printf '%s' "$(cd "$lib_dir/../.." && pwd)/Test/fixtures/trust-gate/known-red.txt"
}

# known_red_load [file]   parse the policy file; refuse an entry with no reason.
known_red_load() {
  local file="${1:-$(known_red_default_file)}"
  KNOWN_RED_PATH="$file"
  KNOWN_RED_KIND=()
  KNOWN_RED_TARGET=()
  KNOWN_RED_REASON=()
  if [ ! -f "$file" ]; then
    echo "FAIL known-red: $file is missing; the declared-red set is part of the gate, not an optional file" >&2
    return 1
  fi
  local raw line body reason="" target lineno=0 unexplained=0
  while IFS= read -r raw || [ -n "$raw" ]; do
    lineno=$((lineno + 1))
    line="$(known_red_trim "${raw%$'\r'}")"
    case "$line" in
      "") continue ;;
      "#"*)
        body="$(known_red_trim "${line#\#}")"
        case "$body" in
          reason:*) reason="$(known_red_trim "${body#reason:}")" ;;
          gate:*)
            target="$(known_red_trim "${body#gate:}")"
            [ -n "$target" ] || continue
            if [ -z "$reason" ]; then
              echo "FAIL known-red: $file:$lineno declares gate $target with no '# reason:' line above it" >&2
              unexplained=1
            fi
            KNOWN_RED_KIND+=(gate)
            KNOWN_RED_TARGET+=("$target")
            KNOWN_RED_REASON+=("$reason")
            ;;
        esac
        ;;
      *)
        if [ -z "$reason" ]; then
          echo "FAIL known-red: $file:$lineno declares module $line with no '# reason:' line above it" >&2
          unexplained=1
        fi
        KNOWN_RED_KIND+=(module)
        KNOWN_RED_TARGET+=("$line")
        KNOWN_RED_REASON+=("$reason")
        ;;
    esac
  done <"$file"
  [ "$unexplained" -eq 0 ]
}

# known_red_index <kind> <target>   the entry's index, or -1.
known_red_index() {
  local kind="$1" target="$2" i=0
  while [ "$i" -lt "${#KNOWN_RED_TARGET[@]}" ]; do
    if [ "${KNOWN_RED_KIND[$i]}" = "$kind" ] && [ "${KNOWN_RED_TARGET[$i]}" = "$target" ]; then
      printf '%s' "$i"
      return 0
    fi
    i=$((i + 1))
  done
  printf '%s' -1
  return 1
}

# known_red_declared <kind> <target>   true when the policy file declares it.
known_red_declared() {
  known_red_index "$1" "$2" >/dev/null
}

# known_red_reason <kind> <target>   the named failure reason, or the empty string.
known_red_reason() {
  local i
  i="$(known_red_index "$1" "$2")" || { printf ''; return 1; }
  printf '%s' "${KNOWN_RED_REASON[$i]}"
}

# known_red_verdict <kind> <target> <observed>
#
# Prints the verdict; returns 0 when it is accepted and 1 when it refuses.
known_red_verdict() {
  local kind="$1" target="$2" observed="$3"
  if known_red_declared "$kind" "$target"; then
    case "$observed" in
      fail)    printf 'red as declared';    return 0 ;;
      pass)    printf 'UNEXPECTED PASS';    return 1 ;;
      missing) printf 'not built';          return 0 ;;
      *) printf 'unknown result %s' "$observed"; return 1 ;;
    esac
  fi
  case "$observed" in
    fail)    printf 'UNDECLARED FAILURE'; return 1 ;;
    pass)    printf 'green';              return 0 ;;
    missing) printf 'not built';          return 0 ;;
    *) printf 'unknown result %s' "$observed"; return 1 ;;
  esac
}

known_red_row() {
  printf '  %-7s %-46s %-19s %s\n' "$1" "$2" "$3" "$4"
}

# known_red_judge <results-file> [kind]
#
# `<results-file>` holds one `<kind> <target> <pass|fail|missing>` per line, in
# any order; blank lines and `#` comments are ignored. Prints the per-entry
# table -- every declared entry of `<kind>` (defaulting to every kind), plus
# every observed failure that is not declared -- and returns 1 if any row
# refuses. A declared entry with no observed result reads `not built`.
known_red_judge() {
  local results="$1" want="${2:-}"
  local refused=0 i=0 kind target observed reason verdict line
  known_red_row kind target verdict reason
  while [ "$i" -lt "${#KNOWN_RED_TARGET[@]}" ]; do
    kind="${KNOWN_RED_KIND[$i]}"
    target="${KNOWN_RED_TARGET[$i]}"
    i=$((i + 1))
    if [ -n "$want" ] && [ "$kind" != "$want" ]; then continue; fi
    observed="$(known_red_observed "$results" "$kind" "$target")"
    verdict="$(known_red_verdict "$kind" "$target" "$observed")" || refused=1
    known_red_row "$kind" "$target" "$verdict" "$(known_red_reason "$kind" "$target")"
  done
  # Anything red that nobody declared still fails, exactly as before this file
  # existed. This is the half that keeps a known-red list from becoming a mask.
  while IFS= read -r line; do
    line="$(known_red_trim "${line%$'\r'}")"
    case "$line" in ""|"#"*) continue ;; esac
    # shellcheck disable=SC2086
    set -- $line
    kind="${1:-}"; target="${2:-}"; observed="${3:-}"
    [ -n "$kind" ] && [ -n "$target" ] || continue
    if [ -n "$want" ] && [ "$kind" != "$want" ]; then continue; fi
    if known_red_declared "$kind" "$target"; then continue; fi
    [ "$observed" = fail ] || continue
    known_red_row "$kind" "$target" "UNDECLARED FAILURE" "not declared in $(basename -- "$KNOWN_RED_PATH")"
    refused=1
  done <"$results"
  [ "$refused" -eq 0 ]
}

# known_red_observed <results-file> <kind> <target>
#
# The observed result recorded for one entry, or `missing` when the run
# produced none.
known_red_observed() {
  local results="$1" kind="$2" target="$3" line k t o
  while IFS= read -r line; do
    line="$(known_red_trim "${line%$'\r'}")"
    case "$line" in ""|"#"*) continue ;; esac
    # shellcheck disable=SC2086
    set -- $line
    k="${1:-}"; t="${2:-}"; o="${3:-}"
    if [ "$k" = "$kind" ] && [ "$t" = "$target" ]; then
      printf '%s' "${o:-missing}"
      return 0
    fi
  done <"$results"
  printf 'missing'
}
