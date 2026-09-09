#!/usr/bin/env bash
# The declared-red policy, standalone: parse `Test/fixtures/trust-gate/known-red.txt`,
# judge one observed result per entry, and refuse an UNEXPECTED PASS or an
# undeclared failure. `scripts/lib/known-red.sh` holds the format and the policy;
# this script is its command line.
#
#   scripts/check-known-red.sh --list              parse and print the table; builds nothing
#   scripts/check-known-red.sh --self-test         the policy over fabricated result lists
#   scripts/check-known-red.sh --dry-run <file>    the policy over a given result list
#   scripts/check-known-red.sh                     elaborate every declared module and judge it
#
# A result list is one `<kind> <target> <pass|fail|missing>` per line.
#
# The default mode is the same evidence `scripts/test-trust-gate.sh` step 0b
# collects -- one `lake env lean` per declared module -- so run it under the
# machine's Lean lock, and prefer the dry run when only the policy is in
# question. Gate entries are judged by the gate that owns them
# (`scripts/check-ocaml.sh`), not here: this script cannot observe an OCaml
# switch it did not run.
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
. "$repo_root/scripts/lib/known-red.sh"

mode=check
dry_run_file=""
policy_file="$repo_root/Test/fixtures/trust-gate/known-red.txt"
while [ "$#" -gt 0 ]; do
  case "$1" in
    --list)      mode=list ;;
    --self-test) mode=self-test ;;
    --dry-run)   mode=dry-run; dry_run_file="${2:?--dry-run needs a result list}"; shift ;;
    --file)      policy_file="${2:?--file needs a path}"; shift ;;
    -h|--help)   sed -n '2,/^set -euo/p' "${BASH_SOURCE[0]}" | sed '$d; s/^# \{0,1\}//'; exit 0 ;;
    *) echo "unknown argument $1; try --help" >&2; exit 2 ;;
  esac
  shift
done

# The module -> source mapping is the audit gate's `modulePath`: the library
# lives under `src/`, the batteries and the authored fixtures at the root.
module_source() {
  case "$1" in
    Effect4|Effect4.*) printf 'src/%s.lean' "${1//.//}" ;;
    *) printf '%s.lean' "${1//.//}" ;;
  esac
}

known_red_load "$policy_file"

case "$mode" in
  list)
    printf 'known-red policy: %s\n' "$policy_file"
    printf '  %-7s %-46s %s\n' kind target reason
    i=0
    while [ "$i" -lt "${#KNOWN_RED_TARGET[@]}" ]; do
      printf '  %-7s %-46s %s\n' \
        "${KNOWN_RED_KIND[$i]}" "${KNOWN_RED_TARGET[$i]}" "${KNOWN_RED_REASON[$i]}"
      i=$((i + 1))
    done
    printf 'PASS known-red: %s entries, every one with a named reason\n' "${#KNOWN_RED_TARGET[@]}"
    ;;

  dry-run)
    printf 'known-red dry run: %s against %s\n' "$policy_file" "$dry_run_file"
    if known_red_judge "$dry_run_file"; then
      echo "PASS known-red: every entry is red as declared or not built, and nothing undeclared failed"
    else
      echo "FAIL known-red: the table above has an UNEXPECTED PASS or an UNDECLARED FAILURE" >&2
      exit 1
    fi
    ;;

  self-test)
    # Fabricated result lists, so the policy itself is exercised without a build.
    # Every case of the table in lib/known-red.sh appears at least once, and case
    # 3 is the one that says a known red case accepts nothing but itself.
    tmp="$(mktemp -d "${TMPDIR:-/tmp}/effect4-known-red.XXXXXX")"
    trap 'rm -rf -- "$tmp"' EXIT
    first="${KNOWN_RED_TARGET[0]}"
    second="${KNOWN_RED_TARGET[1]}"
    failures=0
    expect() {
      local label="$1" want="$2" file="$3" kind="${4:-}" got=0
      known_red_judge "$file" "$kind" >"$tmp/out" 2>&1 || got=1
      if [ "$got" -eq "$want" ]; then
        printf 'PASS self-test: %s\n' "$label"
      else
        printf 'FAIL self-test: %s (exit %s, wanted %s)\n' "$label" "$got" "$want" >&2
        sed 's/^/    /' "$tmp/out" >&2
        failures=$((failures + 1))
      fi
      sed 's/^/    /' "$tmp/out"
    }

    # 1. every declared entry red, nothing else failing: accepted.
    : >"$tmp/all-red"
    i=0
    while [ "$i" -lt "${#KNOWN_RED_TARGET[@]}" ]; do
      printf '%s %s fail\n' "${KNOWN_RED_KIND[$i]}" "${KNOWN_RED_TARGET[$i]}" >>"$tmp/all-red"
      i=$((i + 1))
    done
    printf 'module Test.Machine.SomethingGreen pass\n' >>"$tmp/all-red"
    expect 'every declared entry red, one undeclared green' 0 "$tmp/all-red"

    # 2. one declared entry green: UNEXPECTED PASS refuses. The entry has to be
    #    removed deliberately; nothing here may quietly drop it.
    sed "s|^module $second fail\$|module $second pass|" "$tmp/all-red" >"$tmp/unexpected-pass"
    expect 'a declared entry that has gone green refuses' 1 "$tmp/unexpected-pass"

    # 3. a known red entry beside an undeclared failure: still refuses. This is
    #    the clause that keeps the list from turning a build into accepted failure.
    cp "$tmp/all-red" "$tmp/undeclared"
    printf 'module Test.Machine.SomethingRed fail\n' >>"$tmp/undeclared"
    expect 'an undeclared failure beside a known red one still refuses' 1 "$tmp/undeclared"

    # 4. a declared entry with no observed result reads `not built`, accepted.
    grep -Fv "module $first fail" "$tmp/all-red" >"$tmp/not-built"
    expect 'a declared entry with no result is `not built`' 0 "$tmp/not-built"

    # 5. a declared gate, red and then green. Gates share the module policy.
    printf 'gate engine-tests fail\n' >"$tmp/gate-red"
    printf 'gate engine-tests pass\n' >"$tmp/gate-green"
    if known_red_declared gate engine-tests; then
      expect 'a declared gate that is red is accepted' 0 "$tmp/gate-red" gate
      expect 'a declared gate that has gone green refuses' 1 "$tmp/gate-green" gate
    else
      printf 'NOTE self-test: the sample gate is not declared red today, so the gate half is exercised as the undeclared case\n'
      expect 'an undeclared gate failure refuses' 1 "$tmp/gate-red" gate
    fi

    if [ "$failures" -eq 0 ]; then
      echo "PASS known-red self-test: the policy holds on every fabricated case"
    else
      echo "FAIL known-red self-test: $failures cases" >&2
      exit 1
    fi
    ;;

  check)
    cd "$repo_root"
    results="$(mktemp "${TMPDIR:-/tmp}/effect4-known-red.XXXXXX")"
    log="$(mktemp "${TMPDIR:-/tmp}/effect4-known-red-log.XXXXXX")"
    trap 'rm -f -- "$results" "$log"' EXIT
    i=0
    while [ "$i" -lt "${#KNOWN_RED_TARGET[@]}" ]; do
      kind="${KNOWN_RED_KIND[$i]}"
      target="${KNOWN_RED_TARGET[$i]}"
      i=$((i + 1))
      if [ "$kind" != module ]; then continue; fi
      source_file="$(module_source "$target")"
      if [ ! -f "$source_file" ]; then
        printf 'module %s missing\n' "$target" >>"$results"
      elif lake env lean -M4096 "$source_file" >"$log" 2>&1; then
        printf 'module %s pass\n' "$target" >>"$results"
      else
        printf 'module %s fail\n' "$target" >>"$results"
      fi
    done
    if known_red_judge "$results" module; then
      echo "PASS known-red: every declared module is red as declared or not built"
    else
      echo "FAIL known-red: the table above has an UNEXPECTED PASS or an UNDECLARED FAILURE" >&2
      exit 1
    fi
    ;;
esac
