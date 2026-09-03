#!/usr/bin/env bash
# The sweep: every gate of the trace, lowering, citation and runtime-census
# lanes, in dependency order, one process at a time.
#
# This is the entry point. Before it there was no sweep, only a scratchpad of
# `.log` files and fifteen of fifty-seven scripts that somebody remembered to
# run, which is how two drift gates stayed red on main without anyone noticing
# (survey findings H34 and H5).
#
#   ./scripts/sweep.sh                 every gate; stop at the first failure
#   ./scripts/sweep.sh --keep-going    run them all and report at the end
#   ./scripts/sweep.sh --hermetic      the host-free subset, which is what CI runs
#   ./scripts/sweep.sh --force         ignore every stamp and re-run everything
#   ./scripts/sweep.sh --list          print the table and exit
#
# ## Order
#
# Generators before checkers -- each drift gate regenerates from Lean inside
# itself, so this is a property of the gates rather than of the list. Then
# hermetic before host: the Lean-only gates need no node and no installed
# Effect, they are the ones CI can run, and a golden that has drifted from Lean
# should be reported before a minute of host runs against it. Then the host
# lane, `check-trace-host.sh` first because it is what establishes that the
# committed TypeScript modules are still Lean's. Self-tests last: they plant
# defects and ask whether the gates catch them, which is only worth asking once
# the gates have passed on the real tree.
#
# ## Stamps
#
# Rule 9 of docs/research/2026-09-03-refactor-plan.md. Every gate below keys a
# stamp under `.lake/stamps/<gate>/` on the content of what it reads, so a
# second sweep with nothing changed re-runs nothing and costs seconds rather
# than minutes. The `hit`/`miss` column says which happened; `--force` makes
# every gate a miss. What each gate keys on is written at the top of that gate.
#
# ## Where the summary goes
#
# `.lake/sweep-summary.tsv`, not `generated/`. Everything under `generated/` is
# a deterministic projection of committed inputs, and a table of wall-clock
# seconds is not: it changes with the machine, the load and which gates were
# stamped. `.lake/` is the right home -- gitignored, and removed by exactly the
# command that removes the build the timings describe.
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
. "$repo_root/scripts/lib/portable.sh"

hermetic_only=0
keep_going=0
list_only=0
for argument in "$@"; do
  case "$argument" in
    --hermetic)   hermetic_only=1 ;;
    --keep-going) keep_going=1 ;;
    --force)      export EFFECT4_FORCE=1 ;;
    --list)       list_only=1 ;;
    -h|--help)    sed -n '2,/^set -euo/p' "${BASH_SOURCE[0]}" | sed '$d; s/^# \{0,1\}//'; exit 0 ;;
    *) echo "unknown argument $argument; try --help" >&2; exit 2 ;;
  esac
done

# lane|name|command, in the order they run. `lane` is `hermetic` when the gate
# needs no node and no installed Effect package, and `host` when it does.
gate_table() {
  cat <<'GATES'
hermetic|trace-goldens|scripts/check-trace-goldens.sh
hermetic|lowering-coverage|scripts/check-lowering-coverage.sh
hermetic|internal-citations|scripts/check-internal-citations.sh
hermetic|effect-runtime-census|scripts/check-effect-runtime-census.sh
host|trace-host|scripts/check-trace-host.sh
host|lowering-types|scripts/check-lowering-types.sh
host|trace-patched|scripts/check-trace-patched.sh
host|lowering-property|scripts/check-lowering-property.sh
host|effect-v4-family|harness/effect-v4-family/check.sh
hermetic|lowering-coverage-gate|scripts/test-lowering-coverage-gate.sh
host|trace-goldens-gate|scripts/test-trace-goldens-gate.sh
host|lowering-mutations|scripts/test-lowering-mutations.sh
GATES
}

if [ "$list_only" -eq 1 ]; then
  printf '%-24s %-9s %s\n' gate lane command
  while IFS='|' read -r lane name command; do
    if [ "$hermetic_only" -eq 1 ] && [ "$lane" != hermetic ]; then continue; fi
    printf '%-24s %-9s %s\n' "$name" "$lane" "$command"
  done < <(gate_table)
  exit 0
fi

logs="$repo_root/.lake/sweep-logs"
summary="$repo_root/.lake/sweep-summary.tsv"
mkdir -p "$logs" "$(dirname "$summary")"
printf 'gate\tstatus\tseconds\tstamp\n' >"$summary"

failed=0
ran=0
hits=0
sweep_start="$(date +%s)"
scope="every gate"
if [ "$hermetic_only" -eq 1 ]; then scope="the hermetic subset"; fi
echo "sweep: $scope, one process at a time"

while IFS='|' read -r lane name command; do
  if [ "$hermetic_only" -eq 1 ] && [ "$lane" != hermetic ]; then continue; fi
  log="$logs/$name.log"
  start="$(date +%s)"
  if ( cd "$repo_root" && "./$command" ) >"$log" 2>&1; then status=PASS; else status=FAIL; fi
  seconds="$(( $(date +%s) - start ))"
  # A gate that hit its stamp says so in the line `stamp_report` prints.
  if grep -Fq 'skipped (EFFECT4_FORCE=1 re-runs)' "$log"; then
    stamp=hit; hits=$((hits + 1))
  else
    stamp=miss
  fi
  ran=$((ran + 1))
  printf '%-24s %-4s %4ss  %s\n' "$name" "$status" "$seconds" "$stamp"
  printf '%s\t%s\t%s\t%s\n' "$name" "$status" "$seconds" "$stamp" >>"$summary"
  if [ "$status" = FAIL ]; then
    failed=$((failed + 1))
    # Rule 6: the gate's own diagnostic, never a summary of it.
    echo "--- $name failed; last 60 lines of $log ---" >&2
    tail -60 "$log" >&2
    echo "--- end of $name ---" >&2
    if [ "$keep_going" -eq 0 ]; then
      echo "FAIL sweep stopped at $name ($ran of the gates run); --keep-going runs the rest" >&2
      exit 1
    fi
  fi
done < <(gate_table)

total="$(( $(date +%s) - sweep_start ))"
printf 'sweep: %s gates, %s hit, %s miss, %ss total; table in .lake/sweep-summary.tsv\n' \
  "$ran" "$hits" "$((ran - hits))" "$total"
if [ "$failed" -gt 0 ]; then
  echo "FAIL $failed of $ran gates failed; logs under .lake/sweep-logs/" >&2
  exit 1
fi
echo "PASS $scope is green"
