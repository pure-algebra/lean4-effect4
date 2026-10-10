#!/usr/bin/env bash
# Live progress of the running Lake build: the modules written since it started (law graph,
# batteries, the rest) and the modules compiling now with how long each has run. It refreshes
# every two seconds and exits when no `lake build` runs. Run it in a terminal beside a build
# whose output went to a log:
#
#   scripts/build-progress.sh
set -u
root="$(cd "$(dirname "$0")/.." && pwd)"
lib="$root/.lake/build/lib/lean"
marker="$(mktemp "${TMPDIR:-/tmp}/build-progress.XXXXXX")"
trap 'rm -f "$marker"' EXIT

seconds() { # [[dd-]hh:]mm:ss -> seconds
  local t="$1" d=0 h=0 m=0 s=0
  if [[ "$t" == *-* ]]; then d="${t%%-*}"; t="${t#*-}"; fi
  IFS=: read -r a b c <<<"$t"
  if [[ -n "${c:-}" ]]; then h="$a"; m="$b"; s="$c"; else m="$a"; s="$b"; fi
  echo $(( 10#$d * 86400 + 10#$h * 3600 + 10#$m * 60 + 10#$s ))
}

pid="$(pgrep -f "lake build" | head -1)"
if [[ -z "$pid" ]]; then echo "no lake build is running"; exit 0; fi
elapsed="$(ps -o etime= -p "$pid" | tr -d ' ')"
start=$(( $(date +%s) - $(seconds "$elapsed") ))
touch -t "$(date -r "$start" +%Y%m%d%H%M.%S)" "$marker"
laws_total=$(find "$lib/Effect4/Laws" -name '*.olean' | wc -l | tr -d ' ')
test_total=$(find "$lib/Test" -name '*.olean' | wc -l | tr -d ' ')

while pgrep -f "lake build" >/dev/null; do
  laws=$(find "$lib/Effect4/Laws" -name '*.olean' -newer "$marker" | wc -l | tr -d ' ')
  tests=$(find "$lib/Test" -name '*.olean' -newer "$marker" | wc -l | tr -d ' ')
  all=$(find "$lib" -name '*.olean' -newer "$marker" | wc -l | tr -d ' ')
  clear
  echo "lake build, running $(ps -o etime= -p "$pid" | tr -d ' ')"
  echo "written: $all modules  (law graph $laws of $laws_total, batteries $tests of $test_total)"
  echo
  echo "compiling now:"
  ps -eo etime=,args= | grep "bin/lean " | grep -- " -o " | grep -v grep \
    | sed -E 's|^ *([0-9:-]+) .* ([^ ]+\.lean) -o .*|  \1  \2|; s|'"$root"'/||' | sort -r
  sleep 2
done
echo "the build finished"
