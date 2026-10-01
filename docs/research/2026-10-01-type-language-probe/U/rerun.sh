#!/bin/sh
# Probe U: rebuild the probe modules and recheck every probe, one compiler at a time
# (LEAN_NUM_THREADS=1; warnings are errors). Each log ends with its exit code; every RED
# control is an asserted #guard inside its probe, so a green log means the red control held.
#   sh U/rerun.sh            from the worktree root
set -u
U="$(cd "$(dirname "$0")" && pwd)"
log() { name="$1"; shift; { "$@"; echo "exit $?"; } > "$U/logs/$name.log" 2>&1; tail -1 "$U/logs/$name.log" | sed "s/^/$name: /"; }
for m in Generic Faces Classes Reflect Enum; do
  log "olean-$m" "$U/run-lean.sh" olean "$U/probes/ProbeU/$m.lean"
done
for p in SpellingFolds MonoidFolds UnionSpine Reflections ReflectionsLcnfMl ReflectionsLcnfSemantics \
         EnumerationsSemantics EnumerationsMl EnumerationsTables EnumerationsTyVectors Laws KeyInjective; do
  log "$p" "$U/run-lean.sh" check "$U/probes/$p.lean"
done
exit 0
