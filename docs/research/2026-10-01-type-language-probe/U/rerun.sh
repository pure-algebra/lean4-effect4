#!/bin/sh
# Probe U: rebuild the probe modules and recheck every probe, one compiler at a time
# (LEAN_NUM_THREADS=1; warnings are errors). Each log ends with its exit code; every RED
# control is an asserted #guard inside its probe, so a green log means the red control held.
#   sh U/rerun.sh            from the worktree root
set -u
U="$(cd "$(dirname "$0")" && pwd)"
log() { name="$1"; shift; { "$@"; echo "exit $?"; } > "$U/logs/$name.log" 2>&1; tail -1 "$U/logs/$name.log" | sed "s/^/$name: /"; }
# The generated module first: rerun the patched generator and refuse a changed output.
ROOT="$(cd "$U/../../../.." && pwd)"
R="docs/research/2026-10-01-type-language-probe/U"
cp "$U/generated/ProbeU/TyFoldExtras.lean" "$U/scratch-prev-extras.lean" 2>/dev/null || true
log gen-extras sh -c "cd '$ROOT' && LEAN_NUM_THREADS=1 lake env lean -M 4096 --run $R/patches/Fold.lean --extras --group TyFoldExtras --imports Effect4.Program.Fold --out $R/generated/ProbeU/TyFoldExtras.lean --namespace ProbeU Effect4.Program.Ty"
if [ -f "$U/scratch-prev-extras.lean" ]; then
  cmp -s "$U/scratch-prev-extras.lean" "$U/generated/ProbeU/TyFoldExtras.lean" && echo "gen-extras: idempotent" || echo "gen-extras: CHANGED"
  rm -f "$U/scratch-prev-extras.lean"
fi
log olean-TyFoldExtras "$U/run-lean.sh" olean-gen "$U/generated/ProbeU/TyFoldExtras.lean"
# The two tables: JSON data, emitted by the table emitter (a missing or extra row is refused).
log gen-tables sh -c "cd '$ROOT' && LEAN_NUM_THREADS=1 lake env lean --run $R/patches/TableGen.lean faces $R/tables/ty-faces.json $R/generated/ProbeU/FacesTable.lean && LEAN_NUM_THREADS=1 lake env lean --run $R/patches/TableGen.lean classes $R/tables/ty-classes.json $R/generated/ProbeU/ClassesTable.lean"
for spec in olean:Generic olean:Faces olean-gen:FacesTable olean:ClassRow olean-gen:ClassesTable olean:Classes olean:Reflect olean:Enum olean:Lowering olean:RecordTy olean-gen:RecordFold; do
  mode=${spec%%:*}; m=${spec#*:}
  if [ "$mode" = olean ]; then f="$U/probes/ProbeU/$m.lean"; else f="$U/generated/ProbeU/$m.lean"; fi
  log "olean-$m" "$U/run-lean.sh" "$mode" "$f"
done
# RED controls of the table emitter: a constructor with no row, a row for no constructor.
log gen-tables-red-missing sh -c "cd '$ROOT' && LEAN_NUM_THREADS=1 lake env lean --run $R/patches/TableGen.lean faces $R/tables/red-missing-row.json $R/scratch/red.lean"
log gen-tables-red-extra sh -c "cd '$ROOT' && LEAN_NUM_THREADS=1 lake env lean --run $R/patches/TableGen.lean classes $R/tables/red-extra-row.json $R/scratch/red.lean"
for p in SpellingFolds MonoidFolds UnionSpine Reflections ReflectionsLcnfMl ReflectionsLcnfSemantics \
         EnumerationsSemantics EnumerationsMl EnumerationsTables EnumerationsTyVectors Laws KeyInjective \
         RecordFoldReceipts; do
  log "$p" "$U/run-lean.sh" check "$U/probes/$p.lean"
done
exit 0
