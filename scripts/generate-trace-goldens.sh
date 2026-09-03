#!/usr/bin/env bash
# Writes the Lean-expected traces of the harness family and the registered mask
# table into generated/traces/ (or the directory given as $1). Each file carries
# provenance rows (generator, regenerate command, inputs with digests, the
# effects pin) followed by the rows Generate.lean prints.
set -euo pipefail
repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
out="${1:-$repo_root/generated/traces}"
mkdir -p "$out"
cd "$repo_root"
lake build Effect4 >/dev/null
sha() { shasum -a 256 "$1" | cut -d' ' -f1; }
effects_rev="$(python3 -c "import json;m=json.load(open('lake-manifest.json'));print(next(p['rev'] for p in m['packages'] if p['name']=='effects'))")"
provenance() {
  printf 'format\teffect4-trace-golden-v1\n'
  printf 'generator\tscripts/generate-trace-goldens.sh\tsha256=%s\n' "$(sha scripts/generate-trace-goldens.sh)"
  printf 'regenerate\t./scripts/generate-trace-goldens.sh\n'
  printf 'input\tharness/trace/Generate.lean\tsha256=%s\n' "$(sha harness/trace/Generate.lean)"
  printf 'input\tEffect4/Meta/Derive.lean\tsha256=%s\n' "$(sha Effect4/Meta/Derive.lean)"
  printf 'input\tEffect4/Target/TypeScript/Trace.lean\tsha256=%s\n' "$(sha Effect4/Target/TypeScript/Trace.lean)"
  printf 'pin\teffects\t%s\n' "$effects_rev"
}
run() { lake env lean --run harness/trace/Generate.lean "$@" | grep -v '^warning: manifest out of date'; }
{ provenance; run masks; } > "$out/masks.tsv"
for program in $(run programs); do
  { provenance; run golden "$program"; } > "$out/$program.empty.tsv"
done
# The Flow-runner face of the same programs (the internal oracle), kept in a
# subdirectory so the host gate's program glob never sees them.
mkdir -p "$out/flow"
while IFS=$'\t' read -r program tape; do
  { provenance; run flow-golden "$program" "$tape"; } > "$out/flow/$program.$tape.tsv"
done < <(run flow-programs)
# Interruption as decisions (M2). Their own subdirectory under flow/, so the
# flow host loop's `flow/*.tsv` glob never sees them: they need the Interrupts
# service and `interrupt-tail.ts`, not `flow-tail.ts`. The `tape` header of each
# is the *interrupt* tape; none of these flows chooses.
mkdir -p "$out/flow/interrupt"
for program in $(run interrupt-programs); do
  { provenance; run interrupt-golden "$program"; } > "$out/flow/interrupt/$program.tsv"
done
# The `Scopes` family, likewise in a subdirectory of its own: it has its own
# generated module and its own tail (`scope-tail.ts`), so the straight-line
# host loop's `*.empty.tsv` glob must not see it.
mkdir -p "$out/scope"
for program in $(run scope-programs); do
  { provenance; run scope-golden "$program"; } > "$out/scope/$program.tsv"
done
# The `Layers` family (packet M4): its own generated module and its own tail
# (`layer-tail.ts`), so neither the straight-line glob nor the scope loop sees
# it. Its handles are rc.112 `Ref` and `Scope` objects, indexed by the tracer.
mkdir -p "$out/layer"
for program in $(run layer-programs); do
  { provenance; run layer-golden "$program"; } > "$out/layer/$program.tsv"
done
# The `Fibers` family (packet M3): its own generated module and its own tail
# (`fiber-tail.ts`), so the straight-line glob must not see it either. Each
# golden carries the tape its forks are answered from, in the `tape` header row.
mkdir -p "$out/fiber"
for program in $(run fiber-programs); do
  { provenance; run fiber-golden "$program"; } > "$out/fiber/$program.tsv"
done
# The job runner (packet: the first real program). Its own generated module
# (`job-fixture.ts`) and its own tail (`job-tail.ts`) over a real file-backed
# queue, so neither the straight-line nor the flow glob may see it. A golden is
# named `<program>.<golden>`: four goldens share the `jobRunner` body and differ
# in their queue seed and their tapes. Each carries *both* tapes in one `tape`
# header -- the choice sites are below `Effect4.Flow.interruptBase` and every
# interrupt site is at or above it, so the tail splits the list by site.
mkdir -p "$out/job"
while IFS=$'\t' read -r program golden; do
  { provenance; run job-golden "$program" "$golden"; } > "$out/job/$program.$golden.tsv"
done < <(run job-programs)
# The `Deferreds` family, kept in a subdirectory for the same reason as the
# flow goldens: the host gate's `*.empty.tsv` glob must not see them, because
# they run through `deferred-tail.ts`, not `tail.ts`.
mkdir -p "$out/deferred"
for program in $(run deferred-programs); do
  { provenance; run deferred-golden "$program"; } > "$out/deferred/$program.tsv"
done
# The `Refs` family: its own generated module and its own tail (`ref-tail.ts`),
# so the straight-line `*.empty.tsv` glob must not see it either.
mkdir -p "$out/ref"
for program in $(run ref-programs); do
  { provenance; run ref-golden "$program"; } > "$out/ref/$program.tsv"
done
echo "PASS wrote $(find "$out" -name '*.tsv' | wc -l | tr -d ' ') trace projections to $out"
