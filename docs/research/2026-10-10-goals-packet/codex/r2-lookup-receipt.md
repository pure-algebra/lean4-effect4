# Recover the first lookup across message words

The lookup law needs no uniqueness premise. The actual message reader also checks a machine with duplicate ids.

## Placement

- Concept: reactive-scheduling, R11, the proposed `command-moves` structure claim.
- Helper: `InterferesWithLookup.backward_lookup` in `src/Effect4/Laws/Program/Interference.lean`.
- Consumer: Timeout command assertions after settlement messages.
- Reach: forward first lookups and the existing birth interval, with an unchanged allocation counter.
- Limit: this proves lookup transport. It proves no progress, numeric invariant, or host agreement.

The unchanged counter excludes births. The forward first-lookup law then selects the predecessor of the final first lookup.
The proof does not invert an edit or assume unique ids.

## Evidence

Base: `68f3808d25e1c292e610f8f88864fd590ba480fd`.

Commands:

```sh
LEAN_NUM_THREADS=3 lake build Effect4.Laws.Program.Interference
LEAN_NUM_THREADS=3 lake build Effect4.Laws.Program.CommandFrames Effect4.Laws.Program.NativeEvaluation Effect4.Laws.Program.Guard.Messages Effect4.Laws.Program.Guard.NativeStateMotion Effect4.Laws.Program.Guard.ReturnCommands Effect4.Laws.Program.Guard.Settle Effect4.Laws.Program.Guard.Core Effect4.Laws.Program.ReleaseCustody.NativeMachineShape Effect4.Laws.Program.StackRegion
LEAN_NUM_THREADS=3 lake env lean -DwarningAsError=true docs/research/2026-10-10-goals-packet/codex/R2LookupReader.lean
git diff --check
```

The module build passes, with 338 jobs. The direct consumers pass, with 450 jobs.
The reader and duplicate-id control pass. `R2LookupReader.out` records 241 declarations within `[propext, Quot.sound]`, with no goals.
The diff check passes. Executable code does not change.

Changed files: the helper module, `R2LookupReader.lean`, `R2LookupReader.out`, and this receipt.
The Timeout numeric producer and the behaviour sweep remain open.
