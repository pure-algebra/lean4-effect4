# Shared entry capability receipt

The shared program relation now proves the failure capability bound at every typed entry.
The unit-input judgments retain their type-only statements.
The original reachable typing endpoint still needs its ambient runtime instance.

Base: `c86b1a86a`, after shared exit signature `2b974a2fc`.
Proof role: preservation dependency of `typed-state-reachable`, R4 and R9.
Scope: owner-approved success and failure guarantees, decisions rows 117 and 349.
Evidence status: checked shared proofs, actual provider producer and refusal controls.

## Existing shared structure

`ProgramArrow` receives one world-independent `Entry : Input → Object → Prop` parameter.
Each existing constructor retains that entry premise.
`ProgramArrow.entry` reads it without another code traversal.
World transport and program closing retain the same premise.

The unit instance uses `True`.
The ambient instance uses the failure guarantee below the available row.
Default constructor proofs apply only to the unit instance.
Ambient constructors supply their actual bound explicitly.

`Contracts.StackArrow` is the existing `Contracts.Path` over annotated frame arrows.
`Contracts.SavedArrow` generalizes the existing current-code and saved-path relation.
`SavedOk` becomes its unit-input alias with the same outward statement.
`savedOk_mono` uses the shared annotated world transport.
No new stored syntax, world, service table or evaluator appears.

`Context.ambient_entry` exposes the current entry bound.
`Context.AmbientSaved` instantiates the same saved relation at ambient positions.
The complete runtime host relation and queued delivery instance remain next.
The existing registration arrows still need their annotated position instance.
The source provider restoration still needs the existing compiled region instance.

## Actual producer and helper scope

The provider keeps the previous services through the existing right-biased merge.
`provider_entry` consumes previous runtime coverage and strong supplied-context membership.
It uses `Provision.satisfies_merge_left` to discharge the entry bound after the actual setter.
It retains declared service carriers and fitting service values.

The newly introduced internal setter helper gains:

```lean
kept : Row.Subset available ctx.services.keysRow
```

Its earlier completion-only statement permits a raw setter to remove guaranteed failure services.
`EntryCapabilityAfter.lean` rejects that exact boundary.
This helper restriction affects no frozen type-only header or original scenario statement.
A search finds no frozen contract or registry pointer naming this helper.
Actual source providers discharge the restriction from their real merge.
Captured restoration must discharge it from the actual captured context.
No runtime failure is assumed to restore the entry context.

## Controls and commands

`EntryCapabilityBefore.lean` compiles at retained commit `c86b1a86a` before the refinement.
It admits a successful completion with an unsupported failure row.
Its retained bytes document the old helper boundary; it is not a current battery.
`EntryCapabilityAfter.lean` proves that the refined relation refuses that same unsupported row.
It also rejects a raw setter that drops the guaranteed failure services.
`ExitDemandConsumer.lean` retains the actual setter and loop-top interruption equations.

Run:

```sh
LEAN_NUM_THREADS=3 lake build Effect4.Laws.Program.Typed.Context Effect4.Laws.Program.Typed.Stack Effect4.Laws.Program.Typed.Adequacy
LEAN_NUM_THREADS=3 lake env lean -DwarningAsError=true docs/research/2026-10-11-machine-models/codex/context/EntryCapabilityAfter.lean
LEAN_NUM_THREADS=3 lake env lean -DwarningAsError=true docs/research/2026-10-11-machine-models/codex/context/ExitDemandConsumer.lean
```

Result: 472 jobs pass; both controls pass with no output.
The audit covers Contracts, Membership, Residual, Seq, Context, ExpandFix, Stack and Adequacy.
Result: 1,595 declarations within `[propext, Quot.sound]`, zero goals and zero modulo declarations.
`git diff --check` passes.

Changed sources: Typed/Contracts, Typed/Residual, Typed/Seq and Typed/Context.
The coordinator's central Codegen.Types refusal remains outside this checkpoint.
No Machine module changes, original scenario assumptions or behavior gates occur in this slice.
The latest primary consolidation audit section is 2026-10-11 13:45.
