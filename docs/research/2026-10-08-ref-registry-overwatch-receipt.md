# Ref semantics registry overwatch

The semantics registry join closes the Ref operation claim's registration gap, with one prose correction still needed.
The optional-write sentence overstates the proved observation and misdescribes `modifySome` on None.
Production files and the active implementation session remain unchanged by this review.

Previous reviewed code: `84deccef2ec90340789e5d1831f6f0281d55d7b9`.
Reviewed head: `3d2a72585d543953980511850d8441bb0f9d3f79`.
Review branch: `codex/ref-registry-overwatch`.
Review worktree: `/Users/pooks/.codex/worktrees/module-design-review/lean4-effect4`.
The diff adds a proof bundle, its semantics registry entry, the generated report, and the State entry.
No operational definition or import changes in that diff.

## Active implementation

A bounded recent tail of session `9ebf38b2-8b2f-44e5-8fd9-2dc0cb5a1f50` identifies the primary repository as its working directory.
Claude integrates Ref and commits its semantics registry join at the reviewed head.
The session reports green integration and report builds.
This review reproduces only the narrow commands below, not those larger runs.

The primary tree then starts C3, moving the semantics registry and explanation tools.
During this review, C3 lands separately at `07adb0aa93121f0623039554f1b3fed7031f8d4f`.
That landing remains outside this pinned review.
A final source check confirms REF-REG-01 remains in its relocated semantics registry entry.
The semantics registry path at the reviewed commit is `tools/Tools/SemanticsRegistry.lean`.
C3 moves it to `tools/ProofGraph/Registry.lean`.
No message or instruction is sent to the implementation session.

## Finding REF-REG-01

Evidence kind: checked source and finite Lean controls.
Category: claim-description mismatch.
Priority: P2.
Owner: the semantics registry coordinator.

`Tools.Semantics.registry` describes `ref-steps-agree` in `tools/Tools/SemanticsRegistry.lean`.
The new title says an optional operation writes nothing on none.
`Tools.Semantics.buildReport`, in `tools/Tools/Semantics.lean`, exports this title to the report JSON.
The Markdown report lists the claim status and bundle type, without that title.

`Effect4.Ref.Model.modifySome`, in `src/Effect4/Library/Ref/Model.lean`, instead records `some oldValue` on None.
`Effect4.Ref.modifySome_agrees`, in `src/Effect4/Laws/Library/Ref/Operations.lean`, uses that model result.
Latest (Effect 4.0.1)'s `modifySome`, in `vendor/effect-4.0.1/src/Ref.ts`, calls `modify`, which assigns the selected value to the cell.
The three optional update operations skip that assignment on None.

The finite controls choose an allocated natural cell containing 5.
Both tested operations return 5 and leave the cell containing 5.
Their model write fields differ: `getAndUpdateSome` records none, while `modifySome` records `some 5`.
The positive Some control records `some 7`.
The new bundle's two relevant fields prove the actual reply and final-store observations at this cell.

The bundle observes replies and final stores, not write events.
Its theorem therefore cannot justify the title's blanket statement about absent writes.
Future documentation or mechanical tooling could wrongly classify `modifySome` as skipping its write.
The existing implementation needs no repair for this finding.

Replace the semantics registry title's write sentence with this observation limit:

> The laws compare replies and final stores under their stated allocation and callback-evaluation premises.
> They do not compare write events.

If operation detail is retained, name the three optional update operations explicitly.
State separately that `modifySome` writes the old value on None.
Regenerate the semantics report from the corrected semantics registry; do not edit the generated file by hand.
The source model and existing theorem statements retain their current behavior.

## Resolved registration gap

`Effect4.Ref.StepsAgree`, in `src/Effect4/Laws/Library/Ref/Operations.lean`, has one field for each of the thirteen effectful Ref operations.
Each field uses `type_of%` on its existing law.
This retains that law's quantified types, allocation premise, callback premise, and conclusion without copying its statement.
`Effect4.Ref.ref_steps_agree` supplies every field from the existing operation law.
The semantics registry now points to this bundle and the generated report lists it as proved.

The bundle adds no caller configuration or second program representation.
It groups existing proof obligations behind the semantics registry's one claim.
The callback connector still consumes `modify_agrees` directly in `src/Effect4/Laws/Library/Ref/Callback.lean`.
The join adds no schedule, host execution, or write-event theorem.
The existing named-input callback interface stays unchanged.

An independent GPT-6.1 Sol agent reviews the pinned source diff and reaches the same finding.
That agent performs no edits or builds.
The following reproduced evidence belongs to this review worktree.

## Verification

```sh
LEAN_NUM_THREADS=3 lake build Effect4.Laws.Library.Ref.Operations Tools.LoadPaths
LEAN_NUM_THREADS=3 lake env lean -DwarningAsError=true \
  docs/research/2026-10-08-ref-registry-overwatch.lean
```

The narrow build passes with 259 jobs.
The probe passes its two real bundle readers and all finite controls.
The scoped axiom check checks all 50 declarations owned by the operation-law module, including the bundle and its generated declarations.
The reached axioms are `[Quot.sound, propext]`, within the repository's permitted set.
The audit refuses missing declarations, empty discovery, exhausted traversal, and prohibited implementation forms.

The focused load report returns:

```text
graph: 1635 theorems of the tree, 17 roots, 351 load-bearing
landing [Effect4.Laws.Library.Ref.Operations]: 31 theorems, 1 of them roots
  edges: 31 local, 1 tree, 28 core, 0 instance; reuse ratio 3%
  load-bearing: 18 of 31
```

Its thirteen remaining unconsumed names are generated `StepsAgree` projections.
The report excludes anonymous readers, including this probe's actual uses of two projections.
The count describes this loaded environment and the tool's existing direct-citation model.
It measures no loss of proof reuse or architectural quality.
The twelve nonallocating laws still share the existing kernel connector.

This review reruns no TypeScript or OCaml checks because the delta changes no program or emitter.
The earlier Ref receipt retains that evidence at `84deccef`.
No full sweep, merge, push, semantics registry edit, or owner ruling occurs in this review.

## Checkpoint

- Reviewed through `3d2a72585d543953980511850d8441bb0f9d3f79`.
- Ref's semantics registry aggregation is checked; its previous registration gap is closed.
- REF-REG-01 remains open in the semantics registry description.
- C3 at `07adb0aa93121f0623039554f1b3fed7031f8d4f` awaits its separate slice review.
- The earlier wrapper, schedule, identity, and PartitionedSemaphore gaps retain their prior scope.

Changed review files are this receipt and `docs/research/2026-10-08-ref-registry-overwatch.lean`.
The receipt records bounded probes and a scoped axiom check, not general host compatibility.
