# Map proof checkpoint

All six map atoms now reach Boolean membership, world-indexed membership, typed term evaluation, and both handle observations.
The coordinator must import the three map fixtures from `Test/All.lean` and run the reached case and target checks.
No root import or policy file was edited here.

Base: `6ffcf31c`. Branch: `codex/data-admission`.
The commit containing this receipt is the checkpoint head.
This base includes the already approved metadata dependency `404d893e`, locally `6ffcf31c`.
The world proof import path needs that source through `Codegen.Record` and `Api`.

## Integration order and ownership

The not-yet-integrated map commits, in order, are:

1. `bc781486`: machine operations, six appended atoms and raw controls.
2. `8f7077fd`: coordinator-generated AtomInventory.
3. `fb315a7b`: shared map readers and raw handle helpers, locally `71d9f9ae`.
4. `1ffd63ab`: all six schemes and the existing list-view repair.
5. `2a35fed4`: coordinator-generated PreludeAtoms.
6. The commit containing this receipt: the proof consumers and final fixtures.

The shared handle seat supplied `Laws/Machine/Map.lean`, the native cases in `Laws/Program/Handles/Term.lean`, and `Test/Program/MapHandles.lean`.
This seat applied and checked those patches with the typing consumers, as the coordinator requested.
The handle seat supplied the second-bind repair for the new list view.
This seat qualified two fixture annotations as `Store.Val` after the expanded imports made `Val` ambiguous.
The corrected handle brief and earlier receipt retain that seat's exact placement wording.

## Proof placement and unchanged statements

| Landed group | Concept and question | Immediate consumer and reach | Limits and requirement |
| --- | --- | --- | --- |
| `Typed.MapValues.encoded_of_all`, `sorted_pairs`, `canon_all` | Store Typing & Value Membership; helpers of `denote-typed` | Carrier reconstruction and canonical order, consumed by both map membership proof families; each payload predicate is retained | No independent membership judgment or scheduler claim; M5, R3 |
| `MapChecks.map_inv`, `write_canon`, `get`, `set`, `keys`, `entries`, `fromEntries` | Store Typing & Value Membership; helpers of `denote-typed` | Actual evaluation existence and `Val.hasTy` result membership, consumed by `NativeAtom.Sound` at every accepted instance of the existing schemes | Boolean shape membership does not establish world declarations; M5, R3 |
| `Typed.MapFits` helpers and the native atom cases | Store Typing & Value Membership; helpers of `denote-typed` | Actual evaluation existence and `Fits w` result membership at the same world; consumed by `atomFits`, `atom_progress` and `evalTerm_progress` | Retains each world and substitution premise; no scheduler progress or host execution; M5, R3 |
| Raw map handle helpers and native cases | Residual Program Typing; helpers of `straight-meaning-typed` | Successful evaluation retains only raw input handle frames, including unknown kind bytes; consumed through `RawHandles.nativeAtom_handles` and `evalTerm_handles` | Subset forgets order and multiplicity and proves no allocation existence; R3/R4 |
| Decoded key cases | The separate handle route under R4 | `nativeAtom_keys` and `evalTerm_keys`, then hooks and layers | No direct premise of the M7 exit-handle theorem is added |
| `Denote.NativeAtom.eval_validIn` proof migration | Residual Program Typing; helper of `straight-meaning-typed` | Uses raw handle containment to retain `Val.validIn` in the same stores after successful atom evaluation; the existing straight-line result remains `Denote.meaning_typed` | The latter still requires `Straight`, native typing and its empty initial environment/stores; no loop, scheduler or external-row theorem |

The statement headers of `NativeAtom.sound`, `Typed.atomFits`, `Typed.atom_progress`, `Typed.evalTerm_progress`, and `Denote.NativeAtom.eval_validIn` compare byte-for-byte equal to the previous checked record stage.
No typing or progress premise was added.
The last proof body shrank from 70 lines to 10 by reusing `RawHandles.nativeAtom_handles`.
Its old operation-by-operation case split is deleted.

Decision rows 125, 166 and 197 still bound the carrier, key order and duplicate policy.
Construction keeps the last repeated input entry.
Update binds the old and replacement types separately and returns their union.
The raw list-view repair is recorded in `map-scheme-receipt.md`: an empty fiber snapshot passes existing list membership and must construct the empty map.
The new proof does not bypass that input or narrow the old list judgment.

## Checks

```text
LEAN_NUM_THREADS=3 lake build Effect4.Laws.Program.Typed.Membership Effect4.Laws.Program.Typed.Denotation Effect4.Laws.Program.Handles.Term Effect4.Laws.Program.MeaningSound
PASS: 403 jobs

LEAN_NUM_THREADS=3 lake env lean -DwarningAsError=true Test/Program/MapTyping.lean
PASS: 14 finite guards, 7 theorem applications, 15 axiom queries

LEAN_NUM_THREADS=3 lake env lean -DwarningAsError=true Test/Program/MapHandles.lean
PASS: 12 finite guards, 19 axiom queries
```

The build includes the shared reader helpers, Boolean typing and world-indexed typing dependencies.
The two small shared typing helpers queried in `MapTyping` use `[propext]`.
Its other thirteen queried theorems use `[propext, Quot.sound]`.
Four queried reader/handle theorems in `MapHandles` use `[propext]`; its other fifteen use `[propext, Quot.sound]`.
No query reports another axiom.

Logs: `/tmp/map-final-build.log`, `/tmp/map-typing-fixture3.log`, and `/tmp/map-handles-final2.log`.
The earlier source checkpoint retains 30 raw operation controls and four source axiom queries.
The final typing controls include all six signatures, mixed updates, bad key types, empty-entry inference and the snapshot discriminator.
The membership examples keep present undefined, present option-none and nested declared references distinct.
A concrete declaration table witnesses the positive reference premise; a negative example refuses an undeclared reference.
The handle controls retain unknown kind bytes 254 and 255 and exercise actual term evaluation.
These controls remain finite evidence; the quantified theorems provide their stated general laws.

Earlier diagnostic runs needed explicit result witnesses and a world argument at a scalar inversion.
They also found the missing metadata source dependency.
Those are repaired in the final build above.
The first fixture attempts required an existing normalized-order reflexivity theorem and explicit value annotations.
No frozen statement changed during those repairs.

## Remaining boundaries

The coordinator owns the reached case census, root fixture imports and target checks.
The generated inventory and prelude were already checked separately by the coordinator.
No full battery, full axiom gate, TypeScript execution, JSON codec check or OCaml simulation ran in this proof checkpoint.
JSON and Schema faces remain separate slices.
The old pending `FormationContract.lean` edit was already handed to the coordinator and is excluded from this commit.
The Lean lane is released to the Schema seat.
