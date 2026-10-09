# Ref model and native operation receipt

The thirteen native operation laws observe replies and final stores, under encoded inputs and successful callback evaluation.
The model records optional writes, but final-store equality does not expose write events.
The coordinator must retain that distinction when integrating the callback bridge and semantics registry proposal.

Base: `b8b4099eb6516f59d4380f8a8bdcb488332adeee`.
Code head: `a34d33b223d9f79646ba800b9ccf160e4a90dd71`.
Branch: `codex/ref-model`.
The worktree is `/Users/pooks/.codex/worktrees/module-folds/lean4-effect4`.
The branch retains the earlier `codex/module-folds` branch and its ignored files.

## Changed files

| Path | Content |
| --- | --- |
| `src/Effect4/Library/Ref/Model.lean` | Independent generic model, with replies and optional writes |
| `src/Effect4/Laws/Library/Ref/Operations.lean` | Thirteen operation laws and four shared helpers |
| `Test/Program/RefModel.lean` | Numeric and handle readers, optional branches, and negative controls |
| `docs/research/2026-10-08-ref-model-receipt.md` | This receipt |

The model imports no step or machine implementation.
Its definitions transcribe latest (Effect 4.0.1), under `vendor/effect-4.0.1/src/Ref.ts`, with source lines beside each definition.
`Model.Result` holds values, never a callback or program syntax.
The operations remain the existing native rows and authoring forms.

`Model.set` returns a supplied backing-cell identity.
Latest's implementation returns the backing MutableRef through `MutableRef.set`, although Ref.set's declaration says void.
The model makes no outer JavaScript object identity claim and does not amend DI-98.
`Model.modifySome` accepts `B × Option A` and writes the old value on None.
Optional update operations perform no write on None.

## Proof placement

The Ref catalogue plan places these obligations before their proofs.
The proposed question is `ref-steps-agree`, with role simulation and concept `translation-simulation`.
Each declaration carries requirement R10.

| Declaration group | Required property and consumer | Reach and hypotheses | Limits | Requirement |
| --- | --- | --- | --- | --- |
| `make_agrees` | Initial cell allocation; Ref callers | Every exact image and initial value; allocation appends one cell | No whole run or host allocation spelling | R10 |
| `get_agrees`, `set_agrees`, `getAndSet_agrees`, `setAndGet_agrees` | Native operation agreement; Ref callers and keyed cells | One allocated cell holding the encoded value | No scheduling, write-event observation or host object identity | R10 |
| `update_agrees`, `getAndUpdate_agrees`, `updateAndGet_agrees` | Pure callback agreement; typed Step callback bridge | Encoded held value and callback evaluation to the encoded next value | No arbitrary callback, exception or reentrant mutation | R10 |
| `updateSome_agrees`, `getAndUpdateSome_agrees`, `updateSomeAndGet_agrees` | Optional callback agreement; typed Step callback bridge | Encoded held value and exact option callback result | No write-event observation or mutable payload aliasing | R10 |
| `modify_agrees`, `modifySome_agrees` | Separate reply and next-value agreement; callback bridge and SynchronizedRef | Arbitrary exact images for A and B; successful exact pair evaluation | No allocation inference from typing or whole-run agreement | R10 |
| `kernel_agrees` | Native kernel connector; twelve operation laws | Existing kernel row, held value, encoded reply and optional write | Its optional-write premise does not add write events to the result | R10 |
| `decode_option`, `decode_modifySome`, `encode_getD` | Exact callback shape equations; optional operation laws | Every exact image and option or callback pair | No typing or reply admission | R10 |

All declaration names in the table belong to `src/Effect4/Laws/Library/Ref/Operations.lean`.
The consumer bridge will connect Step reading and typing to these callback premises.
Allocation remains a separate law.
The coordinator owns the semantics registry addition and root imports.

## Verification

The following focused commands pass:

```text
LEAN_NUM_THREADS=3 lake build Effect4.Library.Ref.Model Effect4.Laws.Library.Ref.Operations
Build completed successfully (257 jobs).

LEAN_NUM_THREADS=3 lake build Test.Program.RefModel
Build completed successfully (753 jobs).

LEAN_NUM_THREADS=3 lake env lean /private/tmp/RefScopedTrust.lean
Ref scoped trust: checked 77 declarations; observed axioms [propext, Quot.sound]

LEAN_NUM_THREADS=3 lake build Tools.LoadPaths
Build completed successfully (4 jobs).

LEAN_NUM_THREADS=3 lake env lean /private/tmp/RefLoadReport.lean

git diff --cached --check
Exit 0.
```

The battery applies every operation law at a concrete numeric carrier.
It also applies get at an actual promise handle through the identity image.
Each optional operation has readers for Some and None.
The negative controls retain an unallocated cell, malformed callback shapes, and a mutant with the same reply but a different final cell.
Another control retains set's non-unit reply.
The model's controls distinguish skipping a write from writing back the old value.
These controls provide finite checks, not whole-run or host evidence.

The scoped trust script checks every declaration owned by the three new modules.
It rejects unsafe declarations and any transitive axiom outside `[propext, Quot.sound]`.
Its source is retained below for reproduction:

```lean
import Effect4.Laws.Library.Ref.Operations
import Test.Program.RefModel
import Lean

open Lean Elab Command
elab "#ref_scoped_trust" : command => do
  let env ← getEnv
  let modules := [`Effect4.Library.Ref.Model, `Effect4.Laws.Library.Ref.Operations,
    `Test.Program.RefModel]
  let mut count : Nat := 0
  let mut observed : List Name := []
  for (name, info) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    unless modules.contains env.header.moduleNames[idx.toNat]! do continue
    if info.isUnsafe then throwError "unsafe declaration: {name}"
    let axioms ← liftCoreM <| collectAxioms name
    for axiomName in axioms do
      unless [`propext, `Quot.sound].contains axiomName do
        throwError "{name} reaches refused axiom {axiomName}"
      if !observed.contains axiomName then observed := axiomName :: observed
    count := count + 1
  logInfo m!"Ref scoped trust: checked {count} declarations; observed axioms {observed.reverse}"
#ref_scoped_trust
```

The source scan reports:

```text
Ref source scan: 3 files; no refused trust or proof-style tokens
```

That scan rejects the prohibited trust words and proof fallbacks in the new Lean files.
It also rejects handwritten simp without only.
The scoped audit does not run the whole-tree axiom, module-closure or library-root gates.
Those integration checks remain with the coordinator.

## Reuse and authoring findings

The load report imports the operation laws, their battery, and `Tools.LoadPaths`.
Its command is `#load_report Effect4.Laws.Library.Ref`.
It measures this output:

```text
graph: 1621 theorems of the tree, 16 roots, 325 load-bearing
landing [Effect4.Laws.Library.Ref]: 17 theorems, 0 of them roots
  edges: 18 local, 1 tree, 28 core, 0 instance; reuse ratio 5%
  load-bearing: 0 of 17
  unconsumed (13): [Effect4.Ref.getAndSet_agrees, Effect4.Ref.getAndUpdateSome_agrees, Effect4.Ref.getAndUpdate_agrees, Effect4.Ref.get_agrees, Effect4.Ref.make_agrees, Effect4.Ref.modifySome_agrees, Effect4.Ref.modify_agrees, Effect4.Ref.setAndGet_agrees, Effect4.Ref.set_agrees, Effect4.Ref.updateAndGet_agrees, Effect4.Ref.updateSomeAndGet_agrees, Effect4.Ref.updateSome_agrees, Effect4.Ref.update_agrees]
  reached by a consumer, but by no root (4): [Effect4.Ref.decode_modifySome, Effect4.Ref.decode_option, Effect4.Ref.encode_getD, Effect4.Ref.kernel_agrees]
  joints: [Effect4.Machine.syncOpStep_eq_refStepOf ×1]
```

The direct-citation report counts the shared existing connector once.
It does not count that connector's transitive proof reuse in each public operation law.
It excludes anonymous battery examples from the authored theorem graph.
The semantics registry and downstream callback consumers have not yet been integrated in this worktree.
The report therefore marks the thirteen concrete battery readers' laws unconsumed.

- The twelve non-allocation laws reuse one native kernel connector rather than repeating store proofs.
- Four local helpers concentrate callback shape decoding and encoded optional defaults.
- The thirteen model definitions mirror the thirteen public effectful operations separately.
- Battery terms write the current-value position as zero.
- The assigned Step callback bridge will remove that positional work from callers.
- The model writes no structural record, identity table or second program representation.
- No proof raises the heartbeat limit.
- No value proof repeats the native store operation cases.

## Open limits

The callback evaluation premises remain conditional.
The typed callback bridge must discharge them from Step reading and typing.
The public operation observation contains final stores and reply, not a sequence of write events.
Arbitrary JavaScript callbacks, exceptions, external effects, reentrant mutation and mutable aliases remain outside the model.
No host execution, TypeScript compilation, whole-run theorem, semantics registry integration or root reachability check occurs in this seat.
The coordinator handles those assigned integration obligations.
The seat runs no full sweep and pushes no branch.
