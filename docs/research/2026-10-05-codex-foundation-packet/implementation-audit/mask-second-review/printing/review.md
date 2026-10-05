# Mask second note: TypeScript printing review

Recommendation: accept the single-body direction with the corrections below.
Evidence status: source review at `c3263529`; no Lean execution or new runtime probe.
Scope: the proposed printer, reader, saved type, and program paths.

## 1. Add the method separation proof

F5 understates the required proof work.
`Tpl.head?` returns no head for a method template (`src/Effect4/Codegen/Template.lean`).
`rowsApart` requires a reserved head for a rigid template before the raw row-call fallback.
Therefore the proposed restore row fails that condition, even after reserving `pipe`.
`table_apart` checks every earlier row against every later row within its family.
Both declarations live in `src/Effect4/Laws/Codegen/ReadPrint.lean`.

Add a method-specific reservation condition and its matching lemma.
Keep the restore row before the raw fallback and the transparent action row.
Verify separation against both rows and against every action template.
The existing layer method templates do not establish this case: their family has no raw row-call fallback.

The theorem statements may remain unchanged.
`read_print` requires `LawfulSpelling`, `Readable`, and successful printing.
`read_exact` requires `LawfulSpelling` and successful reading.
These equations establish program-syntax recovery, not target execution or module typing.
The declarations live in `src/Effect4/Laws/Codegen/ReadPrint.lean` and `src/Effect4/Laws/Codegen/Read.lean`.

## 2. Correct the body path

F3 compiles the false branch at `p.child 1`.
`Node.child` numbers node arguments only, excluding terms (`src/Effect4/Program/NodeLenses.lean`).
A `restore : Term → Eff → Eff` node therefore has its body at child zero.
Use child zero in both the direct branch and the action-body resolver.
Check a restore body containing a fork or layer reference, since these consumers resolve program paths.
The current `suspendBodyAt` follows this convention for selection (`src/Effect4/Program/Compile.lean`).

## 3. Reserve the saved type and bound annotation claims

A new `Val.hasTy` arm is not the entire opaque-type change.
Add the target to `internalHandleTargets` in `src/Effect4/Program/Typed.lean`.
Otherwise `externalHandleTarget` admits an external handle bearing the same target name.
That value conflicts with the proposed restore compiler, which expects a Boolean.
`internalHandleScan` and `findInternalHandle` use this reservation when checking external columns (`src/Effect4/Program/Columns.lean`).
Keep handle and normalized application membership consistent.

A named alias can print through `Types.ofTy` (`src/Effect4/Codegen/Types.lean`).
That fact does not establish annotated-program recovery.
`readArg` rejects local type annotations (`src/Effect4/Codegen/Read.lean`).
`leafReadable` excludes `optTy (some _)` (`src/Effect4/Laws/Codegen/ReadPrint.lean`).
Keep those limits explicit unless the slice deliberately changes them.

Require one emitted module containing the alias, its import, and a returned or stored saved value.
Check target typing and the intended checked-module path separately.
Add negative controls for Boolean use and external answers that invent the saved target.
Program-data serialization does not establish serialization of the target's callable saved value.
No concrete serialization contradiction was established by this review.

## 4. Keep the layer argument conditional

F2 establishes that duplicating an inline subtree creates distinct program paths.
It does not establish the stated memo result by itself.
`LayerTerm.ref` can preserve a shared target despite textual duplication (`src/Effect4/Program/Eff.lean`).
`resolveLayerWith` follows that target when using the memo map (`src/Effect4/Program/Compile.lean`).
The existing selection printer also prints both branches, so it does not itself collapse two sites.

Describe this as an identity obligation for a proposed collapsing printer.
A counterexample needs both branch visits within one memo-map lifetime and the target's allocation points.
Use an explicitly shared layer reference as the control.
The single-body constructor avoids duplicate program syntax without relying on an unmeasured memo divergence.
The classifier and extra-suspension arguments remain independent reasons for the direction.

## Queue amendment check

The current source addresses the three earlier model findings in `e5ae130d`.
`room` uses `Option Nat`, and `fit none n` admits all `n` values.
`unboundedBatch` and `unboundedClear` retain controls above the former one-million limit.
`clear` documents and checks its capacity-zero rendezvous behavior.
`accounted` checks whether departing waiting requests receive an emitted signal or answer directly.
`shutdownNamesNobody` retains the negative control that the former state properties missed.
These declarations live in `docs/research/2026-10-05-claude-lead/queue-contract/QueueContract.lean`.

The retained output contains eight results at 177156 runs and eight at 402234 runs.
Each result reports both tested Boolean properties as true.
This review inspected that output; it did not rerun the searches.
The added accounting concerns emitted signals, not their eventual delivery.

## Live edit at close

The note changes during this review, while HEAD remains `c3263529`.
F3 adds `Fits`, and the exclusions leave the Boolean-versus-handle carrier choice open.
These edits do not address the method separation, child index, or target reservation findings.
The receipt retains both note hashes; all other inspected source hashes remain unchanged.
