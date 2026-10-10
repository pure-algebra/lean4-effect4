# Polarity review and graph merge checkpoint

Retain structural parameter occurrence when consolidating the membership fold.
The scalar polarity fold cannot reproduce `Ty.valueVars` on every `Ty`.
The checked witnesses are in [MembershipProbe.lean](MembershipProbe.lean).
This finding concerns the proposed connector, not the proved subtyping laws.

## Reviewed state

| Item | Commit | Evidence |
| --- | --- | --- |
| Initial polarity landing | `044aa8f481a660d1d87d37f8475d4183cda384fc` | Independent source reviews, narrow build, finite probes, and module audit |
| VAR-2 proof | `cd61d93378275c276a2c0206a8391b881b1f9864` | Independent source review, narrow build, finite probes, and module audit |
| Promoted gate tables | `87a17323d14d15ae6aebd6456c65b268ac3d7cf0` | Pinned table comparison |
| Graph merge | `8a876482d0cb8600a4b186f1fdeee47f29607a24` | Six implementation files equal the reviewed graph branch |
| Earlier graph review | `86d72c1062d0b63f51f4d8b55b194c48fafd8863` | Existing graph support packet |
| Earlier CX review | `41ec1e0c1d55f05393f3b4e7f938a5d87f7a6214` | Earlier refusal review packet, local commit `8d0dfb652efec437f7691d28ac279d3f090fddaa` |

The first review base is the graph merge.
A follow-up checks the VAR-2 landing at `cd61d9337`.
Only this review directory changes.
No production file, owner ruling, compiler pin, or implementation session changes.
No push or merge occurs in this review.

Claude reports the polarity build and graph merge in the bounded repository session tail.
The session has cwd `/Users/pooks/Dev/lean4-effect4`.
This review independently checks the source and the commands below.
Claude owns the ongoing host-protocol investigation and `TyView.lean` changes.

## Findings

### POL-MEMBERSHIP: the proposed scalar connector loses required information

**Role:** proposed compatibility connector.
**Evidence:** finite evaluation over every scalar reading of the two positions used by the witnesses.
**Scope:** the VAR-1 membership connector in `docs/research/2026-10-10-openai-math-type-systems/brief.md`.

`Ty.valueVarsAlg` retains two facts in `src/Effect4/Laws/Program/TypeAlgebra.lean`.
Its first fact records whether any parameter occurs.
Its second fact records the existing membership premise.
An opaque application ignores argument types for membership but retains their structural occurrence.
A surrounding cell checks that retained occurrence.

| Type | Existing `Ty.valueVars` |
| --- | --- |
| `refOf (var 0)` | false |
| `app "Opaque" [var 0]` | true |
| `app "Opaque" [refOf (var 0)]` | true |
| `refOf (app "Opaque" [var 0])` | false |

`MembershipProbe.lean` checks all sixteen cell/application readings of `HeadReading`.
Each reading disagrees with at least one row.
A positive control reproduces the first three rows with invariant cells and bivariant application arguments.
The last row then disagrees.

**Consequence:** proving the brief's exact scalar connector wastes effort.
Discarding the old occurrence fact changes the premise used by existing membership proofs.

**Smallest action:** retain the paired summary while sharing the traversal.
Alternatively, restrict the connector to a named fragment without the conflicting nesting.
Keep the existing `fits_instantiate_widens` statement in `src/Effect4/Laws/Program/Typed/Membership.lean` unchanged.
The proof outline is in [PROOF-DAG.md](PROOF-DAG.md).

This is not a counterexample to `Ty.sub_instantiate_polarity`.
No runtime or TypeScript result follows from these four types.

### POL-CENSUS: derive the inspected parameters from each answer

**Role:** protection of a finite census.
**Evidence:** current-table coverage control and a synthetic negative control.
**Scope:** `answerAboveCo` in `Test/Program/RowPolarity.lean`.

The census checks the fixed indices `[0, 1, 2]`.
The current tables use only `[0, 1]`, as measured by [Probe.lean](Probe.lean).
A synthetic answer `refOf (var 3)` passes the current filter despite its invariant occurrence.

**Smallest action:** use `answer.varsOf.any` to select the indices.
The local replacement agrees on every current representative and detects the synthetic case.
This change removes a separate bound that future authors must remember.
It reveals no faulty current built-in row.

`NativeOp.spelled` in `src/Effect4/Program/Native.lean` contains representatives.
Its `Deferred.make` representative uses `nat` for both explicit types.
A statement about every explicit instance needs its closed-type premises.
Keep supplied tables and definition blocks outside this finite census.

### POL-SUFFICIENCY: polarity supplies a sufficient condition

The battery says answers grow with bindings exactly where their polarities are co or bi.
That sentence is too strong for raw types.
`union unknown (refOf (var 0))` has invariant polarity.
The checked `nat` and `int` instances relate in both directions despite failing the invariant binding premise.

**Smallest action:** replace the necessity wording with a sufficient-condition statement.
The VAR-2 theorem already has that conditional form.

### Proof support and smaller limits

The subtyping reading matches the inspected `Ty.sub` arms.
The finite instantiation probe finds no counterexample among combinations satisfying its premise.
`Ty.sub_instantiate_polarity` is a planned goal at the initial landing.
Claude proves the same statement in `cd61d9337` during this review.
The follow-up build and module audit pass.
The audit reports no planned goal or declaration depending on one.
The proof reuses the generated argument view and its subtyping connector.

The bounds theorem returns `subN` comparisons.
The proved VAR-2 statement expects raw `sub` comparisons.
[NormalizeProbe.lean](NormalizeProbe.lean) checks the proposed normalization bridge and retains a control against reversing that implication.
[PROOF-DAG.md](PROOF-DAG.md) names the existing connectors and the small missing helpers.

`Var4.semiring_laws` describes a preorder but omits transitivity from its conjunction.
`Var4.le_trans` is separately proved in the same module.
Add it to the bundle or narrow the docstring.
This is a statement-packaging issue, not a missing transitivity proof.

The TypeScript research fixture discards the result of `Ref.set` before calling `Ref.get`.
The Lean `pAtoms` returns the row's result.
DI-98 records that these result columns differ: the machine returns the cell, while rc.112 returns `void`.
The handwritten fixture supports its numeric call sequence, not whole-program result agreement.
This review runs no TypeScript compiler.

## Graph and gate observations

[review_tables.py](review_tables.py) compares pinned Git objects and writes [table-and-merge-review.json](table-and-merge-review.json).
The six merged graph implementation files equal the previously reviewed versions byte for byte.
The existing graph packet therefore describes those implementations.
This comparison does not reproduce the merged build or rendering checks.

The target selection adds `pQueueService` and `pSemaphoreService` and removes no program.
The corpus table changes only diagnostic text in its changed rows.
Its acceptance and execution columns stay unchanged.
Three diagnostic-table verdicts move from `refused-silent` to `refused-unmapped`.
That gate previously excluded advisory truthiness codes from its verdict.
The new type errors participate in its verdict.
The tuple row keeps its status and changes its observed type signature and explanation.

These are table and source observations.
Claude's reported external gate runs are not reproduced here.

## Verification

| Command | Result |
| --- | --- |
| `LEAN_NUM_THREADS=3 lake build Test.Program.RowPolarity ProofGraph.AxiomAudit` | Pass; [build.log](build.log) |
| `LEAN_NUM_THREADS=3 lake env lean docs/research/2026-10-10-polarity-overwatch/Probe.lean` | Pass; [probe.log](probe.log) |
| `LEAN_NUM_THREADS=3 lake env lean docs/research/2026-10-10-polarity-overwatch/Audit.lean` | Pass; [audit.log](audit.log) |
| `LEAN_NUM_THREADS=3 lake build Effect4.Laws.Program.TypeAlgebra` | Pass; [membership-build.log](membership-build.log) |
| `LEAN_NUM_THREADS=3 lake env lean docs/research/2026-10-10-polarity-overwatch/MembershipProbe.lean` | Pass; [membership-probe.log](membership-probe.log) |
| `LEAN_NUM_THREADS=3 lake build Effect4.Laws.Program.Template` | Pass; [normalize-build.log](normalize-build.log) |
| `LEAN_NUM_THREADS=3 lake env lean docs/research/2026-10-10-polarity-overwatch/NormalizeProbe.lean` | Pass; [normalize-probe.log](normalize-probe.log) |
| `python3 docs/research/2026-10-10-polarity-overwatch/review_tables.py` | Pass; [table-and-merge-review.json](table-and-merge-review.json) |

The initial and follow-up audits check only `Effect4.Program.Polarity` and `Effect4.Laws.Program.Polarity`.
The initial output records 85 declarations within `[propext, Quot.sound]`, zero modulo planned goals, and one planned goal.
The follow-up output records 125 declarations within the same allowance, zero modulo planned goals, and zero planned goals.
The follow-up build and finite probe pass on `cd61d9337`.
Their commands and outputs are in [var2-verification.json](var2-verification.json), [var2-build.log](var2-build.log), [var2-audit.log](var2-audit.log), and [var2-probe.log](var2-probe.log).
This is not an audit of the whole library or M7.

The finite probe checks 1,944 combinations, of which 908 meet its premise.
All 908 satisfy its conclusion.
The membership probe checks sixteen readings.
The normalization probe checks 24 lookups and 36 instantiation comparisons.
These counts come from the retained logs.

The initial membership probe uses a reserved identifier and fails to parse.
The corrected file passes.
The initial failure remains in [membership-probe-initial.log](membership-probe-initial.log).
No failed result is counted as evidence for the finding.

## Checkpoint

The reviewed polarity checkpoint advances to `cd61d93378275c276a2c0206a8391b881b1f9864`.
The reviewed graph integration checkpoint is `8a876482d0cb8600a4b186f1fdeee47f29607a24`.
The intervening host-protocol runner change receives only source inspection here.
Its reported external runs are not reproduced.
The most recent CX source review remains `41ec1e0c1d55f05393f3b4e7f938a5d87f7a6214`.
The earlier refusal projection, module-layer typing, and call-ownership findings remain open and unchanged.
Their evidence stays in the earlier CX refusal review packet.

The new next actions are the membership summary correction and source-derived census indices.
The normalization outline connects the proved VAR-2 statement to the next row consumer.
