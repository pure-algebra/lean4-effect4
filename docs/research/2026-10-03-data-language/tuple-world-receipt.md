# Tuple world membership and handle containment

The tuple core proof slice is checked against the combined source.
It requires no weakened theorem premise and no new trust exception.
The coordinator must add both new fixtures to the test root; target structural proofs remain a separate slice.

Base: `c101f5cf19a88cbf13182111618ddf6070789259`.
Proof head: `3fa0e208cbdcb7a4606c62d326af718f886339ea`.
Branch: `codex/tuple-proof-completion`.
Worktree: `/Users/pooks/.codex/worktrees/data-admission/lean4-effect4`.
The earlier source, checker and coarse proof receipts remain the evidence for those stages.

## Proof placement and consumers

The five-part placement is in `tuple-brief.md`, including the two direct consumers found by the combined check.
All these declarations serve existing claims; this slice adds no claim registry or ledger mechanism.

| Declarations | Existing claim and consumer | Exact reach and limit |
| --- | --- | --- |
| `Typed.FitsAll.tuple`, `tupleItem_fits`, `tupleAt_fits`, `tuple_project_fits`, `tuple_typeAt_fits` | Store Typing & Value Membership; `denote-typed`; `atomFits`, `evalTerm_fitsAll`, `evalTerm_progress` | Same world and fitted input values. A position accepted by every normalized tuple alternative returns an actual fitting value. No scheduler or host progress. |
| Tuple cases of `atomFits`, `atom_progress`, `evalTerm_fitsAll`, `evalTerm_progress` | `denote-typed`, M5 and R3 | Existing signature and environment premises remain. Construction covers arbitrary argument lists; projection keeps the exact natural index. |
| `Val.tupleAt?_mem`, `tupleAt_keys`, `tupleAt_handles`; native and term consumer cases | Residual Program Typing; `straight-meaning-typed` through `RawHandles.evalTerm_handles`, `Denote.evalTerm_validIn`, `sound`, `meaning_typed`; decoded keys also serve R4 consumers | Successful raw evaluation, with no typing premise, introduces no new handle or decoded key. No allocation, finalization or direct M7 conclusion. |
| Record-tag case of `Denote.Decision.decide_validIn` | `straight-meaning-typed` through `TypedAt.bound` and `Denote.sound` | Either branch binds the unchanged whole input. The existing validity premise and conclusion remain; no claim about branch reachability. |

The normalized type rule ignores explicit bottom only.
It does not decide general inhabitance.
The type rule refuses list and unknown types as tuple targets.
Projection reads a plain list frame, not a list-view snapshot.
The existing straight-meaning theorem still covers its stated straight fragment and empty row table.
These proofs make no claim about target execution or whole-machine observations.

## Commands and results

The first combined command built the new membership and handle proofs.
It then found two missing cases: `tupleAt` in `Typed.RecordOperations.evalTerm_fitsAll`, and `recordTag` in `MeaningSound.Decision.decide_validIn`.
The coordinator approved both direct repairs.
The same command then passed, with 410 jobs:

```sh
LEAN_NUM_THREADS=3 lake build Effect4.Laws.Program.Typed.Membership Effect4.Laws.Program.Typed.Denotation Effect4.Laws.Program.Handles.Term Effect4.Laws.Program.MeaningSound
LEAN_NUM_THREADS=3 lake env lean -DwarningAsError=true Test/Program/TupleMembership.lean
LEAN_NUM_THREADS=3 lake env lean -DwarningAsError=true Test/Program/TupleHandles.lean
```

- `TupleMembership`: passed three theorem applications and eight axiom queries.
  A concrete declaration table establishes the handle premise; a negative control rejects an undeclared reference.
- `TupleHandles`: passed two finite evaluation guards and seven axiom queries.
  Construction retains both raw handles, and projection retains only the selected value's handle.
- All fifteen axiom queries reported exactly `[propext, Quot.sound]`.
- Eleven existing theorem headers were compared with the base and are unchanged: `atomFits`, `atom_progress`, `evalTerm_fitsAll`, `evalTerm_progress`, `nativeAtom_keys`, `evalTerm_keys`, `nativeAtom_handles`, `evalTerm_handles`, `Decision.decide_validIn`, `sound` and `meaning_typed`.
- `git diff --check` and `git diff --cached --check`: passed.
- The focused language check passed for the brief after replacing an ambiguous use of “preserved” with the concrete draft-saving fact.

The membership queries cover `FitsAll.tuple`, `tupleItem_fits`, `tuple_project_fits`, `tuple_typeAt_fits`, `atomFits`, `atom_progress`, `evalTerm_fitsAll` and `evalTerm_progress`.
The handle queries cover `tupleAt_keys`, `tupleAt_handles`, `RawHandles.nativeAtom_handles`, `RawHandles.evalTerm_handles`, `Denote.evalTerm_validIn`, `Denote.Decision.decide_validIn` and `Denote.meaning_typed`.
Their transitive dependencies include the unqueried local projection helpers.

Logs: `/private/tmp/tuple-final-build.log`, `/private/tmp/tuple-final-build-2.log`, `/private/tmp/tuple-membership-fixture.log` and `/private/tmp/tuple-handles-fixture.log`.
The first log is the initial failing check; the second is the successful retry.
No full sweep, module-closure gate or whole-root axiom gate was run in this seat.

## Changed files and integration

Proof files:

- `src/Effect4/Laws/Program/Typed/Membership.lean`
- `src/Effect4/Laws/Program/Typed/RecordOperations.lean`
- `src/Effect4/Laws/Program/Typed/Denotation.lean`
- `src/Effect4/Laws/Program/Handles/Term.lean`
- `src/Effect4/Laws/Program/MeaningSound.lean`

Fixtures: `Test/Program/TupleMembership.lean` and `Test/Program/TupleHandles.lean`.
Documentation: the updated tuple brief and this receipt.
No root import, target, generated file, manifest, decision register or build configuration changed.
The coordinator adds `Test.Program.TupleMembership` and `Test.Program.TupleHandles` to `Test/All.lean`.
All changed law modules already belong to the existing law graph.
Target structural checks and later integration gates remain coordinator-owned.

The original `codex/data-admission` branch remains at `e66b4c99`.
Its pending drafts have exact copies under `/private/tmp/effect4-tuple-proof-save` and scoped stash `e0b35cdde146b3089b16b82bde2668f464dbb3e3`.
The integrated FormationContract file is byte-identical to the saved draft, so it required no reapplication.
No draft was discarded and no push was run.
The shared Lean lane was released directly to the target proof seat after the final fixture.
