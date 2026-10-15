# Protected finalizer constructor

The coordinator must import `Effect4.Laws.Machine.AnswerFlowProtected` from the Laws root.
This slice changes no root and closes no Timeout endpoint.

Base: `0a3d49223` on `codex/timeout-m3`.
The source change is `src/Effect4/Laws/Machine/AnswerFlowProtected.lean`.

`AnswerFlow.saved_protected_finalizer` serves scope-lifetime-finalization R11 and store-typing R4.
Its consumers are Timeout's numeric finalizer families and the initialized crew finalizer families.
It requires a classed exit and a total installed finalizer at every permitted future world.
It establishes the ordered saved-frame contract for the actual protected `onExit` frame.
It supplies no installed program, command producer, initialized history, or progress.

The theorem uses `SavedAt.mk` once.
The protected mask hook excludes the actual discarded-handler branch.
The theorem assumes no class for arbitrary discarded causes.
`AnswerFlowConstructors.saved_onExit` requires that stronger premise, so it cannot discharge this case.

| Command through the serialized Lean slot | Result |
| --- | --- |
| `lake build Effect4.Laws.Machine.AnswerFlowProtected` | Passed, 178 jobs |
| `lake env lean scratch/TimeoutProtectedAudit.lean` | The output below |
| `lake build Test.Dogfood.Proofs.HostTimeoutNumberPhaseFlow` | Passed, 1190 jobs; both finalizer families use the constructor |

```text
#axiom_audit: 1 declarations within [propext, Quot.sound], 0 of them modulo planned goals; 0 planned goals
```

The phase-flow consumer remains a work in progress outside this commit.
No host behaviour gate changes because the slice changes proof construction only.
