# Atomic and finalizer proof checkpoint

The two assigned whole-history goals remain open.
The checked changes establish local store transitions, initial stages and selected-source exclusions.
They do not establish the application stage history or unrestricted source uniqueness.

## Base and proof commits

Base: `5f07927c8cfc4481ec660a56cfeed993b5027cd4`.

| Commit | Changed paths | Checked result |
| --- | --- | --- |
| `8c07222ae` | `Test/Dogfood/Scenario/Atomic/Store.lean` | Initial request stages and actual decision/deposit store transitions |
| `c3a491b77` | `src/Effect4/Laws/Program/FinalizerPlacement.lean`, `src/Effect4/Laws/Program/FinalizerRun.lean` | Selected-source exclusions and their direct-fragment finalizer reader |

## Atomic placement and scope

Concept: store-typing, R4.
Question: the stage witness of `Atomic.Store.shop_stages`.
Consumers: `Atomic.counted` and `Atomic.committed`.

`load_stages` proves the initial stages for every native program and compilation budget.
`refModify_answer` connects the actual native answer to the evaluated pair and the actual heap write.
`decision_step` connects that answer to the admission or rejection count that the operation writes.
`deposit_step` proves the actual deposit appends its literal request event.
`deposit_step_amounts` connects the operation to the existing account observation, from an actual list history.

These declarations reside in `Test/Dogfood/Scenario/Atomic/Store.lean`.
Their environments and input record values remain arbitrary.
They establish no request progress, stage history or host behavior.
The shared request-stage witness through every actual command remains unproved.

## Finalizer placement and scope

Concept: scope-lifetime-finalization, R11.
Question: source uniqueness, through `FinalizerRun.once_placed_outside_census`.
Consumer: `FinalizerRun.once_placed_pushes_once`.

`forbidden_child_zero` proves that an excluded syntax edge contains no selected once-placed source opportunity.
`clear_loops` derives the existing loop restriction from `OncePlaced`.
`definition_body_zero` excludes every root definition body.
`definition_resolve_zero` retains every environment, tape, call stack and compilation budget.
These declarations reside in `src/Effect4/Laws/Program/FinalizerPlacement.lean`.

`once_placed_direct_pushes_once` consumes `clear_loops` in `src/Effect4/Laws/Program/FinalizerRun.lean`.
Its direct-fragment, finalizer-child, sequential-scope and race restrictions remain explicit.
It establishes the registration bound on that fragment, with no finalizer progress or host claim.

The unrestricted source statement remains unchanged.
No checked counterexample refutes it.
Repeated root-definition invocation does not supply the suspected counterexample: `OncePlaced` excludes the definition bodies.

## Remaining finalizer connection

The unrestricted proof needs selected-source opportunities in stored release programs and unlaunched race programs.
It also needs the actual parameter sites to retain their excluded-source property.

`SourceScope.Opportunities` assumes `ClearFinalizers` and assigns no selected opportunity to scope storage.
`PlaceFunding.NoQueue` requires zero race weight.
`ReleaseCustody.Execution.history` carries release custody only under its direct-fragment, sequential-scope and race restrictions.
Those restrictions prevent a direct composition for the unrestricted goal.

A proposed composition transfers selected opportunities into scope custody at acquisition registration.
It transfers them back into active source code at the recorded release start.
The race reading must transfer an unlaunched program's opportunity into its spawned fiber.
These are proposed proof connections, not checked declarations.

## Commands and results

All Lean commands use `/Users/pooks/Dev/lean4-effect4/scratch/lean-slot.sh`.

| Command | Result |
| --- | --- |
| `lake build Test.Dogfood.Scenario.Atomic.Store` | Passed, 1170 jobs |
| `lake build Test.Dogfood.Scenario.Atomic ProofGraph.AxiomAudit` | Passed, 1262 jobs |
| `lake build Effect4.Laws.Program.FinalizerPlacement Effect4.Laws.Program.FinalizerRun` | Passed, 607 jobs |
| `lake env lean scratch/AtomicFinalizerAudit.lean` | Passed, audit output below |
| `git diff --check` | Passed before the checkpoint commits |

The audit explicitly imports and names the three changed modules.

```text
#axiom_audit: 300 declarations within [propext, Quot.sound], 1 of them modulo planned goals; 2 planned goals
```

The planned goals are the original assigned goals.
The modulo declaration is the original unrestricted finalizer reader.
No runtime implementation, source language or stored value carrier changes.
No behavior gate result is claimed for this proof checkpoint.

## Source and custody transfers

The endpoint goals remain open after `b8f9f14ca`.
The source ledger distinguishes active and saved release continuations.
A registration push transfers the selected release descendant into custody.
A release-start push returns that descendant to its saved continuation.
The race ledger retains every unlaunched program and proves actual launch balance.
The layer projection reserves delayed user bodies through the existing primitive fold.
Definition and parameter redirects exclude the selected once-placed source.
The parameter-stack transport and runtime custody join remain open.

Changed proof leaves:

- `src/Effect4/Laws/Program/FinalizerSource.lean`
- `src/Effect4/Laws/Program/FinalizerPlaces.lean`
- `src/Effect4/Laws/Program/FinalizerRace.lean`
- `src/Effect4/Laws/Program/FinalizerControl.lean`
- `src/Effect4/Laws/Program/FinalizerLayerBody.lean`

`FinalizerRun.lean` imports those leaves through its checked dependency closure.

Checks:

- `scratch/lean-slot.sh lake build Effect4.Laws.Program.FinalizerRun ProofGraph.AxiomAudit`: passed, 619 jobs.
- `scratch/lean-slot.sh lake env lean scratch/AtomicFinalizerAudit.lean`: passed.
- Audit: 805 declarations within `[propext, Quot.sound]`; one modulo planned goals; two planned goals.
- `git diff --check`: passed.

These proofs change no machine behavior and establish no progress or host result.

## Reviewed command design

`SourceOpportunities.source_local` does not provide the unrestricted finalizer command producer.
Its history connector requires `Fragment`, and `PlaceFunding.Local` requires zero race weights.
`FinalizerPlaces.launch_balance` proves weighted launch accounting, but supplies no full command or history connector.
`FinalizerTransfer` accounts for native onExit frames and leaves scoped foreign-release custody separate.

The next finalizer slice should generalize `PlaceFunding`, rather than duplicate its command cases.
Split `NoQueue` into zero command/task weights and a `RacePrograms` interface.
The interface reads each race as the sum of its pending program weights.
`PlaceLedger.IterDebit`, `install_balanced` and `settle_balanced` already retain all places.
Reuse them instead of reducing funding to state and fibers.
Weighted launch consumes one pending program when its child starts.
Other race metadata edits retain programs, while race deletion can discard weight.
Retain reply permissions, and remove the zero-weight entrant permission from weighted launch.
Parameterize scoped custody by a `FinName → Nat` weight and sum that weight over close orders.
The selected descendant weight is `below q (capture.path ++ [1])`.
Its registration and release-start transfers cancel the source ledger's opposite transfers.
Old zero-race instances should use the same generalized command theorem.

The Atomic endpoint requires a joint stage, heap, frame, queue and snapshot invariant.
The earlier G2 proposal states no checked producer.
`Atomic.Store.Writes` already supplies the concrete decision, deposit, refill and cleanup primitive equations.
The stage producer should reuse those equations and `Guard.source_decision_lift` with `Lift.CoupledDecision`.
A store-derived frame world cannot retain stages lost during interruption.
The proof world must remain external and must advance jointly with pending reply and snapshot assertions.


## Contextual command and settlement slice

The endpoints remain open. These shared producers remove repeated transport proofs.

Commits `fe2125eb4` and `a9b26c660` retain one world across actual messages and settlement.
`ContextualMessages.Admitted` requires immutable admission for each addressed message.
Its producer reads the actual machine, generated commands and fiber lookup.
The unrestricted producer is its trivial-admission instance.
`Admitted.settle` composes installation, messages, owner rereading and the outcome producer.
`AnswerFlowGhostCommands` retains one world for native flow and the application postcondition.
Its administrative interface still requires unrestricted frame interruption.
Timeout uses the contextual admitted producer for its stronger running-frame authority.

Checks:

- `scratch/lean-slot.sh lake build Effect4.Laws.Machine.AnswerFlowGhostCommands`: passed, 227 jobs.
- `scratch/lean-slot.sh lake env lean scratch/GhostAudit.lean`: passed.
- Audit: 177 declarations within `[propext, Quot.sound]`; zero modulo goals; zero goals.
- `git diff --check`: passed.

## Atomic fact dependency slice

Commit `972b7012a` moves reusable facts into `Atomic/StoreFacts.lean`.
`Atomic/Store.lean` retains `shop_stages` and its observation consumers.
`Atomic/Writer.lean` and `Atomic/Writes.lean` import the fact module.
The stage history can now use their equations without importing its own endpoint.
No statement changes, and `WriterPhase.lean` remains untouched.

Checks:

- Store, Writes, WriterNative and Cleanup builds pass: 1263 jobs.
- `scratch/lean-slot.sh lake env lean scratch/StoreFactsAudit.lean`: passed.
- Audit: 354 declarations within `[propext, Quot.sound]`; zero modulo goals; one original goal.
- `git diff --check`: passed.

Overwatch F4 changes the next stage route.
The shared bare `Initialization` producer supplies the three reference identities.
The Atomic stage and Boolean facts join it through `withCoupledFact`.
Overwatch F2 supplies one predicate fold and compiler contract before another source walk.


## Shared predicate compiler closure

Commit `0e5a904fd` consolidates the leading-binding compiler walk.
`CodeClosure.Predicate.codeAlg` lifts name and thunk predicates through the generated runtime-code fold.
`CodeClosure.Code` retains a stable head for the named normalization rules.
`fold_and` uses `hom_eq_cata_prim`, rather than another constructor induction.
`CodeClosure.CompileContract` names local minted leaves and recursive-child transport.
`compile_closure` covers every source constructor and every fuel value.
It requires no direct-source fragment premise.
`AnswerSlots.compile_at` supplies a leading-binding contract and calls that closure once.
Its former compiler case list is removed.

`NativeScope.CodeAt` additionally couples registration callbacks to their actual producer bodies.
It also classifies cancellation names.
Those protections remain; the plain name/thunk predicate fold does not subsume them.
A future consolidation needs an enriched edge carrier or a separate coupling conjunct.
No source ownership, stage history or finalizer endpoint is claimed by this slice.

Checks:

- `scratch/lean-slot.sh lake build Effect4.Laws.Program.AnswerSlots.Actions`: passed, 391 jobs.
- `scratch/lean-slot.sh lake env lean -DwarningAsError=true Test/Program/CodeClosureBank.lean`: passed.
- The bank control accepts the named bank and retains the expected error without it.
- `scratch/lean-slot.sh lake env lean scratch/CodeClosureAudit.lean`: passed.
- Audit: 190 declarations within `[propext, Quot.sound]`; zero modulo goals; zero goals.
- `git diff --check`: passed.

The coordinator adds `Test.Program.CodeClosureBank` to `Test/All.lean`.
Existing AnswerSlots imports reach the shared proof leaves.

## Stable prefix consumer

The coordinator can integrate `9eb5f6312` after Queue's `AnswerSlots.Stable` interface.
The new `AnswerSlots.PrefixStable` supplies `prefixSpec` and `prefixLaws` for any direct source fragment.
The instance admits every value and cause while retaining `AnswerSlots.CodeAt bindings` in current and saved code.
Its saved edge is independent of the completed-fiber view.
Its installed finalizer reads the actual interpreter program and retains the native restore wrapper.
The instance reuses the existing callback laws and introduces no compiler traversal.

Placement: store-typing R4 and scope-lifetime-finalization R11.
Consumers: the common allocation-prefix adapter and the Atomic and Timeout history producers.
The interface supplies no allocation or history certificate itself.
Both assigned endpoints remain open.

Verification uses the serialized Lean slot from `/private/tmp/meanings-atomic`.
`lake build Effect4.Laws.Program.AnswerSlots.PrefixStable` succeeds with 393 jobs.
`lake env lean -DwarningAsError=true scratch/PrefixStableAudit.lean` audits both shared modules.
The audit reports 63 declarations, zero declarations modulo planned goals and zero planned goals.
`git diff --check` succeeds.

## Actual Atomic roles and admitted saved handlers

The coordinator can integrate `58b227212` and `7d19775dd` independently.
The Atomic history goal remains open.

`StageWorld` and `StageSource` land at `514bbdd48`.
The source facts connect actual decision branches, fork heads and spawned child identities.
The stage producers use the actual window, deposit and cleanup writes.
Their audit reports 161 declarations, zero declarations modulo planned goals and zero planned goals.

`RootBindings` lands at `58b227212`.
Its `fork_transition` joins the same actual spawned identity with the root's returned handle and next source point.
The actual callback updates the completed-fiber view before resolving that point.
The theorem retains the root phase and next-id hypotheses.
`lake build Test.Dogfood.Scenario.Atomic.RootBindings` succeeds with 1176 jobs.
Its audit reports 17 declarations, zero declarations modulo planned goals and zero planned goals.

`ContextualSavedFamily` lands at `7d19775dd`.
Its discard clause reads an explicit predicate on the actual recorded cause.
The existing shared pop proof carries this predicate through its existing recorded-cause equality.
The proof retains the actual delivered cause and actual saved suffix.
The existing unconditional family supplies the constant-admission instance.
The legacy `External` entry points remain wrappers over the common proof.
No second pop recursion lands.

The concrete reader constructs an admitted family whose cause class excludes typed failures.
The control proves that a fabricated typed pending cause prevents the corresponding unconditional family.
This control corrects no endpoint statement and supplies no source-history counterexample.
Timeout confirms that its actual recorded-cause invariant supplies the new premise.

The serialized build covers native history, PrefixStable and the Atomic role leaves with 1198 jobs.
The serialized build covers GhostCommands, CausePop and the admission control with 280 jobs.
The audit covers the contextual family, shared pop module, legacy history and control.
It reports 234 declarations, zero declarations modulo planned goals and zero planned goals.
`git diff --check` succeeds.
