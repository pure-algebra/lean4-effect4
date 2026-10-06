# What dogfood now asks of the semantic model

Snapshot: `00b160d25d6929ab7ba3aa19cc00fa6fdcfa9674`, with a clean primary checkout at the initial read.
This is a source audit, not a new build or acceptance run.
`manifest.json` retains 49 exact source files.
`requirements.json` retains all thirteen requirement titles and open-parts lists, joined against the registry.

## Main finding

The missing foundation is the connection from local steps to scheduled public operations.
It is not another generic fold library, another program representation, or a wholesale repair of the typing model.

Queue, Semaphore, and Pool now have local agreement laws.
Queue also has public-operation typing and atomic-attempt connectors at actual minted scopes.
These results stop before a request's whole lifetime across waiting, notification, cancellation, and completion.
Dogfood now exercises precisely that missing connection.

No source inspected here establishes a contradiction in the chosen model.
Several broad claims would be false, and the tree already records their exclusions or counterexamples.
Those boundaries must remain visible when local results are composed.

## What already connects

### Typing is substantially ahead of scheduled module agreement

`m7_proved` is a theorem in `src/Effect4/Laws/Program/Typed/Commands/Clauses/All.lean`.
Its named M7 fragment uses a checked lawful source, closed requirements, an empty host table, and answer-free tapes.
It gives typed recorded exits, typed stores, and absence of a stuck machine.
It does not promise termination or successful completion.

The stronger `reachable_typed` theorem takes a checker equation and `AdmittedTape`.
The tape premise is ghost admission at each reached world, not a check the session has discharged.
`obs_typed` transports that result to the frame observation at the empty-table route.
`Results.exits_hasTy` then states typed recorded exits across program fragments, including scheduled programs and loops.
The open host bridge must not be described as an open M5 or M6 proof.

`AdmittedProgram.source` and `reachable_typed_admitted` connect public program admission to the proof-side source.
The service half of an application signature still has public-face limits in R1.
The nonempty-table operational connection is R6's separate DI-57 boundary.

### Module steps already reuse the same proof owners

`Modules.step_updates`, `step_keeps_cell`, and `cell_read` are in `src/Effect4/Laws/Modules/Store.lean`.
They join an elaborated step's reading and typing to one atomic cell operation.
`step_keeps_cell` needs the current cell's membership and a typed captured environment.
A model profile alone supplies neither.

Queue's `take_attempt_minted` and siblings already combine those facts with model agreement and concrete scope resolution.
Their owner is `src/Effect4/Laws/Modules/Queue/Ops.lean`.
The result includes the new cell, reply membership, and the ordered signals to post.
The initial cell membership and later allocated identities still belong to the wrapper relation.
The relation must connect model identities, live handles, current hints, and the typed world.

Queue's `Notified` records all model signals and their order.
It does not record whether a helper delivered one or which suspended continuation owns it.
Pool's relation explicitly leaves fiber-to-lease ownership and posted selections to its wrapper relation.
These are precise omissions, not lost data in the existing step theorems.

### Equality already has several legitimate observations

`StraightEq` compares an exit and the complete stores for every environment on the `Straight` fragment.
Its bind, handler, and finalizer congruences already exist.
`run_agrees` uses separate sufficient budgets for the two programs.
It excludes traces and executions cut by insufficient fuel.

`loopAgreement` instead assumes that a budgeted meaning finishes.
It gives a machine result beyond some sufficient bound on the `Looped` fragment.
It does not make arbitrary loops terminate.

`Machine.Obs` keeps every fiber's exit and the stores, omitting the trace.
`Beh_fuel_irrelevant` fixes the initial machine and tape and requires sufficient budgets.
`Suffices` does not mean every fiber has exited.
A public module relation may hide private cells only after naming the public requests, commits, replies, interruptions, and terminations.
Rows 79 and 230 already require that choice.

`Projects`, `Refines`, their composition laws, and observation factorization already live in `Laws/Machine/Refinement.lean`.
Reuse them where their operation and answer relation fits.
Do not infer a scheduled stuttering relation from their one-operation shape.

## The useful new learning from dogfood

### A notification has an owner and a lifetime

A Queue wake invites a retry; it reserves no message.
A blocked offer's wake can instead carry an answer already committed by another step.
Interruption before commitment and interruption after commitment must therefore have different observations.
`QueueTraces` retains both cases and the wrong withdrawal that takes a committed message back.
These are finite controls, not the general cancellation theorem.

The pending obligation moves through the cell, a command, a dispatcher task, and an accepted receiver continuation.
A stale hint must not discharge a newer wait.
The full relation must count occurrences; a set of waiter identities cannot describe every stage.
This is the shared semantic pattern worth extracting once Semaphore supplies the second consumer.
The module still owns its commitment point and cancellation rule.

### A fuel frontier is not a saved continuation

Trace 7 in `Test/Program/QueueTraces.lean` measures one posted delivery with a growing receiver continuation.
At the eight retained lengths, the measured sufficient fuel grows with that continuation.
One less fuel leaves no root exit, even after five later ample flushes.
The source labels this an excluded internal cut under row 226, not a wrapper defect.

Consequently, journal append and cut laws do not provide driver resumption.
CUTS concerns completed journal prefixes and excludes the machine after the stopped row.
`play_controls_eq_replay` requires every added control to progress.
Its exact machine equality does not turn refused or insufficient-budget controls into successful replay.

A reusable scheduled module needs either a proved budget covering its actual continuation or a retained driver continuation.
The latter must keep pending commands, drained tasks, phase ownership, and atomic ownership.
`Machine.Lift.Guarded` already shows why the task snapshot is separate from both the machine and command list.

### Protected acquisition needs one enclosing mask boundary

`Waiting.waitRetry` owns a mask around the waiting operation.
That mask ends before a caller installs its protected body's cleanup.
Row 275 therefore asks for a wrapper taking the caller's restore function.
Semaphore's protected permit and Pool's `use` are its concrete consumers.

The local mask-pop law is proved.
LIFT's run invariant and the later region bracket are separate obligations.
A cleared stack is not restoration: clearing retains the current flag.
The small exact clearing connector in the earlier LIFT packet serves both `Cmd.finish` and `Cmd.exitDone`.
The pending clear's condition must survive observers and their nested commands.
It remains an uncompiled proposal in this review.

## Ranked next foundational work

### 1. State one Queue wrapper relation, then reuse its shape for the next waiting module

- Concept: `translation-simulation`, with `store-typing` and `reactive-scheduling` helpers.
- Question: existing proposed `queue-expansion-agrees`, `wait-registration-no-gap`, and `waiting-request-obligation-preserved`; R4 and R10–R12.
- Reach: the ratified positive-capacity suspend profile, admitted caller types and requests, typed world and handle declarations, mask condition, compatible decisions, sufficient work budget.
- Observation: public request identities, ordered commits and replies, interruptions, terminations, and the ownership of each pending notification.
- Consumer: Queue's public `take` and `offer`, followed by Semaphore's waiting take.
- Exclusions: no fairness, starvation freedom, arbitrary transaction body, host row, or target execution theorem.

Use `Queue.Ops` attempts as the transition cases.
Initialize and renew the cell/world relation from actual allocation facts.
Carry signal ownership through `Machine.Lift` rather than repeat its command and decision inductions.
QINV contributes the model-side invariant; do not duplicate its active work.
A first proof can remain conditional on the explicit budget and mask premises.
The graph must report any planned goals used by that proof.

### 2. Complete LIFT, then give the shared protected-waiting form its law

- Concept: `scope-lifetime-finalization`, with existing `store-typing` rules.
- Question: the R11 run lift of `saved-mask-pop-discipline`, then the region bracket and row 275's protected waiting consumer.
- Reach: each fiber's fixed starting flag; pending clear commands satisfy the pre-clear condition; the body returns to the region's entry stack.
- Observation: the mask flag at the defined boundary and the protected body's cleanup registration order.
- Consumers: Semaphore's protected permit and Pool's `use`.
- Exclusions: a mask chain alone proves neither cleanup exactly once nor a full run's close order.

The smallest ahead connector is `cleared_maskChain_iff` from the prior packet.
It reduces a clear to equality of the pre-clear flag and fixed base.
Reuse the current `Guarded J I O` interface and frame lemmas.
State shared `waitRetry` or `waitAnswer` typing when the second waiting consumer needs it.
The existing `Waiting.Answers`, `Kept`, and minted-scope rules already supply the lower rules.

### 3. Make the work-budget contract compositional before claiming arbitrary scheduled reuse

- Concept: `reactive-scheduling`; `translation-simulation` for the named observation.
- Question: existing `embedded-budget-sufficient`, or later `driver-continuation-split` and `driver-suspension-keeps-typed`; R8, R10, R12, R13.
- Reach: one selected wrapper/helper and its receiver continuation, or a specifically represented driver suspension.
- Observation: preserved machine state and owned residual work; a resumed split must match the corresponding uninterrupted execution.
- Consumers: posted Queue wakes, then Semaphore's visits and Pool's waiting wrapper.
- Exclusions: CUTS alone is no suspension proof; a finite fitted fuel formula is no universal bound.

The present ruling already excludes internal cuts and asks for a sufficient embedded budget.
That is an implementation/proof obligation, not a fresh owner decision.
Admitting arbitrary resumable cuts would require the separate retained-driver representation and its law.
Do not hide that change inside a journal helper.

## R1–R13 crosswalk

Every row still has explicit open parts at this snapshot.
A proved local top node is not completion of the requirement.

| Requirement | Established source connection | Remaining connection relevant here |
| --- | --- | --- |
| R1, signature parameter | Admitted sources carry a lawful application signature; core typed replay accepts it | Public authoring and target faces still have native/table-only signature boundaries; structured carriers remain limited |
| R2, conservative extension | Existing C1–C8 infrastructure and scoped proofs | Host-row meaning, concrete `TypedProg` extension, world projection/back condition, and per-form obligations remain |
| R3, data | Rich record, tuple, map, formation, and scoped codec work supports current module cells | Recursive declarations, error residuals, numeric fields, unsupported Schema images; independent of the next wrapper proof |
| R4, typed state | General module-step typing and typed atomic update connectors | World/handle initialization and renewal along public module runs; target handle identity and some type-argument faces |
| R5, services/layers | Typed source and existing build/reference laws | Machine layer-build refinement and runtime bridge context/key validation |
| R6, host | Keyed receipt/application and bounded prepared-value membership | Executable admission to ghost `AdmittedTape`, typed token/world correspondence, table-aware operational transport, external handles |
| R7, retained behavior | Supplied first-order bodies and scoped captures already support current forms | A stored code reference's entry, captures, context, and lifetime; Cache is the named future forcing consumer |
| R8, observations/targets | Straight and loop agreement; progressed-control replay; finite target lanes | Scheduled module relation, numeric profile implementation, identities across faces, and verified lowering contract |
| R9, typed execution | M5, M6, M7 and typed recorded exits | Closed-requirement transport for missingService remains separate; no termination conclusion |
| R10, library composition | Queue, Semaphore, and Pool step agreement; Queue public typing | Whole public wrapper agreement, internal-step hiding under a named observation, and protected/posted composition |
| R11, resource lifetime | Local saved-mask restoration and mask-pop chain | Run lift and region bracket; at-most-once and exact close-order cleanup across whole runs |
| R12, progress/frontiers | Finite endpoint/deadlock facts and scoped local progress | Notification ownership, sufficient budgets or real suspension, infinite fairness, module request liveness |
| R13, inputs/journals | Journal replay and same-input determinism within their premises | Config/environment/seed, recorded service signature, clock conversion; CUTS adds prefix connectors without resumption |

## What does not need another decision now

The first Queue profile, strict request order, posted wake, commit/cancellation distinction, and fresh hints are ratified.
The same is true of keeping program content first-order and retaining `Eff` as its owner.
Do not reopen them as theoretical uncertainties.

General Queue typing is no longer a backlog item: the five uniform step proofs landed, and public operation typing uses them.
A literal string as an arbitrary caller term remains outside those typing statements.
This is a narrow certificate/API generality issue, not evidence that the runtime string type is unusable.

Raw `Eff.bind` reassociation can capture different absolute positions.
The proposed scope-correct `composeAt` laws remain future work.
Separately, `TypedProg` is not closed under unrestricted bind because nonlocal closing markers carry their original exits.
The checked counterexample is `Test/Program/TypedProgBindRed.lean`; `seq_typed` is the existing constructive route.
Do not combine these two counterexamples or attempt to repair them with one generic monad law.
Neither demands an algebra campaign before the concrete wrapper relation above.

Genuine later choices include a retained behavior value, unrestricted driver suspension, and the still-unruled lowering contract.
The current host guarantee also needs call-site type instances and table-aware transport before more host-facing promises.
None is a prerequisite for the next internal Queue/Waiting/Pool proof slice.

## Evidence limits

No new Lean theorem, finite execution, host run, compiler check, or gate was run.
The existing theorem and report status is read at the frozen source commit.
The Queue trace results are retained source guards, not fresh measurements by this review.
The new clearing statement remains uncompiled.
The packet proposes no parallel ledger and changes no current requirement status.
