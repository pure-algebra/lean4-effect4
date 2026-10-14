# PROC-6: independent review of version 4

The coordinator should revise version 4 before freezing decisions row 379.
The direct block route remains viable, but the budget boundary and the shared-service replay need explicit contracts.
The proposed body theorem also needs a connection to the enclosing block.

This review uses three independent Sol 6.1 agents.
The parent checks their evidence and repeats the decisive finite probes.
The review changes no implementation, plan, decision, generated repository file, or theorem.
This directory holds the review and its evidence.

## Reviewed inputs

The final reviewed plan is [the version 4 snapshot](plan-v4.md).
Its SHA-256 is `f100b80cdbcbcfe0237dd63d8309e64f48fc8fc6ebff352a56c07af542689705`.
The two user attachments are [the second review](inputs/second-review.txt) and [the additional context](inputs/additional-context.txt).

The checkout changes externally during this review.
The first source pass reads `9ccb94e2b8349f72dae884328e84cf25582c95c4`.
The final source pass reads `7c9bb76172400d2f885cf461f2f09db334d2495a`, the plan's source pin.
The report below uses version 4 and the final pin.
The earlier findings that version 4 already fixes are not outstanding findings.

The [manifest](manifest.json) records the input hashes, source pins, evidence files, and final working-tree status.
No `rows-block-host` registry claim or decisions row 379 exists at the final pin.
Their absence is expected before placement and ratification.

## Findings

### F1 — major: the budget invariant needs an actual domain and reply guarantee

Version 4's stage 4 acknowledges the host question, but its justification still says the language cannot change the scheduler budget.
An admitted program refutes that statement.

The [admission probe](evidence/context-scheduler/AdmissionBoundary.lean) declares a generic identity row whose request and answer types are the same variable.
The program reads its context, sends it to that row, and provides the returned context around a body that takes a machine step.
The signature and program pass admission.
The checked call's instantiated answer type is `contextOf empty`.
The checked session accepts a context containing `Env.maxOpsKey` with value `1`.
Its running fiber then holds budget `1`, with yielding enabled.
The [parent's repeated evaluation](evidence/context-scheduler/parent-admission.log) confirms each result.

Explicit context columns are already refused by `findInternalHandle` and `dataRow`.
The witness uses the generic row's instantiated type instead.
Testing `externalValue` alone would not establish an admitted row or a reachable state.
This witness checks both program admission and the actual session reply path.

`SigApp.serviceTy` in `src/Effect4/Program/SigApp.lean` refuses a reserved key as a declared application service.
That rule does not prohibit the key inside a whole context supplied by a host.
`ServicesFit` in `src/Effect4/Laws/Program/Typed/Membership.lean` does not prohibit undeclared keys either.
It constrains declared carriers and requires every stored value to be live.

A declared-type restriction can support the invariant on checked recorded runs, through actual reply admission.
It cannot constrain an arbitrary raw host by itself.
`Column.carrier` and `RowSig` in `src/Effect4/Laws/Program/DenoteRows.lean` give every row the answer carrier `ExitV`.
The raw host can return any such exit, irrespective of its declared columns.

**Required correction.** State where the invariant applies: reachable machine states from `emptyCtx`, with a specific fragment and admitted replies.
Keep the context-general local relation separate from that reachable-state invariant.
If a host restriction enters a theorem, state it and connect it to the recorded run's reply checks.

A rule excluding context-bearing replies must cover success and failure payloads, nested types, `unknown`, and instantiated generic columns.
A stronger alternative admits contexts whose entire reachable contents keep the scheduler settings unchanged.
Both choices need a property of actual values, not a search for a type's spelling.
Neither choice follows from the existing getter theorem.

**Owner:** the coordinator, with the scope amendment recorded by the owner.
**Evidence:** source inspection and finite Lean evaluation.
**Placement:** `rows-block-host`, `translation-simulation`, R6; the reachable machine-to-local-run connection.

### F2 — major: small budgets require more than replacing the arithmetic

The pasted review understates the small-budget boundary.
Budget `2` also stalls after an existing yield.

The finite probe uses the actual scheduler with matching context and cached budget fields.
It evaluates a success operation, then allows twenty flush rounds.

| Starting state | Budget | Completed exits | Flush receipt | Retained frame-stack length |
| --- | --- | --- | --- | --- |
| Fresh operation | 0 | 0 | false | 21 |
| Fresh operation | 1 | 0 | false | 21 |
| Fresh operation | 2 | 1 | true | 0 |
| Already yielded | 2 | 0 | false | 1 |

These are bounded observations, not a universal divergence proof.
The step definitions explain the failed progress argument.
`fire_Myield` consumes one counted operation when it resumes the fiber.
At budget `2`, the next checkpoint yields before an original program step.
The inequality `2 ≤ budget` therefore cannot imply strictly positive local progress after resumption.
That argument needs `2 < budget`.

Budgets `0` and `1` also interrupt the resumption operation.
They can accumulate scheduler continuation frames, as the finite results show.
A general connection must represent those frames as well as yields that take no local program step.

**Required correction.** Keep `H9Blocks` conditional on an exited, funded, settled recorded run.
The small-budget tests do not refute that statement.
Do not derive unconditional finite replay from local termination at arbitrary budgets.
The successful-flush receipt can support induction on rounds without assuming positive local progress each round.
The relation must also account for the scheduler's additional frames.
Keep the existing positive-progress result as a default-budget result if the general connection needs a separate theorem.

**Owner:** the coordinator of stage 4.
**Evidence:** finite Lean evaluation and inspection of `iteration`, `fire_Myield`, `flush_Myield`, and `flushAll_Myield`.
**Placement:** `rows-block-host`, R6; separate agreement from progress.

### F3 — major: building the service once captures the request recorder

The server creates repository methods inside each request.
Those methods close over that request's `KeyedRecorder`.
`TodoAppContext` captures the repository context, and each generated method provides that captured context again.

The current cached service reproduces the failure.
The probe builds it under recorder A, completes a list request, and closes A's record.
It then adds an item under recorder B.
The add still calls A and fails with `a live call after the request's record`.

The exact output is in [the fresh-service recording probe](evidence/consumer-build/captured-context-current.log).
The source is [the corresponding probe](evidence/consumer-build/captured-context-current.ts).
It imports the freshly emitted cached service and the real recorder and row bindings.

The source owners are `serve` in `apps/todo/server.ts`, the emitted `TodoAppContext`, and the generated methods.
The merge behavior comes from rc.112's `provideContext` in `vendor/effect-4.0.0-rc.112/src/internal/effect.ts`.
Providing a new outer repository does not replace the captured inner repository.

**Required correction if server lifetime is adopted.** Give the shared service a repository adapter whose lifetime matches the server.
Route each call through the active request recorder under the existing serialized request order.
Alternatively, define another recording boundary that has the same observation.
Include startup construction, persistent stores, and each request's exit in the replay contract.

`runOf` and `checkSession` in `tools/Tools/RunChecks.lean` rebuild separate runs and thread only the reference model's state.
`H9Blocks` observes a program's final root exit and stores.
It does not yet connect separately observed request exits to one persistent service session.
That connection needs a placed goal and a consumer before implementation.

The cache claim also needs correction.
A repeated read hits the cache, but a successful write invalidates it.
The next read calls the repository again.
The [fresh cache probe](evidence/consumer-build/cache-current.log) records `all`, `insert`, `all`.
Thus the pasted claim that GET after POST becomes a cache hit is false for the current cached service.

**Owner:** the coordinator of stage 5 and the server-lifetime amendment.
**Evidence:** finite runtime tests with Bun 1.4.2 and Effect 4.0.0-rc.112, plus source inspection.
**Placement:** `rows-block-host` and the application replay consumer; the TypeScript connection remains finite runtime evidence.

### F4 — minor proof debt: the body theorem does not yet reach the block root

Stage 1 excludes `defs` from `BodyRows`.
Stage 2 states `compilesBlk` only for `BodyRows table e = true`.
Stage 3 needs the result for a `BlockRows` root, which is a `defs` node.
Listing a `defs` arm in the proof outline does not extend the theorem's domain.

**Required correction.** Add the block-root connection explicitly.
Apply the body theorem to `main` at `p.child 1` and handle exhausted compile fuel.
Place that theorem under `rows-block-host`, with stage 3 as its consumer.
This is a missing proof connection, not a counterexample to the intended semantics.

**Owner:** the coordinator of stages 2 and 3.
**Evidence:** the proposed statements in the version 4 snapshot.

## Answers to version 4's four questions

| Question | Answer |
| --- | --- |
| Fragment restriction or reply admission? | A named fragment restriction is the smaller scoped change. Inspect instantiated call columns, or conservatively exclude variables that can become contexts. Connect the rule to actual admitted replies. Do not silently change global reply admission. A broader budget-safe-context protocol needs its own value property and proof. |
| Fewer context-related statement changes? | Keep the existing context-free step. Let the hosted step handle context actions before delegating other actions. Put context in the hosted state and outcomes. Default arguments help old callers but do not prove the broader statements. No compiled migration establishes a smaller count. |
| Is `intro_call` the only direct P3 call consumer? | The source sweep finds it as the only consumer of `suspendBodyAt_call`. The two reference equations and the typed `call_arm` also change. No additional call-specific consumer appears in `Simulation/`. This is source evidence, not a compiled repair. |
| Should stage 0a land early? | Yes, after its contract and placement are fixed. It is independently buildable and can precede stage 2. Stage 0 can proceed independently. Keep stage 0a's reference repair, typed repair, regeneration, and reached behavior gates in the same slice. |

The budget choice is a scope decision.
The current language can receive scheduler-changing contexts.
Describe any exclusion as a restriction of this agreement fragment, rather than impossibility in the language.
The general agreement remains a valid objective, with progress stated separately.

## Disposition of the six original questions

| Question | Checked result | Remaining limit |
| --- | --- | --- |
| Q1: lexical call frame | The listed implementation, reference, hop, introduction, and typed sites match the direct consumer sweep. Existing empty-scope stack lemmas fit the proposed repair. | The repair is not implemented or built by this review. Observation preservation on all checked programs still needs its stated evidence. |
| Q2: reader lift and agreement | The pointwise lift is plausible. `EffAlgebra.AgreeOn` requires unconditional equality for `provideContext` and `withFiber`. Empty context requirements also pass its key guard vacuously. Version 4 correctly uses fragment induction. | Conservativity and the new algebra remain proposed. |
| Q3: context and masks | Context must survive calls and yields. `PlainFrame` rejects the `setInterruptible false` frame that context restoration creates. | Also widen the context finalizer, continuation, and success/failure step lemmas. Defaults alone do not generalize proofs. |
| Q4: scheduler budget | Exact default-budget arithmetic exists. The small-budget failure is reproduced, including an already-yielded budget of 2. | Close the actual fragment/reply invariant, or generalize the machine connection. Keep progress separate. |
| Q5: lifetime and twin | Separate layer provision builds separate state in this server. A ready context avoids rebuilding per request. | Shared recording and persistent replay remain unresolved. A write invalidates the cache. |
| Q6: context typing | The getter theorem exists under valid service values and required-key coverage. | It does not establish those conditions for every raw context or arbitrary host answer. |

The Q6 anchors are `checked_context_arm` and `native_context_answer` in `src/Effect4/Laws/Program/Typed/Context.lean`.
`fits_context_inv` and `ServicesFit` live in `src/Effect4/Laws/Program/Typed/Membership.lean`.
`inv_action_context` lives in `src/Effect4/Laws/Program/Typing/CheckInversion.lean`.
Its result type is `contextOf keys`, rather than the bare `Ty.context` stated in the pasted review.
The reachable typing result also requires program checking, a closed root requirement, and an admitted tape.
The host boundary remains the one in `docs/core/host-boundary.md`.

The invocation-budget argument survives inspection.
Captured argument trees retain the caller's budget.
`RunsToDO.mono` lowers the required step count without changing the observed outcome.
Rebuilding those closures at the smaller budget would require a different argument.

The proposed context exit law survives the two malformed-term controls.
Compilation evaluates the context or service value before entering the body.
Both controls produce `badShape`, matching the proposed algebra.
This finite check does not prove the full exit law.

## Verification and reproducibility

The review runs one Lake process at a time, with `LEAN_NUM_THREADS=3`.
The pinned Lean toolchain is `leanprover/lean4:v4.33.1`.

| Command or probe | Result |
| --- | --- |
| `lake build Effect4.Laws.Program.Agreement.Machine` | Passed; log retained. |
| `lake build Effect4.Laws.Program.Agreement.LoopCalls` | Passed; log retained. |
| `lake env lean` on `ExitFold.lean` | Passed; both malformed-term guards accepted. Parent repeated it at the final pin. |
| `lake env lean` on `Probe.lean` | Passed. Parent repeats it with coherent context and cached budget fields at the final pin. |
| `lake build Effect4.Run Effect4.Api.Author Effect4.Program.Typing.Call` | Passed before the admitted generic-row witness. |
| `lake env lean` on `AdmissionBoundary.lean` | Passed: signature admission, program admission, instantiated context answer, and the checked session's adoption of budget 1. Parent repeated it. |
| Narrow build of the cached emitter's imports | Passed after setting `LAKE_CACHE_DIR` to the temporary review directory. |
| `lake env lean --run apps/todo/EmitTodo.lean` with a temporary output directory | Passed; freshly emitted cached service retained. |
| `bun` on the layer-lifetime probe | Passed: separate lifetimes answer `[1,1]`; shared lifetime answers `[1,2]`. |
| `bun` on the fresh cached-service recording probe | Passed: the probe detects the second request's expected recording failure. Parent repeated it. |
| `bun` on the fresh cache invalidation probe | Passed: repository calls are `all`, `insert`, `all`. Parent repeated it. |

The first cached-emitter build encounters a sandbox cache-write restriction, not a Lean error.
The supported `LAKE_CACHE_DIR` setting resolves it without changing the repository configuration.
Both attempt logs are retained.

The ignored `apps/todo/.work/todo.gen.ts` contains an older uncached service during this review.
The current emitter selects `Test.Dogfood.Scenario.Todo.Cached.cached`.
The decisive runtime tests use a fresh temporary emission, not that stale file.
The manifest records both hashes.

The detailed runtime commands are in [the consumer receipt](evidence/consumer-build/receipt.md).
The scheduler analysis is in [the scheduler receipt](evidence/context-scheduler/receipt.md).
The final scheduler output is [the coherent-state rerun](evidence/context-scheduler/coherent-probe.log).
The retained TypeScript probes use Bun directly.
No TypeScript compiler acceptance is claimed.

The plan's reached behavior gates remain implementation obligations.
This review runs neither `make check-full` nor the whole-tree axiom gate.
It introduces no production theorem, so it claims no new axiom-audited proof.

Stage 0a's OCaml sequence is `make gen-lcnf`, then `opam exec --switch=effect4 -- dune build` from `ocaml/`.
`make check-ocaml` does not substitute for regenerating the changed LCNF outputs.
Version 4 already fixes the pasted command name.

**Verdict: rework.** Retain the direct block route and version 4's corrected context split.
Specify the budget domain, add the block-root proof connection, and design the shared recorder and replay boundary before freezing the plan.
