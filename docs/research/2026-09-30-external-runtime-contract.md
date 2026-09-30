# External replies, runtime representations, and lowering: proposed completion contract

Date: 2026-09-30. Inspected base/head: `be15b062db15eb6619c594e775d142370253c6bd`.

**The external lane is required for completion.** Completing an empty-table or
internally typed transition proof does not complete the public runtime contract.
The endpoint is a checked, usable external protocol connected to reference
execution, with runtime structures specified well enough to replace their
backing representations and compose separately justified compiler stages.

Status: design proposal and fresh research evidence. This note does not change
the decision register, frozen predicates, production APIs, or implementation.
The new choices in §10 require an explicit recorded freeze before their slices
land. Existing DI-57/58/65/68/69 rulings already require the external work; they
do not need to be decided again.

The origin-ledger work remains its own small change. Its acceptance cannot close
any external, typed-boundary, storage-implementation, or compiler obligation.

## 1. Authority, scope, and checked starting point

The authorities remain:

- `docs/DESIGN-ISSUES.md`, DI-57: keyed, table-aware `session_eq_ref`, comparing
  classification and full machine observation. The empty-table theorem becomes
  its corollary.
- DI-58: exact per-call envelope, separate receipt and application, no preloaded
  answer-list bypass after explicit migration.
- DI-65: relational host work, retained state on failure, pending acquisition
  ownership and completed cleanup.
- DI-68: distinct execution/compilation budgets and observed live frontiers.
- DI-69: the row-family denotation and its single-fiber `StraightRows` theorem.
- `docs/core/machine-state.md`: runtime field owners, the observation boundary,
  lawful storage interfaces and separate lowering connections.
- `docs/core/post-phase-c-synthesis.md`, W3/W10/W11: observation/storage,
  external semantics and lowering workstreams.

The scheduler contract packet still contains an older raw-replay formulation.
When freezing executable statements, reconcile that packet to the amended
DI-57 target and current APIs. Do not establish a second owner here or copy the
old signature as though it were an elaborated current theorem.

“Full” has two named scopes:

1. **Current admitted core:** every permitted row/value/completion/session case
   has semantics, executable admission, a prepared-answer typing connection,
   and table-aware reference agreement. An unsupported case has a located
   refusal and is excluded from the published profile before execution.
2. **Module and target expansion:** each new host binding, stored-behavior API,
   transaction profile, runtime container and compiler target extends those
   contracts with its own obligations. No claim of all Effect exports, arbitrary
   foreign objects, or an unproved whole compiler follows from scope 1.

An implementation slice may be small. Required functionality cannot disappear
by narrowing its acceptance profile after a counterexample.

### Fresh evidence

The executable [Probe.lean](2026-09-30-external-runtime-contract/Probe.lean)
contains 11 finite guards:

- A program checked at answer `nat` spawns a child returning `"wrong"`, then
  receives that actual child's handle from an external row claiming
  `fiberOf nat never`. Current `Api.replayChecked` accepts the reply and the
  program joins the child, returning the string. This is a real checked replay,
  not a forged arbitrary starting machine.
- Its positive companion uses a child returning `7`; the same reply path
  succeeds at the declared type.
- Two allocation replies inspected against one allocation snapshot both pass
  `admitAnswer`; after one allocation, the other original reply fails.
  Pre-numbering it with the next index instead fails against the original
  snapshot. These four guards are local admission controls, not a complete
  two-call session execution.
- Direct replies cannot currently return an existing external handle, a fresh
  handle inside an option, or an existing handle inside an option.

The source cause is precise: `Val.hasTy` deliberately checks only the handle
kind for refs/deferreds/fibers, and runtime admission adds existence, not the
declared payload type. Merely switching `Typed.replay` to today's checked
helper cannot establish the promised typed-result guarantee.

The separate [PredicateProbe.lean](2026-09-30-external-runtime-contract/PredicateProbe.lean)
checks five small kernel facts about the current typing predicate. Products,
Results and successful reified exits can bypass nested handle declarations;
a union can obtain shape evidence from one branch and handle evidence from
another. These are facts about the predicate, not a claimed reachable-state
counterexample for every wrapper. §4 makes their repair an explicit prerequisite.

## 2. Boundary ownership and the state transition

Keep `Eff` as the sole program representation. Keep `Ty`, `Store.Val`,
`Completion`, row tables and `Runner.Command` as their existing sort owners.
Reference continuations and semantic relations remain proof carriers.
Host promises, callbacks, pointers and runtime objects never enter stored
program syntax.

The boundary adds data about calls, capability correspondence and ownership.
Its implementation may use the six interfaces in §7. It must not depend on
list positions being host identities.

Use the following semantic interfaces; names below are proposed, not existing
Lean declarations:

| Interface | Required meaning |
| --- | --- |
| `RequestFits` | The live `(fiber, token)` identifies the exact external row and evaluated request; request values and required services fit their declared types and capability correspondence. |
| `HostProgress` / `HostComplete` | A binding may take observable host steps before completion; a completed success or failure retains its resulting host state. Alternatives are relational until explicit choices are fixed. |
| `ReplyEnvelope` | Version, session, binding/profile, exact raw table, call ID, key, row, request and category match the recorded call. Canonicalized type columns do not erase raw table identity. |
| `ReplyFits` | The received data and capability claims are valid for this call. Checking does not execute the machine, allocate machine handles, or mark the reply consumed. |
| `PrepareReply` | Given a currently applicable reply, produce the prepared `Completion`, new stores, capability/ownership correspondence and extended typing world, or a located refusal. |
| `PreparedFits` | The prepared completion fits the exact parked continuation in the resulting world; all old declarations and external target spellings remain valid. |
| `ApplyReply` | Select one key, prepare and resume it, consume the exact guard at most once, and retain all committed state across failure or a later frontier. |
| `RegistryAgrees` | Executable capability metadata agrees with actual allocations, checked creation sites and the proof world's declarations. |

Separate facts are owed for each row of this table. Envelope matching alone is
not semantic answer typing; semantic typing alone is not evidence that a real
host binding performed the specified work.

### Lifecycle and ownership

Use explicit states equivalent to:

`issued → host pending → acquired/unprepared → received → prepared/machine-owned → cleanup pending → released`

Cancellation or refusal may move an unprepared acquisition to
`compensation pending`; cleanup failure retains an outstanding obligation.
Acquired/unprepared can precede receipt. The host driver therefore owns an
acquisition even if the session never accepts its reply.

The following behavior is required:

| Event | Machine/session effect | Resource responsibility |
| --- | --- | --- |
| Bind a live call | Add one call/key association in bind order; no host answer applied. | Binding records any host work it starts. |
| Receive a valid reply | Store exactly once for its key; do not run or allocate. | Pending acquisition remains accounted for. |
| Receive malformed, duplicate, stale or retired reply | Located refusal; execution/session unchanged by the refused command. | A resource already acquired by the host still requires release/compensation. |
| Apply with zero execution fuel | Frontier; reply, guard and allocation state unchanged. | Ownership unchanged. |
| Apply a valid selected reply | Atomic preparation commit with guard consumption; resume the corresponding continuation. | Transfer fresh resources exactly once, keep alias identity. |
| Exhaust fuel after preparation | Retain prepared state and consumption; never re-prepare on retry. | Machine-owned resources remain owned. |
| Interrupt before application | Retire the association and any accepted payload. | Compensate an unprepared acquisition only when no other valid claimant remains; otherwise retain its ownership entry under §3. Compensation mints no machine ID. |
| Interrupt after application | Use the admitted interruption/finalizer semantics. | Cleanup is part of the machine/binding ownership connection. |
| Finish program while cleanup remains | Report the program result and outstanding cleanup state separately. | A terminal “all resources closed” claim remains unavailable. |

Atomic preparation means construct and validate the complete candidate update
before committing it; no partial allocation on refusal. It is distinct from
host work, which may already have changed host state. The protocol's
at-most-once consumption does not promise exactly-once network side effects.
Crash recovery needs durable journal/host idempotency obligations before that
stronger claim is made.

Receipt order, selected application order, scheduler choices and timer order
remain explicit. The existing `reply_commute` theorem concerns accepted
receipts with frozen execution state. It does not imply two applications
commute or prove independence from subsequent allocation.

## 3. Proposed capability and allocation representation

### Executable type evidence

Add a first-order declaration registry on the checked execution boundary:

- Root declaration comes from checked source admission.
- A fiber declaration comes from the checked body/creation site and the
  **actual allocated ID**, including internal forks.
- Reference and deferred declarations come from their checked allocation
  types; they remain invariant through writes/completion.
- A park declaration records the actual token's intermediate resume type.
  It is not inferred from the receiver's final result type.
- External entries identify target, stable binding identity, machine
  correspondence and ownership state.

The registry is derived metadata. It introduces neither tags inside `Val` nor
a second checker/type language. Creation-site evidence must be produced from
the existing checker and its source/path/environment information, with
coverage of every actual creation transition. Reply metadata cannot create,
replace or widen the declaration of an existing internal capability.

Prove `RegistryAgrees` at loading, creation, mutation, parking, cancellation
and replay. It includes unique domains, lookup equality with `Γ/Π/Ρ/Θ`,
actual allocation correspondence and canonical types. Source admission alone
does not prove registry coverage.

Restoring decoded metadata is insufficient. Restore by checked journal replay,
or validate a separately specified sufficient state certificate. A structural
codec certificate is not a reachable-state certificate.

This is a proposed boundary extension to decision row 44's ghost-only design;
it must be recorded explicitly before implementation. The existing internal
value layout and coarse shape checker can remain stable.

### Host identities, aliases and fresh resources

Use a stable resource key scoped by binding/profile/session, distinct from the
machine allocation index. A fresh resource records its originating call and
an acquisition identity. The binding's correspondence relates that key to the
actual host object; the object itself is not serialized.

Receipt validates the resource claim without guessing the future machine
index. Application allocates at the then-current machine extent. Distinct
independent acquisitions must succeed in either application order; their
different index assignments are related consistently in values, stores and
future requests. Full machine observations in a same-order replay still agree
exactly. No theorem may compare reordered applications by raw ID equality.

Within one reply, repeated references to one fresh resource allocate once and
reuse its identity. Across replies, an existing resource claim reuses an
established correspondence. Two distinct fresh-owner claims for the same
physical acquisition are invalid; ownership cannot be duplicated by inventing
another key. This last property belongs to the binding's host correspondence,
not to a comparison of user-provided strings.

Also support aliases across received-but-unprepared replies. A resource-level
ownership entry retains the originating acquisition, all outstanding call
claims and the optional machine correspondence. The first selected valid
claim materializes the resource once; later claims reuse that correspondence.
Cancelling the originating call removes its claim, not another call's claim.
Compensate an unprepared resource only when no valid claimant remains; after
materialization, its single cleanup obligation belongs to the machine/binding
ownership relation. Bindings declare borrowing/transfer/release rights, and
receipt validates those rights. This is not implicit reference-counted
auto-release: an explicit release follows the binding's stated policy, and
later uses observe its declared closed-resource behavior. The source of a
resource key is provenance, not an unconditional right to close all its aliases.

An allocated identity and an open resource are different facts. Released
identities remain recognizable so the binding can implement its specified
use-after-release/double-close behavior. Closing a resource does not
retroactively make all retained value images malformed.

### Boundary image and recursive preparation

The proposed boundary image has this signature:

- an existing `Completion` whose ordinary value structure is `Store.Val`;
- a finite reply-local capability environment;
- each handle occurrence in that image refers to an entry in that environment;
- entries distinguish certified existing machine capabilities, represented
  existing external resources, and fresh acquisitions;
- fresh entries carry a scoped host key, declared target and ownership evidence
  reference; existing internal entries resolve against the executable registry.

This is a transport interpretation of the existing value structure, not a new
general value language. Do not interpret an unvalidated reply-local index as a
machine ID. The completion's delayed-reference key resolves through the same
environment. Reserved internal targets cannot be minted as external objects.

Its wrapper type is distinct from a prepared machine completion. Every
`.handle kind localIndex` and `.ofRefGet localIndex` resolves through that
environment with an exact kind/capability-sort check. No machine interpreter
receives the wrapper's raw contents before realization. First-occurrence
numbering traverses the entire completion, including a delayed-reference key.

Freeze an exact image domain: no missing, duplicate, conflicting or unused
capability entries; stable first-occurrence numbering; aliases reuse entries;
canonical union handling. Derive structural traversal from the existing value
signature and share the type's decoded views. A versioned codec must prove its
round trip and exact image up to this named normalization.

For a union, select a branch using the **entire** shape-and-capability
judgment. Evaluate candidates without mutation. If more than one branch is
valid, require identical prepared value/store/ownership effects, then choose
the first member in canonical type order. Otherwise refuse ambiguity with its
path. A branch witness supplied by the host is checked, never trusted.

Under `unknown`, retain ordinary data; inspect every embedded capability.
Recognized capabilities require valid correspondence. Unknown handle kind
bytes refuse at this external boundary until a profile defines their meaning.
A fresh external handle under `unknown` requires an explicit target in its
capability entry. Ordinary bytes remain data and cannot later become a
capability through an unchecked conversion.

Returning an existing certified machine fiber/ref/deferred is supported.
Importing an unrelated host fiber/ref/deferred as though it were that machine
capability requires an additional binding relation covering its operations
and lifecycle. Until such a relation exists, use an opaque external handle
with declared operations or a located import refusal. A host's type assertion
does not create that connection.

Cross-process revival requires a versioned binding reviver plus identity,
ownership and lifetime evidence. Profiles without it refuse cross-process
capability restoration. This follows the direction of still-open boundary
decision row 7; the concrete choice is proposed here, not already ratified.

## 4. The typing judgment must cover the actual representations

Do not set the endpoint to “runtime checking implies today's `StrongValue`”
and stop there. Source inspection and `PredicateProbe.lean` show:

- Products admitted by `Val.hasTy` are two-element `.list` values, while
  `HandlesFit` checks `.pair` and otherwise returns `True`.
- `except` and successful `exitOf` payloads take its catch-all `True`.
- Shape and capability evidence for a union may use different branches.
- The list shape checker decodes fiber snapshots, while `HandlesFit` checks
  only ordinary lists.

Introduce a constructor-complete membership judgment beside the old one,
combining shape and capability evidence in the same derivation. Reuse existing
`Ty`/`Val` owners and variance. Connect it to the old judgment in the direction
actually valid; the reverse implication is false in general. Migrate the
consuming continuation, store, delivery and exit obligations before retiring
the old predicate. This is an explicit frozen-judgment amendment.

The current `Err` carrier supports numeric/text/two-string payloads, not
arbitrary values. Existing `valOfErr_keys` and cause-image laws establish
handle-free decoded failures. Use those facts for current failure causes;
do not claim an embedded-handle exploit there. A Result's error arm, however,
is ordinary `Val` data and must be recursively checked.

### Constructor-indexed acceptance matrix

Every current `Ty` constructor appears below. Each implementation must supply
positive and negative controls where inhabited, plus a proof against the
same membership judgment. Profile refusals count as exclusions, not coverage.

| `Ty` constructor | Boundary meaning and required evidence |
| --- | --- |
| `never` | No successful inhabitant. A row answering `never` may still fail, defect, be interrupted or remain pending. |
| `unit` | Exact unit image. |
| `nat` | Exact mathematical natural in the semantic core; a target restriction is explicit and covers intermediates too. |
| `int` | Current native membership has no inhabitant; explicit unsupported profile entry. Adding integer values is a separate carrier/checker/codec/lowering slice. |
| `string` | Exact text image; target encoding relation is declared. |
| `bool` | Exact Boolean image. |
| `handle` | Exact internal reserved-kind clause or external target correspondence; contexts use the selected static service-type rule. Fresh external acquisition uses §3. |
| `option` | Exact absent/present image; recursively fit the present payload. |
| `list` | One shared decoded element view for ordinary lists and admitted snapshots; recursively fit every element. |
| `prod` | The actual two-element list representation; recursively fit both columns. |
| `except` | Exact constructor/arity, recursively fit the selected error or value arm. |
| `exitOf` | Decode once; success recursively fits the answer; failure follows the declared cause/error image. |
| `causeOf` | Decode once; every typed failure fits its error column; defects and interruptions retain their separate categories and ordered annotations. |
| `fiberOf` | Existing allocated fiber plus declared answer/error subtyping, using the ratified covariance. No retyping by reply. |
| `union` | At least one complete matching branch; deterministic preparation only under §3's agreement rule. |
| `lit` | Exact matching string literal. |
| `refOf` | Existing reference with the exact invariant declared type, not the type of its currently stored contents. |
| `deferredOf` | Existing deferred with exact invariant answer/error declarations and its lifecycle invariant. |
| `var` | Templates must be instantiated before boundary admission; refuse remaining open variables. |
| `unknown` | Ordinary data plus explicit capability validation under §3; no unchecked revival. |

Both `Completion` constructors require separate clauses:

| Completion | Required result |
| --- | --- |
| `ofExit (success value)` | Recursive preparation followed by membership at the row's answer in the new world. Fresh/nested/aliased handles are included. |
| `ofExit (failure cause)` | Validate the supported error image and category, preserve reason order/annotations and the host state resulting from work. No failure-to-refusal conversion. |
| `ofRefGet cell` | Validate the declared reference type against the answer type; keep the read delayed until resume. Prove subsequent legal writes preserve that declaration. Current contents fitting once is insufficient. |

Error-column admission must also use the existing supported-error-language
restriction. Adding a general value-carrying error is a separate required
extension if an intended binding needs it; it cannot be smuggled through
`boom`, stringification, `unknown`, or a silent loss of payload.

Required theorem shapes separate receipt from application:

- Under the strengthened typed-state/world invariant, `RegistryAgrees`, a
  lawful linked row/table, and a live call/token correlation, receipt acceptance
  establishes the envelope and boundary-image judgment at that receipt state.
  Binding realization and pending-ownership premises connect those data to an
  actual acquired resource. Receipt does not promise future applicability.
- Under those invariants at application time, the still-live selected key,
  retained reply, current binding/ownership correspondence and successful
  revalidation, preparation establishes a valid state/world extension, exact
  ownership accounting, and a completion fitting that token's intermediate
  type in the new state. Cancellation, revocation and explicit release have
  their declared alternative transitions; unrelated allocation alone cannot
  invalidate the claim.

The converse is owed on the explicitly admitted boundary profile, modulo its
normalizer: every semantically valid representable reply is accepted.
Rejecting all handle replies cannot satisfy the completion contract.

## 5. Reference semantics, typed replay, and entry paths

Extend the existing reference machine, with:

1. A row table and its linked type view.
2. External registration retaining the request/call identity.
3. The same specified preparation/conversion/allocation relation.
4. Table-aware evaluator selection throughout nested evaluation.
5. Keyed bind/submit/apply/control replay and corresponding retained session
   state; the reference must not substitute an answer queue for keyed calls.
6. Separate compilation and execution budgets and matching frontier reasons.

Share one pure preparation owner between interpreters where possible, then
prove its connection to the boundary judgment. Sharing code alone does not
prove the row's intended host behavior.

The proof ladder is:

`checked load → registry/world agreement → typed live request → admitted receipt
→ prepared completion + world/ownership transport → typed resume
→ transition preservation → replay/reference agreement`

For M6, accepted histories are prefix-dependent: validity is checked against
the current machine, work queue, world and actual expected token type.
Keep separate premises for external answers and built-in timer/yield/deferred
deliveries. “This tape passed the old checker” cannot replace those premises
until its bridge is proved.

Built-in parks are answered only by their own typed delivery paths. The sleep
counterexample remains a control for the raw/unrestricted statement; its
`.notExternal` refusal does not test external payload typing.

Name separate theorems/observations:

- **Typed execution:** every consumed intermediate answer and every reported
  fiber exit meets the relevant declaration, under the admitted profile.
- **Machine agreement:** DI-57's outcome classification and all fiber exits
  plus whole semantic stores, for the same admitted source/table/journal and
  compatible budgets.
- **Holder agreement:** active calls, pending payloads, consumed/retired calls,
  guard ownership, command phases and frontier reasons. A projection exposing
  only counts/keys is insufficient to relate omitted payload contents.
- **Host binding refinement:** request/result representation, host progress,
  retained state, identity and cleanup under a named binding relation.
- **Row denotation:** DI-69's `StraightRows` result on its named fragment;
  it does not replace the general machine/session connection.

All four current `Runner.Command` constructors—`bind`, `submit`, `apply`,
`control`—need transition and replay-prefix cases. Refused commands leave the
runner unchanged; external host state is accounted for separately.

Entry-path disposition:

| Current route | Required disposition |
| --- | --- |
| `HostSession` / `Runner` / `Run` | Canonical checked keyed route; complete capability admission and reference/host connections. |
| `Api.replayChecked` | Close declaration/preparation gaps and preserve independent budgets. Retain only as an explicitly low-level decision-evidence interface; it does not certify recorded host calls or replace the keyed production route. |
| `Api.Typed.replay` | Proposed public host replay consumes a session header and `Runner.Command` journal through the canonical checked session, with refusal-bearing phases and both budgets. Any retained decision-tape convenience is separately named low-level and makes no envelope/host-conformance claim. |
| Raw `Api.replay`, program-only `replayAdmitted` | Keep their explicit low-level roles; no claim that source checking admits arbitrary decisions. |
| Preloaded external answer list | Migrate with recorded provenance and remove production bypass under DI-23/58; keep any historical comparator explicitly isolated. |
| Internal due work/timers/yields | Derive typing from registration and lifecycle; do not run them through external-call admission. |
| OCaml target entry | Add a table-aware keyed entry path. Existing fast/reference API engines use `table = []`; their usual differential does not cover this work. |

Do not synthesize a supposedly recorded `Call` from the current machine to
launder an unassociated raw reply through the session. The public typed API
change and compatibility migration are explicit parts of the proposed freeze.
Prove that erasing an accepted journal to its actual machine decisions agrees
with raw execution at corresponding budgets; retain the richer session facts
through the holder relation, which raw replay cannot express.

Executable snapshots and budget continuation need a precise contract. A
machine alone does not necessarily retain the driver's unfinished command
work. Until resumable driver state is represented and related, continuation
across an exhausted operation must use checked replay from its origin with
the selected larger budget. Do not promise direct snapshot resumption that
the current API cannot provide.

Recovery replay reconstructs from recorded commands and replies. It never
reissues physical host work, transfers a physical resource twice, or repeats
compensation. Reconstructed allocation entries reconnect to the retained
resource ledger, with one owner. Reuse the verified old prefix; execute new
host work only after reaching its recorded frontier. If recovery cannot
establish that correspondence, report a recovery refusal/frontier rather than
silently rerun acquisition. Add a repeated-recovery control after allocation.

## 6. Required behavior and independent rejection controls

Positive cases required before calling the external lane finished:

- Scalar and structured results across every inhabited matrix row.
- Fresh, existing, nested and aliased resources; correct internal capabilities.
- One pending resource claimed by two replies, applying either first and
  cancelling the originating call while the other still owns a valid claim.
- Typed failure, supported mixed causes, mutation followed by failure.
- Delayed reference reads with legal intervening writes.
- Two independent acquisitions in both receipt orders and both selected
  application orders; no refusal caused solely by unrelated allocation.
- Cancellation before receipt, after receipt and after preparation; late
  acquisition compensation; pending and failed cleanup.
- Explicit scheduling and timers while unrelated external calls remain pending.
- Zero execution budget with independently positive compilation budget,
  positive execution budget with zero compilation budget, and exhaustion after
  preparation without repeated allocation/consumption.
- Recovery from repeated frontiers after acquisition without repeated physical
  work, allocation ownership transfer or compensation.
- A resource acquired, stored in an ordinary Ref, read and used by another
  external operation, then released through its declared cleanup route.

Negative controls must independently break:

- Version/session/profile/raw table/row/request/key/call/category matching.
- Duplicate, stale or retired replies and forged resource identity.
- Unallocated handles; allocated handles with the wrong target or wrong
  ref/deferred/fiber declaration; internal targets minted as external.
- Every structural predicate gap in §4, including snapshot and union branches.
- A delayed read whose current value fits but whose declared cell type is too wide.
- Missing/conflicting/unused capability entries and ambiguous allocation.
- A partial preparation followed by refusal, or repeated preparation after a frontier.
- Lost cleanup responsibility after cancellation, including resources acquired
  before the session could accept them.
- Incorrectly classifying an incomplete valid input as program failure.
- A backend that duplicates/drops/reorders owed work, changes old snapshots,
  saturates an identity counter, or forgets the prepared resource mapping.

Bindings owe behavior beyond row membership. For example a stream pull's
selected binding law requires either end-of-stream or a nonempty chunk;
`option (list a)` membership alone admits an empty chunk.

Finite controls establish discrimination and reproductions. Universal
typing/session/storage/lowering claims require their named proofs or validated
certificates. Each receipt records exactly which kind of evidence passed.

## 7. Abstract runtime structure coverage

Freeze six distinct operational interfaces now. Supply a small lawful model,
then replace an actual consumer and prove the connection. Avoid a universal
container abstraction that conceals order or allocation policy.

| Interface | Laws required of each backing implementation |
| --- | --- |
| Dense arena | Empty/extent/lookup/replace/allocate; fresh key is old extent; old-key stability; absent-update policy; persistence of prior snapshots. |
| Keyed table | Equality/hash coherence; duplicate/missing policies; specified iteration order; sparse IDs distinct from cardinality and allocation supply. |
| Ordered work | Selection, priority/FIFO where specified, cancellation, snapshot/live drain, reentrancy, exact no-loss/no-duplication delivery. |
| Append sequence | Ordered append/index/projection and retained prefixes. Authoritative journals cannot silently become lossy diagnostic rings. |
| Persistent path/environment | Resolve against the owning program, captures/layout coherence, scope/lifetime and alias preservation. |
| Derived view | Cache equals one fixed projection of owner state after every operation; changing the projection function is a different contract. |

Every interface also states scalar representation and payload ownership:
persistence is not established merely by single-threaded scheduling.

The runtime-family inventory is:

| Family and current owner | Interface and semantic invariants to retain |
| --- | --- |
| Values/types/code: `Store/Carrier/Val.lean`, `Program/Ty.lean`, `Program/Eff.lean`, `Program/Compile.lean` | Existing sort signatures; scalar/codec relations, nested capabilities, `Point` paths/environments and code ownership. |
| Saved frames: `Machine/Frames.lean`, `Machine/Fibers.lean` | Typed intermediate continuation; masking/restoration, catches/finalizers/loops, retained context and interruption. |
| Fibers/origin/children/observers: `Machine/Fibers.lean` | Key lookup/update, unique IDs below supply, source origin correspondence, distinct child tracking, ordered observers and exited-fiber retention. |
| Race/iterator/driver work: `Machine/Fibers.lean` | Entrants/results/source paths/tokens correlate; launch and cancellation order; retain unfinished outer work in any promised suspension. |
| Dispatchers/armed callbacks: `Machine/Fibers.lean` | Ordered work, priority/FIFO, snapshot drain, reentrant enqueue, arming ownership/order. |
| Ref heap: `Machine/Stores.lean`, `Laws/Machine/Arena.lean`, `Laws/Machine/RefKernel.lean` | Dense allocation, atomic answer/state updates, typed aliases, absent-update and snapshot laws. |
| Deferred/due/wakes: `Machine/Stores.lean`, `Machine/Wake.lean` | First completion wins, stored `Completion`, registration-order broadcast, delayed reads, active-token receiver typing and stale-token inertness across pending/captured/due/posted phases. |
| Scopes/releases: `Machine/Scope.lean`, `Machine/Stores.lean` | Sparse IDs; mark closing before cleanup; sequential/parallel strategy; captured services, reentrancy, failure accumulation and cleanup ownership. |
| Layer memo world: `Machine/Stores.lean` | Unique map IDs below shared supply, parent lookup/duplicate policy, promise/scope/finalizer correspondence, observers, sharing/freshness and release ownership. |
| Clock/timers: `Machine/Timer.lean` | Exact clock, monotonicity, deadline/tie order, cancellation, staged advance and running between fires, retained advance frontier. |
| Context/captures: `Machine/Stores.lean`, `Program/Compile.lean` | Service identity/override/inheritance, static types, lexical versus invocation context, path/root coherence and capture lifetime. |
| External allocation/replies: `Machine/Stores.lean`, `Program/Compile.lean`, `Program/Admit.lean` | Prepared-value relation, target/type extension, stable correspondence, no allocation on refused/stale reply, retained state. |
| Session/capability/ownership ledgers: `Api/HostSession.lean`, proposed boundary registry | Call IDs distinct from tokens, exact active/pending/consumed/retired contents, once-only transfer and cleanup responsibility. |
| Journal/diagnostics: `Run.lean`, `Api/Runner.lean`, machine trace | Authoritative command replay; separate semantic/holder/diagnostic projections; trace erasure has its own holder connector. |
| Typed world: `Laws/Program/Typed/World.lean`, `Validity.lean` | Declaration coverage, actual-state correspondence, freshness, per-token types, nested capabilities and target-spelling extension; monotone tables alone are insufficient. |

Current evidence: the arena/list laws and `refStepOfA` connection are proved.
`Projects` composition and projection-induced `Refines` are proved for the
same operation/answer carriers and exact corresponding steps. They do not
provide initialization, a whole-machine store replacement, ID renaming,
different event encodings, or multi-step/stuttering simulation automatically.

The current behavior observation includes the entire concrete `Stores`;
`Book` also shares a store carrier with equality. Introduce and prove a named
logical store projection/related-state connector before replacing list
layouts or hiding private state. Preserve existing statements until their
consumers have moved.

OCaml has fast/list-twin table, fiber-view, trace, memo, dispatcher, path and
environment interfaces. Their property controls are valuable; they are not
Lean certificates for those source implementations. Historical `.mli` references
to removed `OCaml5.Lib.Deque/Map` modules cannot count as current proof evidence.

## 8. Staged lowering and verified implementations

Two different compilation activities already exist:

- `compileEff` turns an `Eff` at a source point into first-order runtime `Prim`
  code referring back to the canonical program.
- `getMonoDecl?` / `translateClosure` translate persisted Lean function
  declarations, including the machine and compiler, through mono LCNF into
  target syntax. This route does not consume the `Prim` value produced above.

A future specializing/multistage compiler needs its own stages and connection
theorems. Neither route currently supplies a self-application theorem.
Each lower representation names its sort, signature, semantics, admission,
observation and connection to its predecessor.

| Connection | Mandatory contract | Current limit |
| --- | --- | --- |
| Admitted source to reference | Meaning under compatible explicit choices; results/causes, requests, public state and frontiers; state retained for finalization. | Existing fragment theorems are reusable, not a general external-program theorem. |
| Reference to compiled runtime | Corresponding preparation, registration, resume, frames, worlds, stores and queued work; progress/frontier relation. | Table-aware lane and stronger typing are required above. |
| Abstract storage to backing implementation | Initialization, operation/state/answer relation, aliases/snapshots, actions and progress; lift through machine and holder. | Arena laws do not certify actual OCaml arrays/maps. |
| Lean declarations to persisted compiler IR | Pinned compiler/erasure assumption or independently checked certificate; roots and complete dependency closure; layout/erased fields. | Reading compiler IR is not a compiler correctness proof. |
| Admitted compiler IR to target semantics | Refusing reader; value/layout relation; each operation/rewrite/extern justified; target exceptions, refusals and frontiers distinguished. | Current evaluator/vector evidence covers selected closures, not the whole machine. |
| Target syntax to bytes | Exact printer/reader image or independent artifact validation; naming/layout and runtime primitive references. | Evaluating in-memory syntax does not validate printed/parsed OCaml. |
| Artifact to actual execution | Compiler/runtime/ABI/FFI versions and semantics, scalar/memory/ownership policy, scheduling and host-adapter connection. | Compiled execution and host behavior are separate trust boundaries. |
| `Eff` to Effect TypeScript | Program printer/reader profile and pinned runtime behavior on a named observation. | Separate from a future LCNF-to-TypeScript backend for the machine itself. |

Every validation certificate binds the exact artifact, admitted profile,
layout, extern table and toolchain pins. A universal semantic claim needs a
kernel-checked certificate or a proved-correct semantic checker; otherwise
that checker remains an explicit trust assumption. Independent finite tests
and structural validators cannot be promoted to semantic certificates.

A local optimization must produce only behavior allowed by the source under
the named observation and choice relation. Require no new stuck state for a
ready admitted operation. If one source step becomes several target steps,
give an internal-step bound or well-founded progress measure; do not allow
infinite stuttering to satisfy a vacuous safety simulation. Reverse behavior
inclusion and fair termination are separate obligations when claimed.

Use one coherent identity relation across returns, stored values, requests,
causes and later commands. Compiler stages that change work counts need a
budget correspondence; equal raw fuel is not automatically the right comparison.

Scalar policy covers every intermediate, including allocation IDs, tokens,
lengths, clocks and fuel. The present OCaml translation uses raw integer
addition for some Nat operations and clamps others; bounds on final answers
alone cannot justify unrestricted Nat semantics. Prefer exact representation
for an unbounded claim, or explicitly enforce a bounded profile with proved
intermediate bounds. `Array.push` lowering to list append also shows that a
source carrier's name does not establish its target representation or cost.

Rows 28/29/31 remain open: full lowering proof versus fragment/rule strategy,
the common target/legalization design and TypeScript read-back ordering.
This packet freezes the obligations each choice must satisfy, not those
implementation choices by implication. A scalar slice is a useful first
result, with whole-machine coverage remaining required-open.

## 9. Dependency order and finishing criteria

The sequence is:

1. **X0 — freeze the external and typing amendment.** Retain the new
   counterexamples; ratify §3/4 choices; reconcile existing frozen packets.
   Constructor/entry-path/refusal matrices and exact observations are present.
2. **X1 — declared capabilities and preparation.** Implement the registry
   connection, constructor-complete membership, boundary image, recursive
   preparation, alias and ownership laws. Migrate consuming typing judgments.
   Include the already-authorized generic-cell row/authoring work from
   decisions 42–43 where needed for the handle-through-Ref slice.
3. **X2 — keyed lifecycle.** Complete receipt/application/cancel/retire and
   cleanup semantics, both budgets, legacy-path disposition and exact image codec.
4. **X3 — reference connection.** Add table-aware reference hooks and keyed
   holder interpretation; prove preparation, transition, replay, frontier and
   DI-57 statements. Derive the old empty-table case as a corollary.
5. **X4 — checked application guarantee.** Connect checker/source admission
   to the strengthened typed state and all valid execution prefixes; close
   public checked/typed entry paths and binding-specific obligations.
6. **S0/S1 — first actual storage replacement.** Freeze the six interfaces
   alongside X0; follow row 85's first Ref arena consumer. Connect one real
   backing implementation, then lift through machine and holder observations.
7. **L0/L1 — one real target closure.** Specify compiler fragment/layout/scalars/
   externs alongside X0; prove or independently validate the selected lowering
   and artifact connection. Include a table-aware target entry.
8. **Compose and expand.** Compose X4/S1/L1 only after their input, identity,
   state, observation and progress relations match. Extend each runtime family
   and host binding with its own laws and evidence.

The first executable vertical slice is acquisition → prepared handle → Ref
storage/read → second external operation → release, with both normal and
interrupted/late-completion branches. It exercises the real boundary and first
storage interface together. It is a first acceptance slice, not the whole
external lane.

The current public native Ref rows and their lowering are Nat-specific. The
generic machine kernel and Arena laws do not by themselves make the proposed
handle-storing program admit. Expose the approved generic-cell operations and
their checker/face/typing connections as an explicit prerequisite of this
slice, retaining its connector to the current Nat specialization.

Full external completion requires all of §4/5/6, not just that first slice.
Universal host termination requires separately named host-response, fairness
and cleanup assumptions; a valid pending run remains legitimate behavior.

Additional module branches remain explicit:

| Future functionality | Semantic work that must precede its implementation claim |
| --- | --- |
| STM/transactions, rows 80/84 | Body profile, atomic/preemptible ownership, retained driver work/budget, selective rollback, nesting/retry registration and cleanup. A single-root budget lemma does not prove the embedded transaction connector. |
| Stored behavior values, row 82 | First-order reference into existing `Eff`, typed entry/captures, resolution, invocation versus captured context, lifetime and portability. |
| Latch/Queue/Pool/Semaphore, row 81 | Per-family wake selection/order/count, pending/captured cancellation, coalescing, reentrancy and cleanup. |
| Custom Clock/Random/context, row 83 | Service/profile meaning, inheritance, numerical/random-state policy and binding relation. |
| New value/error carriers | Existing sort's signature, admission, codecs, elimination laws and lowering; no payload erasure disguised as support. |

These branches do not block useful current-core slices; they do block claims
to the corresponding broader functionality.

Each slice lands beside the old representation/judgment with its connector,
migrates callers, then retires the old piece. Follow the existing generator
ownership, import boundaries and narrow verification rules. Proof receipts
record base/head, named statements and assumptions, changed paths, commands,
axiom output, positive/negative controls and remaining target/host boundaries.

## 10. Proposed rulings and review result

The existing remediation can retain its fork-only ledger, lookup/correspondence
laws and hand-first invariant work. For the broader objective, record these
reaffirmed requirements and proposed amendments before dispatch:

1. **Reaffirmed: external completion is mandatory.** Internal M6 progress is a provisional
   slice; final closure includes DI-57's table-aware reference, checked public
   boundary, both budgets and the complete lifecycle.
2. **Certified executable declarations at the boundary.** Keep `Val` unchanged;
   derive a registry from checked creation transitions and prove its exact
   connection to the typed world. Host replies cannot retype existing handles.
3. **Stable host resource identity and recursive preparation.** Use the
   boundary image/capability environment of §3, allocate only on selected
   application, support existing/nested/aliased resources and retain cleanup
   obligations at every cancellation point.
4. **Amend the structural membership judgment explicitly.** Shape and capability
   evidence recurse together over the actual representations; migrate all
   consuming proof obligations. Proving a checker against today's weaker
   predicate is insufficient.
5. **Reaffirmed: compose named semantic connections.** Storage and compiler work use the
   observation/identity/progress contracts above. Keep every unproved target,
   compiler, runtime and host assumption visible in the claim.
6. **One public typed host replay route.** Use the keyed journal/session path,
   preserve both budgets and record the API migration. Any raw-decision checker
   remains low-level evidence and cannot claim host-envelope conformance.

The packet defines the work and exposes the necessary amendments. It does
not establish that the runtime or any backend already satisfies them.

## Evidence receipt

No production file, existing research plan, decision record, root import or
generated file was changed by this work. `docs/STATE.md` was already modified
by concurrent work and was left alone. No commit or push.

Commands, run serially in this working tree:

`lake env lean -M6144 -DwarningAsError=true docs/research/2026-09-30-external-runtime-contract/Probe.lean`

`lake env lean -M6144 -DwarningAsError=true docs/research/2026-09-30-external-runtime-contract/PredicateProbe.lean`

Results are retained in [probe.log](2026-09-30-external-runtime-contract/probe.log)
and [predicate-probe.log](2026-09-30-external-runtime-contract/predicate-probe.log).
The first contains 11 passing finite guards plus the checked-source-type
theorem at `[propext, Quot.sound]`. The second contains five kernel-checked
predicate facts within that ceiling. Neither file is a production battery or
a proof of the proposed repair.

`python3 docs/research/2026-09-30-external-runtime-contract/verify_packet.py`

Result: exit 0; all 20 current `Ty` constructors appear exactly once in the
matrix, local evidence links resolve, probe outputs contain no failed checks
or unexpected axioms, and the retained artifact hashes agree with
[sha256.json](2026-09-30-external-runtime-contract/sha256.json).

Read-only parallel audits separately covered external semantics, runtime
structures and compiler stages. Findings were reconciled against current
source and the register. No broad build or full coverage/trust sweep was
requested or run for this design packet.
