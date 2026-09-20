# State, primitives, and refinement: architecture plan

This plan fixes the interfaces to settle before the typed-state ledger is pinned. It does not
implement the proposed machine changes or claim that the surveyed APIs or backends agree.
The semantic owner is docs/core/machine-state.md; decisions live only in
docs/core/decisions.md. This file is the implementation plan and evidence record behind them.

Base: 5d6c70da on refactor/phase1-phase3. Lean is pinned at v4.33.1; the behavioral reference is
vendor/effect-4.0.0-rc.112. The earlier tooling branch codex/typed-state-tooling was paused at
the scanner repair f6f9f793; its declaration/frame/ledger work was checkpointed as three
commits on 2026-09-19 and §14 sequences its merge as the first slices.
No machine or language implementation is authorized by the recommendations in this plan.

§14 (2026-09-19) is the short form for the implementer: the D0–D7 stages re-cut as slices with
files, statements, deletions and red controls, from
`docs/research/2026-09-19-plan-deep-dive-review.md`. Read §14 first; §§1–13 are the contracts
and the evidence record behind it.

The checked critique follow-up is `docs/research/2026-09-19-critique-response.md`. It refines
this plan with scope-correct composition, exact term transport, a driver-continuation contract,
and fixed-parameter container/scalar laws. It does not approve the open semantic proposals.

The subsequent `docs/research/2026-09-19-implementation-audit-and-fusion-analysis.md` is retained
unchanged as review input. Its accepted findings and corrections are incorporated below;
§13 records their disposition against cc28511c. Its recommendations do not rule rows 78–83.

## 1. What is settled, and what this packet completes

The owner approved HandlesFit with Val.hasTy unchanged, and per-cell Ref/Deferred types,
including memo cells. Rows 44–45 record that approval. Rows 42–43 already authorize generic
cell operations and binder terms for atomic updates. DI-11 already chooses composite programs
for Queue, Mailbox and PubSub. DI-89 already separates core constructors, generated first-order
rows, and Forms expansions with typing and behavior laws.

The new questions are narrower: the observable contract of those compositions; completion and
memo storage; a scheduled-wake primitive; transaction admission; stored behavior values; and
environment profiles. These are proposals in rows 78–83, not approvals inferred from a scout.

The central task is representation and composition. Reuse the data structures, interpretations
and proof infrastructure already present; choose the few shared interfaces that let them fit
together, and prove their reusable laws once. Further machinery is justified by a concrete
missing connection, not by a requirement to add a gate for every feature. Known future needs
can reserve checked signatures and law statements now, with implementations left explicitly
absent. Completing every future module is not a prerequisite for settling these interfaces.

Done for this design stage means:

1. Every state family and surveyed API family has an owner, representation, primitive
   dependencies, observation, and explicit remaining obligations.
2. The meaning-to-machine, storage-refinement, lowering, and execution connections are separate.
3. Future features cannot bypass transaction admission, nested-handle typing, or wake ownership.
4. The sequence names acceptance and deletions, and does not make all backends a prerequisite
   for completing the typed-state milestone.
5. Actual source checks and finite experiments are distinguished from proposed proofs.

The full transcripts were consulted: session 2c0a6cf4-1df8-4f70-a714-4ca808700f3e and scout
transcripts agent-a428f7455c49c54b1 and agent-ad290c23f2d717271 under the owner's Claude project
directory. Their retained deliverables are the STM scout, stateful API catalogue, and corrected
stores/log map dated 2026-09-19. Those scouts explicitly reported source reading, not execution
or proof. This review adds the finite controls in §10.

## 2. Four connections, one program language

Eff stays the sole stored program syntax. The existing reference interpretation and logical
carriers remain semantic views of Eff; target IRs remain lowerings, not alternate authoring
languages. A proof-only algebra may contain Lean functions. Stored programs and state values
must contain first-order data, never host closures, Expr, host promises, or runtime objects.

The intended proof chain is:

    Eff under an admitted profile and explicit choices
      → reference meaning / reference machine
      → executable Lean machine using a storage implementation
      → admitted LCNF or Lean IR and a target representation
      → compiled artifact plus its runtime and host adapter

These arrows need different evidence:

| Connection | Required statement | Current reusable asset | Still owed |
| --- | --- | --- | --- |
| Program meaning to machine | The named fragment has the same selected observation under related complete choices; unfinished runs remain unfinished | Straight/Looped results, reference scheduler, Book/BMeans bridges | Concurrent invariant and a behavior contract per new composed module; typing alone proves neither atomicity nor liveness |
| Storage implementation to model | Each operation preserves a representation relation, its result, and ordered emitted actions | Existing pure store operations; OCaml interfaces, fast/list instances and property tests | Lean relations/laws for replacements and lifting through the machine |
| Lean through LCNF/IR to target syntax | Name the Lean compiler/erasure assumption or verify that connection; then relate IR evaluation on a named scalar/extern domain, refusing unsupported translation | Existing translator, evaluators, validity and rule summaries | Separate definition-to-IR and IR-to-target evidence; semantic translation proofs or checked per-artifact certificates on selected fragments |
| Target artifact to execution | Connect in-memory target syntax to printed bytes, then name compiler/runtime/ABI, primitive and host contracts | OCaml build and differential infrastructure; Lean compiler/runtime | Explicit remaining compiler/runtime trust; separate native, LLVM and Wasm admission/probes |

Book currently varies code while keeping the same St and equal stores
(src/Effect4/Laws/Machine/Book.lean). It cannot be cited as the missing container-refinement
theorem. Reuse its replay-lifting structure by adding a separate connector with related stores;
do not silently change a frozen theorem.

### How module proofs compose

Reuse the existing store/fiber signature split, reference interpretation and
Laws/Effects/Protocol.Typed for world-indexed typing, weakening and sequencing. The meaning
of a new primitive is its state transition, answer and explicit delivery actions. Its
implementation proof relates those outputs to its logical operation. A module composed from
those primitives has a record invariant and a public operation specification; atomic modify
provides a candidate linearization point, whose relationship to the surrounding concurrent
program still has to be proved.

For a composed module, state the allowed interference between its primitive steps and prove
that its public operation simulates the selected abstract operation under compatible choices.
A return/error postcondition, preservation under interference, cancellation/resource cleanup,
and an optional termination/progress claim are separate clauses. Lift these local statements
through the existing operational/replay machinery. A typing protocol by itself proves none of
mutual exclusion, linearizability, deadlock freedom or fairness. Add only the missing proof
rules demonstrated by the first real module; do not invent a second evaluator or an entire
concurrent program logic merely to name the intended laws.

For syntax composition, reuse the checked `composeAt_typed` and term environment-transport
laws in the critique packet. Extend transport to the selected Eff meaning, then derive identity
and associativity there using the existing semantic bind laws. Start with Straight; Looped
additionally needs its fuel/termination and state/error observations. Neither the typing
theorem nor finite straight-line examples prove these general behavior laws. The two associated
syntax trees need not be equal; normalize grade joins or state the grade equality used.

## 3. Observations must precede representation changes

The current Obs observes every fiber exit and the full Stores record
(src/Effect4/Laws/Machine/Behaviour.lean). It excludes the machine trace. Run.Observation also
exposes supervision and protocol information. These are distinct observations.

Consequences:

- Replacing ordered memo lists with sorted maps is not equality of today's Obs.
- A TxOpen buffer placed in Stores becomes observable under that definition.
- Private cells and watcher fibers introduced by a library expansion cannot disappear from
  today's observation by assertion.
- A different wake schedule can change values, failures and termination, not just trace text.

Keep existing observations and theorems intact. Add a named logical projection or state
relation, with a connector stating exactly what is retained and hidden. Partition observations
by use rather than choosing four event constructors once for every future consumer:

| View | Retains | Rules |
| --- | --- | --- |
| Semantic behavior | Public results/causes, admitted host interactions, public resource state, termination/frontier distinction | State after ordinary failure remains available to cleanup; transactional rollback has its own scope |
| Holder/replay | Command journal and answer correspondence, pending/retired keys, frontier, supervision needed by the API | The run journal remains authoritative at the run layer; removing diagnostic tracing must not change this view |
| Diagnostic | Frame events, profiling, explanatory scheduling detail | Erasure is licensed only by a theorem that it cannot affect semantic or holder behavior |

A matching relation for decisions is required when expansions add fibers, allocations or steps.
Reusing the same raw tape or equal numeric fuel is generally not meaningful. Public-handle
renaming must be consistent across outputs, stored values and future commands; extra private
handles require an ownership/visibility invariant. Diagnostic filtering does not license a
different scheduling decision to become invisible when it changes an exit.

For deterministic related inputs, seek equality at matched observation boundaries. For a
restricted execution profile, state inclusion of target behaviors in allowed source behaviors
and its assumptions. Equality of behavior sets needs the converse direction too. Neither
finite tests nor a single successful terminal execution establish fairness or divergence claims.

Fix what counts as a behavior before using inclusion: finite prefixes, returned outcomes and
maximal executions give different obligations. The retained silent-spin example proves only
preservation of a relation, not a step simulation or full behavior inclusion. When a profile
promises progress, state no-new-stuck conditions for ready operations and control infinite
internal stuttering, for example by a well-founded measure. Eventual completion or starvation
freedom must quantify over every allowed fair execution with the required external responses.
An existential path to a result does not suffice: a transition system can offer both that path
and an infinite self-loop. Blocking APIs do not acquire a universal termination obligation.

This follows the useful shape of the CompCert semantic-preservation contract: a named source
semantics, target semantics and observation, with allowed behaviors explicit. It imports no
CompCert theorem into Eff. See [CompCert's semantic-preservation contract](https://compcert.org/man/manual001.html), §1.2.

## 4. State inventory and owners

This is an inventory of semantic roles, not a proposal to add a store for every row.

| State family | Logical contents | Representation requirements / owner |
| --- | --- | --- |
| Ref arena | Stable cell identity and a current Val | Dense allocation and replacement; no delete/reuse without a generation policy; atomic binder-term read/modify/write |
| Deferred arena | Absent or admitted Completion; registrations and ordered owed delivery | User and memo populations share per-cell typing; ofRefGet stays a deferred read at resume time |
| Scopes and releases | Scope identities, closing state/exit, ordered finalizers, captured code references | Preserve sequential/parallel strategy, late registration, interruption and cleanup state; code references are valid first-order data |
| Memo world | Layer identity, parent lookup, observers, resource scope and promise identity | Remove duplicated effect only with cell-based census witnesses; specify duplicate/iteration policy before changing containers |
| Fibers and races | Saved computation, owner/parentage, pending tokens, observers, children, outcomes and race entrants | Preserve delivery/cleanup order and public supervision; completed-exit cache must equal its named projection |
| Dispatcher and wakes | Owner, priority, order, pending/scheduled state, cancellation and callback generation | FIFO/priority where required; snapshot versus live traversal, coalescing and reentrant enqueue are family-specific |
| Clock/timers | Logical time, deadlines, tie order, registrations and an advance in progress | Time advances by admitted input; preserve pause/refuel and sleep ordering; custom Clock is a separate service-profile decision |
| Context/services | Typed names, inherited/provided values, scheduler-sensitive references | Context lookup/override laws; configuration is data; behavior-valued services need code-reference admission |
| Captures and paths | Code identity/position, captured values and selected context policy | Resolution and capture typing; lifetime and portability; no automatic promotion of the entire machine Capture record |
| External interaction | Request/answer correspondence, identity and admissibility, queued answers | Foreign values are admitted at a typed seam; unresolved input is a frontier, not a failure |
| Journals and diagnostic traces | Played commands and observations in their distinct roles | Authoritative journal append/replay laws; diagnostic sink erasure is separate |
| Latch (candidate) | Open state and pending/scheduled registrations | Proposed smallest scheduled-wake consumer; payload Unit does not remove handle-liveness/cancellation obligations |
| TxRef and active attempt (candidate) | Typed cell values, registrations; owner, ordered accesses and buffered writes during an attempt | Transaction protocol and rollback scope first; active-attempt placement follows its observation and ownership proof |
| Composed module state | Records, lists, maps, handles and code references inside ordinary Refs | No Queue/Cache/Pool store by default; specialized physical layouts require refinement of this meaning |
| Typed world (ghost) | Fiber result/error types and per-cell types, handle coverage, code/capture certificates | Laws-only; extension and mutable-cell compatibility; no runtime type tags introduced by HandlesFit |

“Completion as data” is scoped to the admitted completion alphabet. It does not ban stored
first-order program references in finalizers or future behavior values, and it does not claim
to implement arbitrary rc.112 Deferred.completeWith effects. Narrowing the carrier also does not turn poll
into a stored-exit query: ofRefGet is not yet an exit. Preserve DI-97's ruled internal Boolean
poll and signed target answer-type exception through D2. A pure transition can read the Stores
argument; the issue is that reading at poll time changes a delayed read's timing. A future
faithful rc.112 poll returns stored behavior without executing it and needs a separately
admitted value/signature, handle/capture typing, lifetime and invocation contract. This migration
neither supplies that carrier nor retires the current row.

Identity types should distinguish scopes, finalizers, park tokens and races as well as the
existing fiber/ref/deferred/memo identities. Shared counters are still permitted. Numeric
freshness needs a target-domain law: type wrappers do not prevent integer overflow.

## 5. Small lawful interfaces, not one universal container

Reuse the existing OCaml seven-parameter functor and its list twins. Move semantic contracts
upstream into Lean, then migrate one family at a time. A generic interface mixing allocation,
key lookup, ordered draining and tracing would conceal the laws that matter.

| Interface | Operations to expose when required | Laws and decisive counterexamples |
| --- | --- | --- |
| Dense arena | empty, size, get, replace-existing, allocate | Fresh key equals old extent; domain grows by one; same/other lookup; missing replacement policy; old snapshots unchanged |
| Keyed table | lookup, insert/replace/delete under a named policy, observed enumeration | Key equality/hash coherence; first/last duplicate policy; stable iteration when observed; sparse keys are not allocated by cardinality |
| Ordered work sequence | enqueue, cancellation by identity, take/sweep, snapshot drain | Priority and FIFO where specified; exactly which batch cancellation affects; snapshot versus live traversal and reentrant admission; no dropped/duplicate actions |
| Append sequence | append batch, length/index, projection | No reordering or loss; journal persistence; a lossy diagnostic ring is not an implementation of the authoritative journal |
| Persistent path/environment | get, snoc, prefix, resolve | Position/capture coherence, alias preservation, resolution in the owning code object |
| Derived view | query/update through its owner | Cached completed exits and similar views equal a specified base projection after every operation |

Lists can be proof instances. Arrays, persistent maps/deques, or owned mutable storage are
implementations. Every implementation must preserve all retained snapshots and aliases under
its payload/heap contract. Private construction followed by freezing, copying before updates,
persistent sharing, or proved ownership can each satisfy that obligation; unique ownership and
copy-on-write are not the only choices. One scheduler thread does not imply unique ownership.
The existing OCaml append sequence uses privately filled, then frozen array chunks
(ocaml/engine/e4_log.ml); it is a reuse example, not a Lean refinement certificate. Target data
layout and memory management belong below these contracts.

For an exact abstraction alpha from a concrete container to its model, the desired shape is:

    WF c → getC c k = getM (alpha c) k
    WF c → let c' := setC c k v
      alpha c' = setM (alpha c) k v ∧ WF c'
    WF c → allocC c v = (k, c') →
      allocM (alpha c) v = (k, alpha c') ∧ WF c'

Where representations intentionally quotient order/duplicates, use a named logical projection
or a relation; neither needs an inverse recovering the old concrete list:

    Rel c m → stepC c input = (outC, c') →
      ∃ outM m', stepM m input = (outM, m') ∧
        OutputRel outC outM ∧ Rel c' m'

These are design sketches, not elaborated declarations. A dispatcher may drain a snapshot while
a Semaphore callback traverses a live waiter set; neither policy is universal. Initialization, definedness, relation
preservation, actions, and observations are all required. Machine lifting may need stuttering
and progress obligations so an implementation cannot satisfy a relation by doing nothing.

## 6. Primitive and language basis

The catalogue's table has 20 API-family rows; Request/RequestResolver and ClockRef each group
multiple exports. It is a scoped family catalogue, not an exhaustive export inventory. The
following crosswalk records all its rows, plus the transactional family.

| Family | Shared basis | Extra contract before claiming agreement |
| --- | --- | --- |
| Latch | Candidate scheduled-wake primitive | Inline versus scheduled open, captured batch cancellation, coalescing, opener dispatcher |
| Semaphore, PartitionedSemaphore | Ref + atomic modify + ordered wait protocol + iteration/maps | Permit selection at task time, losers' position, partition fairness, cancellation and reentrancy |
| Queue, PubSub | Ref payloads + modify + Deferred/Latch + scope | Maker versus caller dispatcher, task-time repoll, capacity/shutdown/backpressure/replay, public versus helper identities |
| SynchronizedRef, SubscriptionRef | Ref + permit protocol; PubSub for changes | Permit held across effectful update and interruption; stream surface remains the Stream packet |
| FiberHandle, FiberSet, FiberMap | Ref/maps + Deferred + fork/await/interrupt | Watcher fiber is not an exit observer without a timing and visibility argument; lifecycle cleanup |
| Cache, ScopedCache, RcMap, RcRef, Pool | Maps/Ref + scopes + clock + fibers + typed stored behavior | Key equality, acquisition context, miss coalescing, eviction/finalization, expiry and Pool's counted wake |
| Request/RequestResolver | Resolver identity + batch map + Deferred + fork/yield + stored behavior | Batch boundary/identity, cancellation and partial answers; callback profile |
| Schedule | Descriptor + pure step + clock/sleep/iterate | Retry/repeat state; timeout requires first-exit race with cleanup/loser behavior checked |
| ClockRef, Random, References | Context descriptors + logical timer or Ref-held generator state | Default/configured profiles, inheritance/splitting, seed/algorithm/number semantics, unsupported custom behavior |
| TxRef and ten derived Tx modules | Generic transactional cells + atomic update terms + scoped transaction control + retry/wake protocol | §7; derived modules use no extra machine store by default |

Generic Ref/Deferred rows and binder-term atomic modify precede the semantic proof arms that
use them. Do not restart TxRef at number-only after the generic infrastructure lands.
The user-approved world supplies nested handle typing; coverage and compatibility are distinct
requirements, including handles inside maps, lists, exits and captured environments.

Map atoms need a named admitted key domain and equality policy. The bounded rc.112 probe in
§10 finds structural equality for two plain-object keys; native JS Map differs. Custom Equal/
Hash, function identity, numbers and cyclic foreign objects require explicit support/refusal.
A hash table optimization owes equality/hash coherence, not just lookup examples.

Stored behavior is a typed code reference into the existing Eff owner, plus typed captures.
Before adding a Val/Ty form, settle code identity (module/digest plus entry), resolution, captured
versus invocation context, capabilities/lifetime, recursive calls, admission summaries,
snapshot/wire policy and printer/reader agreement. Code/type references may be opaque below
their owner so Ty and Schema do not import Eff. Captured values carry no host closures.
Capture currently also carries execution details; copying its entire shape into public Val
would freeze fuel/tape/context choices accidentally.

Vendored modules enter through DI-89's rows/Forms, with a pinned export inventory, generated
signatures, named refusals and a module-specific behavior contract. Printing an expansion tests
the expansion on the host; it does not test the native rc.112 API of the same name. Compare both
explicitly when claiming agreement. Library-first is an architectural ruling, not a theorem
that every exported overload has been represented.

### Future compositions and deliberately unselected scope

The following is a candidate menu, not an implementation backlog. Stream and Channel should
first have contracts describing their intended composition as Eff programs; implement only the
pieces a selected consumer needs. Logging is not a required feature. Context extensions and
other derived services likewise start from ordinary programs and existing context operations.
Use the deferred-contract pattern in §9 where the intended shape is useful before the body.

The catalogue does not establish coverage of all Effect exports. If that broader claim is ever
made, its inventory must also account for adjacent families such as these:

| Family outside the 20-row table | Existing direction / design requirement |
| --- | --- |
| Stream, Channel, Sink | DI-11/DI-89 reserve a separate packet; scoped pull, backpressure, cancellation, buffering and consumer/producer lifetime must be related to the shared primitives |
| Config and external services/resources | Existing schema/admission and host-answer seam; name unsupported carriers and operations; OS/network handles stay explicit capabilities rather than hidden state |
| Logger, Metric, Tracer and context extensions | Select only for a concrete application need; distinguish program-visible context/results from diagnostics; stateful callbacks use the shared stored-behavior contract |
| Mailbox and other aliases/wrappers | DI-11's composition direction applies to Mailbox; enumerate pinned aliases and overloads before claiming a concrete module implementation |
| Transactional collections | The ten Tx modules sit over TxRef but their generic value/operation signatures and caller-supplied code must pass admission individually |

For each selected vendor module, the bounded declaration reader supplies the expected export
inventory independently of the implementations. Join every export/overload to a core primitive,
row, Forms expansion, foreign boundary, or located refusal. Attach the observation/profile and
proof obligations to that mapping. Unclassified exports are unknown work; they cannot disappear
because a report counts only implemented declarations. Pure value-library modules use local
receipts unless they introduce one of the semantic connections this plan identifies.

This packet captures the shared representation requirements and the surveyed families, not a
closed proof that no future API can need another primitive. Add a primitive only with a missing
expressivity/behavior witness or a measured optimization plus its refinement obligation.

## 7. Transactions: specify control before erasing versions

Recommendation for review: a restricted atomic transaction profile on the existing evaluator,
with a logical handler/relation as the specification. A versioned/preemptible implementation is
a future alternative only if it proves its relation to that contract, including retry and
termination behavior. The owner has not approved the atomic profile.

Version erasure requires proof, not merely PreventSchedulerYield:

1. Admission composes through every called/stored program, service implementation, finalizer
   and nested transaction. Unknown foreign code is refused without a suitable summary.
2. No admitted action can execute another fiber inline, change protected scheduling state,
   deliver an interrupt/observer, park/fork, or admit a conflicting host action before close.
3. Ownership covers the entire admitted attempt under the selected execution contract. A fuel
   frontier is not release, failure, or permission for a conflicting action. Under replay,
   restart from the initial state with compatible inputs; under suspension, retain the owner
   and all pending driver work. The choice and changed-budget relation are D1 obligations below.
4. Buffered reads see the latest own write; the ordered dynamic access list matches executed
   accesses. A static footprint is a conservative proof aid, not the retry subscription set.
5. Failure/retry discards transactional writes. Allocation and any admitted ordinary Ref writes
   retain their separately specified behavior; rc.112 does not roll back the whole world.
6. Retry closes the attempt and registers one identity across its accessed cells before yielding
   control. Wake/cancel removes it from all cells before guarded resumption. Nested tx is flat.
7. Commit updates atomically and owes the specified scheduled actions. rc.112 schedules retry
   callbacks for every accessed cell, even unchanged/read-only cells, on the committer's
   dispatcher. Versions change only for changed values: notification is not version
   invalidation. With the ordinary queued dispatcher, one subscription can yield a callback
   per accessed cell; cleanup uses the shared registration identity and the resume guard
   prevents repeated effective resumption. This is not Latch's one coalesced broadcast task.

### The execution contract needed by ownership

`driveState` retains its command remainder; `driveState_add` in
src/Effect4/Laws/Machine/Approximation.lean already proves the command-loop split/resume law.
The current decision/session projections discard driver remainder. The retained probe shows
that another evaluate command does not resume that particular frontier, whereas supplying the
saved remainder does. It does not establish that every frontier is permanently stuck.

Keep two contracts available for the owner decision in row 80:

- **Finite replay:** restart from the initial state, fixing compilation inputs and relating
  complete compatible decisions/answers at the chosen budgets. `journal_replays` in
  src/Effect4/Laws/Run.lean proves exact replay at the original budget; it does not prove that
  an existing host journal remains compatible after changing the budget. Reuse the approximation
  laws within their stated scope, then prove any needed changed-budget observation relation.
  Replaying recorded inputs does not authorize repeating external side effects.
- **Driver suspension:** retain commands plus the outer dispatcher batch/task suffix,
  clock/replay position and other pending control work required by the chosen driver. A machine
  and a single dispatcher snapshot are not yet a complete suspension specification. Lift the
  existing split/resume law and generic journal-action laws to that carrier; identify the new
  connector obligations rather than assume all replay laws must be rebuilt.

Neither alternative is selected by this audit. Conditional transaction contracts can be stated
now, but no across-budget ownership claim follows from today's projected session alone.
Write-only retry notification likewise needs a named profile and behavior/progress relation;
hiding diagnostic events alone does not justify it.

Prefer a pure/TxRef first profile; adding other sync effects is a separate admission extension.
The owner decides retry under cause-catching, allocation visibility and the exact effect
fragment. Empty-access retry, cancellation and retained allocation need explicit clauses.

The source permits interleaving that the atomic profile removes. A candidate falsifier to an
unqualified equality claim is a stale read driving an attempt into an infinite loop before
validation. Therefore a theorem about terminating validated attempts is not a theorem about
divergence. The scout's suspected lost wakeup remains unexecuted; this packet does not report
it as an rc.112 defect.

Plain Effect.tx is not automatically the protected target profile. Either the emitted program
installs the required scheduler setting and respects the admission conditions, or the agreement
statement restricts host schedules. Both require tests and a named relation.

## 8. Lowering profiles and evidence

Freeze contracts now; implement fast replacements after a first small refinement slice validates
them. Do not require a universal compiler proof or every backend before finishing typed state.

| Route | Present evidence/structure | Required next boundary |
| --- | --- | --- |
| Lean definitions and native Lean IR/C | Pinned compiler source supplies the LCNF-to-IR and runtime compilation route | Source proofs remain conditional on compiler/runtime behavior; select executable roots and run the chosen state/primitive probes |
| Direct LLVM | Pinned Lean source contains an emitter and runtime-bitcode linkage | Probe supported forms, runtime ABI and layout separately; v4.33.1 EmitLLVM hardcodes size_t=i64 with a target-triple TODO |
| OCaml | LCNF translator, fast/list engine instances, interfaces and property tests | Lean container relations; scalar/extern contracts; generated independent model oracle; remove hand semantic prelude code family by family |
| Wasm | Intended low-level target route | Build compatible runtime/dependencies and host imports; check word size, memory/threads, stack/tail calls, allocation and ABI; no ready repo route established by this audit |
| Effect TypeScript | Existing Eff printer/reader and pinned behavioral oracle | Module profile/expansion versus native API comparison; this route remains distinct from a future LCNF TypeScript backend |

Per-target admission must cover *intermediate* arithmetic, fresh IDs, sizes, clock arithmetic and
priorities. Unbounded Lean Nat is not saturated or wrapping OCaml int. A target either implements
exact scalars, refuses out-of-domain execution under a specified contract, or proves the whole
reachable fragment bounded. Input bounds and a passing corpus alone are insufficient.

LCNF Rules currently checks structural rule summaries, not semantic legalization proofs.
TargetLeanNative reflects layouts, not a whole-machine evaluator. The historical type-algebra
vector comparisons do not establish current whole-machine lowering. LcnfMl reads in-memory
Ml.Syntax; it does not parse emitted OCaml text. Printer/read-back exactness and compiled-byte
execution are separate obligations. Lean definition-to-LCNF/IR compilation also remains an
explicit trusted edge unless separately verified or validated. Preserve these useful checks
while reporting their actual scope.

For D5, distinguish the logical Lean carrier from what each target actually emits. The current
OCaml translator maps Array to list, Array.push to list append, and array lookup to List.nth
(src/OCaml5/Lcnf/Types.lean and src/OCaml5/Lcnf/Translate.lean). Merely replacing a Lean List by
Array therefore establishes no OCaml speedup. Inspect the emitted operations and measure the
selected workload after its refinement laws hold. Do not infer a regression without a compared
baseline, ban Lean Array, or require an RRB vector before proving the storage interface.
Reuse the existing persistent target containers where their operation and retention laws fit;
one logical interface can have different lawful physical representations on different targets.

The official Lean reference separates kernel checking from compilation; the default documented
route emits C. LLVM's Wasm linker documentation supplies linking constraints, not an Eff port:
[Lean compilation pipeline](https://lean-lang.org/doc/reference/latest/Elaboration-and-Compilation/);
[LLVM Wasm linking](https://lld.llvm.org/WebAssembly.html).
The project's pinned compiler source, not the moving manual version, owns concrete API facts.

## 9. Shared contracts and proof reuse

### Local fold reuse within the existing boundary

Decisions 34 and 40 remain in force: no generated-fusion framework, census gate, or conversion
campaign for the thirteen exemptions. Reuse existing algebras, connectors and uniqueness laws
when they simplify a concrete owed proof. Keep the checked short transport proofs where they
already serve the contract; no uniform presentation is required.

Function-valued proof carriers are supported by Program/FoldOf and used by the denotation
algebras in src/Effect4/Laws/Program/Folds/Denote.lean. Weakening and term evaluation already have
parameterized algebras in src/Effect4/Program/Folds/Term.lean; src/Effect4/Program/Fold.lean supplies
TermHom and hom_eq_cata_term. A composed candidate satisfying those constructor equations can use
uniqueness locally. The environment lookup/transport equation still has to be proved; a fold
law does not discover it. No new `cata_term_fusion` API is needed for that argument.

Use each sort's own signature: the Eff fold is mutual, and Term, CauseTerm and operation
payloads are leaves for that fold. Its uniqueness theorem does not discharge their laws,
scheduler invariants, transaction isolation, or progress. Such operational proofs may still
reuse algebra/transport lemmas for individual components. A fold equality also does not change
executable callers or remove allocations. Any proposed pass fusion must supply constructor
compatibility, replace the executed traversal, and establish benefit on the selected target.

### Deferred implementations with useful composition now

Keep Eff, Ty, Val and the machine's existing state owners. Separate four roles in the interfaces
that need them; this is not a requirement for four new framework types per module:

| Role | Content | Reuse |
| --- | --- | --- |
| Signature | First-order operation names, arguments, answers, handles and configuration | Existing signatures and generated rows remain the source for clients and targets |
| Contract | Logical state, observations and allowed transitions or delivery actions | One meaning shared by implementations; unresolved profile choices stay parameters |
| Implementation | Executable operations interpreting the signature | Reference, efficient Lean and target-specific instances can occupy the same seam |
| Laws | Statements relating a particular implementation to the contract | Derived module proofs depend on these laws, then instantiate them for each implementation |

Derived APIs are primarily Eff programs composed from that basis. A Lean builder may be
parameterized while constructing a program; the resulting stored program remains first-order
Eff data. Proof-only interpretations may use Lean functions without putting those functions
into stored syntax. Prefer existing protocol/sequence laws and container interfaces to another
evaluator or a universal module framework. The first real consumer determines any missing law.

An unfinished module can therefore supply its public signature, contract and dependencies now.
Ordinary theorems can prove consequences for any implementation satisfying those laws. Later,
supplying an implementation and its law proofs discharges those parameters once for all derived
clients. A checked conditional theorem establishes the implication; it does not establish its
premises. Even a well-typed contract may be uninhabited until a model realizes it.

Reuse Batteries.Util.ProofWanted from the pinned Batteries revision
4488d40d070b9700d4d5a6aa342f0d40c31b2a2d: def_wanted records a missing implementation;
theorem_wanted/proof_wanted records a missing proof. Derived def_wanted bodies can thread
missing dependencies as explicit parameters. A theorem_wanted with a body is still a wanted
marker; publish an ordinary theorem when a conditional proof is actually complete. Wanted
commands have private/file-local bookkeeping, so stable cross-module interfaces are public
signatures and explicit contract parameters, not an assumption that the wanted notation works
as a cross-module linker.

A stub carries no executable implementation. Do not implement it as a default success, no-op,
fabricated failure or new hole constructor in Eff. Runtime entry points and lowering require
their executable dependencies to be supplied; erasing proof parameters supplies no missing
operation. Recursive programs use the existing recursion representation and induction laws,
not circular placeholder dependencies.

Track implementation availability separately from proof status, using existing declaration
identities and proof references. The paused Obligation carrier covers propositions; its current
command neither derives the whole dependency graph nor integrates missing implementations.
Connect wanted definitions only when the first consumer needs that view. Shared profile,
observation and assumption descriptions should be referenced by goals, not copied into each
one. This pattern requires no new stub framework or per-feature gate suite.

### Completing the existing tooling seam

Retain the scanner repair, direct declaration generation, named Aesop bank, kernel-checked
structural frames and shared theorem-reference validation from the paused tooling branch.
Their reusable portion belongs below both Laws and Conform; none enters runtime roots.

The concrete ledger still needs an independent goal producer from the invariant and actual
transitions. Enumerating authored obligation declarations alone lets a deleted declaration
disappear from the expected set. Counts and placeholder checks cannot detect that omission.

One typed in-memory description should drive clause/arm dependencies, automatic frame attempts
and the required goal set. Use declaration identities and checked propositions; matcher indices
are provenance, not stable semantic IDs. Unsupported analysis refuses with a location. The
kernel must check each frame; a scanner's claimed disjointness never proves a clause.

Use the existing Conform report model for target/input provenance and evidence grades, joined to
the shared proof references. Do not invent a second report framework or TSV authority. Tables,
JSON or diagrams may be disposable projections. Removing every existing TSV at once is not a
prerequisite; migrate consumers and delete each old authority at its owning slice.

Every semantic goal needs structured references for: fragment/profile, observation, decision
relation, representation relation, assumptions, actual theorem, input/source/toolchain identity,
and prerequisites. Keep intended proof dependencies separate from constants used by a checked
proof. A conditional theorem can be closed while its external premise remains an open boundary.

Suggested goal families, with actual names to freeze at declaration time:

| Family | What it establishes |
| --- | --- |
| Admission | Located refusal agrees with the admitted fragment; summaries compose |
| World | Coverage, nested HandlesFit, table extension and per-cell compatibility |
| Store | Same/other lookup, allocation, frame and alias laws; cached-view coherence |
| Wake | Ownership, pending/batch cancel, ordered delivery, stale/duplicate inertness |
| Control | Transaction isolation, rollback, flat nesting, retry cleanup and fuel resumption |
| Module | Typing plus a behavior law for each Forms expansion under its selected profile |
| Refinement | Initial states and operation/step simulation lift to the selected observation |
| Lowering | Definition-to-IR assumption/evidence, scalar/extern domain, IR evaluation relation, printer/read-back connection and pinned artifact execution evidence |

Aesop should consume small named banks for world/store/wake facts with positive and omitted-bank
controls. Keep inductions and metavariable-producing choices local. Proof search produces a
candidate; the kernel and axiom check establish admissible theorem evidence at [propext,
Quot.sound]. The core graph must not count finite host tests as proofs.

## 10. Checks performed and falsifiers still owed

Fresh finite control:

    bun docs/research/2026-09-19-state-refinement/probe.ts

It imports the vendored rc.112 source directly and supplies a deterministic manual scheduler
with automatic yielding disabled. The waiter reads a value after opening; the opener writes
one immediately after opening.

- Latch: waiter had not run before flush; final read was 1.
- Deferred: waiter ran inline; final read was 0.
- Interrupting a Latch waiter after schedule removed it from the captured batch (1 to 0);
  after flush it had not resumed.
- MutableHashMap coalesced two separately created plain-object keys into one entry; native
  JavaScript Map retained two.

These are finite host observations. They do not prove a composed implementation incorrect or a
generic wake law. They refute the design shortcut that changed wake timing cannot affect values,
and distinguish cancellation/equality cases the contracts must include. The checked script and
its output are retained beside this plan.

Source review also confirmed the existing OCaml interfaces/list twins/tests, Book's equal-store
restriction, Obs's concrete Stores field, and the pinned LLVM layout TODO. No new Lean
declarations, compiler targets or proof claims were produced in this design stage.

Use these unresolved behavior questions to guide each corresponding implementation, reusing
existing fixtures where they exercise the question and adding focused controls only where
the answer is missing:

- scope close versus late registration; memo hit/completion shared identity and build-once;
- scheduled cancellation, reentrant enqueue/flush, stale batches, dispatcher ownership,
  heterogeneous permit requests, queue shutdown/backpressure and counted Pool wakes;
- hidden behavior reentrancy, protected-context changes, swallowed/empty retry, read-only
  transaction wake, two-cell duplicate subscriptions, selective rollback and open-attempt fuel;
- retained snapshots, aliasing, sparse-key allocation, duplicate memo keys and cached exits;
- overflow of intermediates/counters, nested optional values, strings/bytes, invalid host answers,
  and native/Wasm runtime layout.

These are proposed falsifiers, not passing tests.

Document validation: python3 scripts/check-source-citations.py passed both citation checks
(4,065 existence tokens, zero baselined missing targets; no prohibited authored-document line
citations). The evidence-file hashes, 20-row inventory, unique decision IDs and separation of
approved rows 44–45 from open rows 78–83 were checked. git diff --check passed after formatting
repair. Three independent reviews covered transactions, stateful APIs and lowering; their
material corrections are incorporated above. No Lean/runtime source changed, so no Lean build
or whole-repository sweep was run for this documentation slice.

## 11. Landing sequence and finishing criteria

| Slice | Work | Acceptance and deletion |
| --- | --- | --- |
| D0: this packet | Reconcile research, record the approved world, correct authority overclaims, identify reusable interfaces | Representation owners and composition seams are explicit; remaining semantic choices stay open in the one register |
| D1: structural contract | Set observation/representation relation, completion and memo contract, identity policy, wake protocol, and replay-versus-suspension contract (§7); reserve signatures and scope-correct composition laws | Shared law statements and dependencies elaborate; reuse command-loop and transport laws; changed-budget claims have their own compatible-input premise; future bodies can remain wanted; frozen Obs stays intact |
| D2: completion/memo migration | Completion-valued cells/owed data beside the old representation, connector, callers, then old fields | Delayed Ref reads, memo sharing and DI-97's Boolean poll exception retained; twelve Deferred witnesses and layer memo clause revisited; obsolete shape/decoder invariants deleted; generated outputs re-cut |
| D3: world/language and ledger | Approved per-cell world, generic Ref/Deferred and binder-term atomic updates in their dependency order; independent transition-goal producer | Exact expected goals, frames, placeholders and dependencies; pinned semantic debt after D2; no claims that structural-frame premises are that debt |
| D4: typed-state proofs | S1/S2/S3 on the stable representation and declared assumptions | Exit typing theorem at its stated fragment/world; current trust ceiling; no full behavioral-equivalence claim from typing |
| D5: first storage refinement | Dense Ref arena: list model and efficient Lean implementation; join to existing OCaml interface/oracle with a target-specific carrier | Operation, well-formedness and retained-snapshot laws plus machine connector; verify actual target operations (Array currently lowers to List), then measure against a named baseline; delete the hand semantic prelude body only after its replacement agrees |
| D6: scheduled/module/control slices | Latch contract first if chosen, then groups from §6; transactions after isolation/admission and ownership contract; stored behaviors before their consumers | A behavior law per module/profile; wake-on-access distinct from version changes; any progress promise covers allowed executions, not just one successful path; no dedicated Queue/Pool store without new evidence and ruling |
| D7: target growth | Apply the established relations to other containers and one small lowering fragment; separate native/LLVM/Wasm probes | Per-target domain/runtime/ABI, Lean-to-IR trust or proof, IR-to-target and printer/bytes evidence; reusable lowering obligations instead of re-proving module semantics |

Rows 78–83 reserve semantic choices, not all useful work. Interface formation and conditional
composition proofs can proceed before all their implementations exist. Fast-container
implementation and new API families do not block the typed-state milestone once its
representation contract is fixed. The catalogue's proposed
“number-only TxRef first” and an automatic “all APIs after the milestone” are not imported as
new sequencing rules: generic language work already required by rows 42–43 must precede the
proofs that depend on it.

D5 and selected D6 consumers can proceed independently once their required contracts are fixed.
D7 starts with one admitted fragment using those contracts; it does not wait for every D6 API.
Their numerical order is not a new serial dependency between unrelated implementations.

Every slice names its deletion. Do not delete wake primitives solely from today's consumer count
while Tx/Latch contracts are being formed; after those contracts are fixed, retain only used
policies and deliberately named near-term dependencies. Do not duplicate the evaluator or
program syntax to make a transaction or target easier to implement.

## 12. Evidence pointers

- docs/core/machine-state.md: semantic owner; docs/core/decisions.md rows 41–45, 78–83:
  approved world and pending choices; docs/DESIGN-ISSUES.md DI-11 and DI-89: composition routes.
- docs/research/2026-09-19-stm-scout.md §§1–5 and
  docs/research/2026-09-19-stateful-api-catalogue.md §§1–5: primary reviewed research.
- docs/research/2026-09-19-stores-and-event-log-map.md: corrected inventory and migration radius.
- src/Effect4/Laws/Machine/Behaviour.lean, src/Effect4/Laws/Machine/Book.lean,
  src/Effect4/Laws/Effects/Protocol.lean: present observation, bridge and reusable protocol logic.
- src/Effect4/Machine/Wake.lean; vendor/effect-4.0.0-rc.112/src/internal/effect.ts:5568–5657;
  vendor/effect-4.0.0-rc.112/src/Effect.ts:24274–24354; vendor/effect-4.0.0-rc.112/src/TxRef.ts:
  wake and transaction sources.
- ocaml/engine/api_engine_ref.ml, ocaml/engine/externs.txt, ocaml/engine/test/prop_store.ml:
  existing implementation seam and finite evidence, not Lean certificates.
- tools/Conform/Lcnf/Rules.lean, tools/Conform/Effect4/TargetLeanNative.lean,
  tools/Conform/Effect4/LcnfSemantics.lean, tools/Conform/Effect4/LcnfMl.lean: evidence scope.
- docs/research/2026-09-19-state-refinement/closeout.md: tracked supporting reviews,
  worktree provenance and the paused tooling handoff.

## 13. Implementation/fusion audit disposition

Reviewed against cc28511c. The incoming audit is preserved byte-for-byte as historical input;
this plan owns the resulting implementation recommendations. Existing decisions remain in their
registers. No machine change, new semantic ruling or fresh execution result is implied.

| Incoming finding | Disposition in this plan |
| --- | --- |
| Public frontier loses continuation | Accept the missing outer-driver contract; §7 reuses driveState_add, preserves both owner choices, and corrects the same-budget scope of journal_replays. “Zombie forever” exceeds the retained probe. |
| composeAt association | Already a semantic obligation; §2 makes environment transport, observation and grade handling explicit. General Straight/Looped laws remain owed. |
| Completion collides with poll | §4/D2 now explicitly preserve DI-97. Purity does not prohibit reading an explicit store; executing a delayed read too early is the semantic error. No retirement is approved. |
| STM wake-on-access | Accept the source fact already present in §7; distinguish version updates, callback scheduling, cleanup and guarded resumption. A write-only policy needs its own behavior relation. |
| Array performance and snapshots | Accept target-operation inspection in §8/D5. Reject an unmeasured slowdown, a blanket Array ban, and RRB/uniqueness as the only routes to persistence; existing frozen chunks are a concrete counterexample. |
| Safety and progress | §3 separates them at the selected behavior boundary. Reject the suggested existential path as a starvation guarantee; an allowed infinite self-loop can coexist with a terminating path. |
| Fusion effectiveness | §9 retains the closed conversion campaign while permitting local reuse. Function carriers are supported; cited algebras already exist. The speculative proof-length comparison is not evidence, and fold equality alone does not optimize execution. |

Two evidence corrections matter when reading the supplied audit's baseline list. Equal frozen
Obs with different holder supervision shows that holder supervision cannot be recovered from
Obs, not the reverse factorization. The silent-spin fixture checks relation preservation only;
it does not prove a matching-step simulation. The original scalar controls remain finite target
hazards, not backend correctness results.

The new audit's reported Bun runs and additional straight-line checks have no retained runnable
receipt in that input; they are not counted as freshly reproduced evidence here. Source reading
confirms the poll/wake facts. The previously retained critique proofs/probes keep their existing
scope and receipts. This integration adds no new proof or benchmark result.

## 14. The slices (deep-dive review, 2026-09-19)

`docs/research/2026-09-19-plan-deep-dive-review.md` re-cut D0–D7 into slices after reading the
paused tooling worktree (built green at its last edit) and the tree. Its findings F1–F16 are the
reasons; this section is the order. Every slice names files, a statement or instrument, a
deletion, a red control and a narrow build in the note's §4. Rows 84–85 record its two
proposals; nothing here rules them.

The simplifications it adopts: the world is one record `⟨Γ, Π, Ρ, s⟩` ordered by table
extension and the existing `Stores.le`; the promise column is stated on `Completion` data,
which makes D2 a deletion and the first machine change; D5 is the `Arena` interface over which
`refStepOf` and its laws are restated, with `RefHeap` the list instance and the OCaml store the
trusted instance (row 85); `WakeList` is already the ordered-work interface of §5, and Latch its
named instance; two of the eleven hand predicates and five `Expect` constructors go; frames are
generated per written-field set; the ledger's goal set is the authored declarations joined to
the write-census holders by name; a first transaction profile on `TxBody ∩ Straight` needs no
across-budget ownership (row 84).

| slice | is | blocks on | deletes |
| --- | --- | --- | --- |
| T0 | the tooling worktree checkpointed as three commits on `codex/typed-state-tooling` | — | — (done) |
| T1 | `tools/ProofGraph` (references, search, ledger) with `Conform` and `Census` over it | T0 | 81 lines of duplicated validator/search |
| T2 | `#typed_state`: the skeleton elaborated in place, the named bank, the scanner refusals | T1 | `TypedStateGen.lean`, the emit driver, the generated `State.lean` body |
| T3 | `#frame_rules`; amend to per written-field set before M6 | T1 | — |
| T4 | `Obligation`, `#proof_wanted`, `#typed_state_obligations`; add `#typed_state_coverage` | T1 | the deleted-goal hazard |
| T5 | the wiring: roots, gate exemptions, `make check-typed-state`, three docs | T2–T4 | the `TypedStateGen` exemption |
| M1 | D2 = R1+R2: completion cells and owed resumes hold `Completion`; `MemoEntry.effect` gone | T5 (the gate re-cuts) | `CompletionShaped`, `DeferredOk.1`, `StoredCodeNoRace`, `DeferredCodes`, `denoteStored`, `STORES-FB-COMPLETION` |
| M2 | layer 1: `Typed/World.lean`, the columns on data, nine hand predicates, `Preds` instance | M1 | `ResumeOk`, `InterruptOnly`, five `Expect` constructors |
| M3 | the residual protocol: `OpOk`/`AnswerOk` under `#answer_gate`, `TypedProg`, `HandlesFit` | M2 | — |
| M4 | `Laws/Machine/Keeps.lean`; the existential `StackOk`; `popR_typed` | M3 | — |
| M5 | S1 `denoteR_typed`; `InterpTyped` for the hooks | M4 | — |
| M6 | S2 by ledger row: the ceiling pinned here; frames, delivery sites, operation families | M5, T3–T4 amendments; binder-term rows before the `refUpdate` family | — |
| M7 | S3 `run_typed` through `BMeans.exitOf`; no `badShape`; DI-17 | M6 | — |
| P1 | D1's Lean content: `Obs.semantic`, `Run.holder`, `Factors` promoted; R3 `parent`/`daemon` | — | the trace read in supervision |
| P2 | D5 re-scoped: `Arena`, `refStepOf` over it, the list instance | T1 | the Lean `Array` instance |
| P3 | R5: typed identities | — | numeric coincidences |
| P4 | D6 transactions v1 on `TxBody ∩ Straight`, per the scout §3 | M7, row 84 | versions, journal handle, conflict path |
| P5 | D6 Latch as the `WakeList` instance with its four controls | — | — |

D3's three parts are split across T4 (the ledger), M2 (layer 1) and the binder-term rows before
M6's `refUpdate` family. D4 is M5–M7. D7 stays as written, after P2. The pin of the semantic
obligation count moves to the start of M6, after M1 and M2, which is what rows 78 and 80 asked.
