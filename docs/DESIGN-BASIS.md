# Effect4 design basis

Effect4 adopts one well-founded algebraic proof carrier, one checked first-order
reification, relational semantics for open effect flow, and separately gated
host targets. This separation is the basis for the library; the cited
literature motivates its interfaces but does not prove that Effect4 models
Effect TypeScript or any host runtime.

Status: decision record begun 2026-08-31, reviewed 2026-09-05. Each DB row
below carries its current disposition. Flow-specific derivations describe the
archived route; current program syntax is `Eff` in `src/Effect4/Program/Eff.lean`.

## Re-review ruling

A fresh review of EffHOL, the current Lean reference pages, and the pinned
Lean 4.33.1 sources does not justify replacing the architecture above with a
larger foundational carrier. It does justify the extraction from Foldlab and
four library-level refinements that are now requirements:

1. The algebra is universe-polymorphic and exposes first-class model
   morphisms, rather than retaining CAS-specific `Type`-only declarations or
   a second morphism predicate.
2. EffHOL separates kinds, types, programs, logical indices, expressions, and
   specifications. Effect4 follows that organization: its program semantics
   precede its logic, while `wlp`, totality, and realizability live in the
   logic/classification layer rather than in `Program` or `Flow`.
3. Lean `Expr` and environment state remain metaprogramming inputs. Persistent
   entries are sorted, serializable first-order rows, and the generated
   declaration/type closure is checked after elaboration. No elaborator
   closure becomes semantic data.
4. The runtime uses an error-and-state result that retains final state.
   Backtracking or rollback is requested explicitly; it is not an accidental
   consequence of transformer order or exception handling.

The online Lean API pages currently describe a newer documentation build than
the project toolchain. API shapes were therefore checked again in the local
4.33.1 sources. The reviewed source digests are:

| Pinned Lean source | SHA-256 | Consequence |
| --- | --- | --- |
| `Lean/Util/CollectAxioms.lean` | `64f340d42f18c51ee83527f03fa69cc26415dd71dcf7fe71031b7760be90007d` | imported declarations use precomputed transitive receipts; the audit still checks every Effect4 declaration directly |
| `Lean/Environment.lean` | `ee364e4788ce0560c87f621eeb3c4c3dfec62e8db4e15e099fd80e6adc533b86` | persistent and asynchronous extension state is an implementation concern; canonical export order is owned by Effect4 |
| `Lean/Expr.lean` | `b9a91d9d170201c2a3622b9c55d694466f54e0e1b8f6068a2d296ff98650169c` | metavariables and elaborator expressions stop at the meta boundary |

This refinement ruling records the original obligations. Current dispositions
and the scope of historical receipts are stated on each DB row below.

## Semantic decomposition

The original Flow design separated the following four observations. This
historical table is superseded on the program-data side by DB-02; the current
module boundaries are in `docs/ARCHITECTURE.md`.

| Face | Purpose | Identity and evidence |
| --- | --- | --- |
| `Program` | Structural induction, algebraic laws, handler construction, and proof-local composition | Lean term identity only; no serialization or decidable content identity |
| checked `Flow` | Stable program identity, sharing, cycles, block references, admission, and generation | First-order canonical data with checked references and profile membership |
| relational semantics | Nondeterminism, divergence, interruption, scheduling, scope, and observable outcomes | Judgments over checked flow, configurations, decisions, and traces |
| bounded runner and host harness | Evaluation, counterexamples, generated TypeScript checks, and regression evidence | Fuel-indexed approximations and versioned host observations |

The faces are connected by explicit relations and preservation theorems. None
is silently identified with another. In particular, an executable runner is
not the denotation, and an Effect TypeScript value is not canonical Effect4
program data.

## Adopted decisions

### DB-01 — `Program` is the well-founded higher-order proof carrier

Status: adopted; the algebra is owned by the pinned `effects` dependency.

Since 2026-09-02 the algebra is owned by lean4-effects `v0.1.0` (`5611c3a`) (`docs/research/EFFECTS-SPLIT-PLAN.md` (untracked working note)); this section states the shape Effect4 builds on. The implemented algebra has the following shape:

```text
Signature.Op     : Type uOp
Signature.Answer : Signature.Op -> Type uAns

Program S A = pure A
            | vis (op : S.Op) (S.Answer op -> Program S A)

Handler S M = (op : S.Op) -> M (S.Answer op)
```

`Program` is higher-order as a representation because `vis` stores a Lean
continuation. It is an inductive, well-founded operation tree suited to monad
laws, interpreter laws, signature sums, handler composition, freeness, and
initiality arguments. It is not necessarily a finite node set or a uniformly
bounded-depth tree: an infinite answer type can index infinitely many distinct
continuation branches whose finite depths are unbounded. Every selected branch
is well-founded, which is the property structural recursion uses. `Program` is
not serializable syntax and receives no content hash, `DecidableEq`, or
generated TypeScript encoding.

This follows the free-model and induced-homomorphism organization in
[Plotkin and Pretnar](https://arxiv.org/abs/1312.1399) and the programming
interpretation demonstrated by
[Bauer and Pretnar's Eff](https://arxiv.org/abs/1203.1539). The literature
licenses the algebraic interface. It does not identify this particular Lean
inductive type with all effectful behavior.

`Handler.sum` is the operation for disjoint signatures. `Handler.through` is
the operation for collapsing an implementation through a second handler.
Categorical composition is stated across signatures; a monoid is available
only for endomorphisms. Implicit universe lifting is excluded. Any explicit
signature map or universe lift requires its own contract and coherence laws.

### DB-02 — `Flow` is the sole reifiable program representation

Status: superseded by `Eff` in `src/Effect4/Program/Eff.lean`; the Flow route
is retained at `606918e` in main's history and on branch `archive/flow-route`.
The paragraphs below record the superseded design, not the current domain model.

Canonical programs use a first-order graph with stable block, operation,
region, and decision identifiers. Admission has the shape:

```text
RawFlow --admit--> CheckedFlow
CheckedFlow --elaborates--> Program
CheckedFlow --denotes--> relational outcomes
CheckedFlow --lowers--> target program
```

`Flow` is not a second free monad. It exists because Lean continuations cannot
carry portable identity and because arbitrary effect flow needs cycles,
sharing, named blocks, and explicit decisions. The bridge to `Program` is an
elaboration relation or function with preservation theorems, not a type
synonym and not an assumed isomorphism.

Pure code is closed at this boundary. A pure fragment enters canonical flow
only through an admitted first-order term language. A host function, promise,
thunk, custom predicate, or raw closure must become a named and registered
foreign boundary or receive a profile refusal. This policy prevents an
uninspectable escape from being mislabeled as full reification.

### DB-03 — open nondeterminism and divergence are relational

Status: adopted; current judgments are over the Machine configurations and explicit decisions.

The denotation is a family of judgments over configurations, explicit
decision tapes, observable events, and terminal outcomes. With no tape fixed,
the meaning of a program is a relation. A complete compatible tape may make a
fragment deterministic; determinism is never inferred merely because one
runner selected one branch.

Scheduling, race winners, wake-up order, external replies, and other choices
have distinct decision kinds. A safety theorem does not assume fairness.
Divergence is witnessed by an infinite run or by compatible finite prefixes,
not by running out of fuel. The design is informed by the event/continuation
semantics and weak equivalence of
[Interaction Trees](https://arxiv.org/abs/1906.00046) and by Choice Trees'
separation of external events from internal nondeterministic branching in
[Choice Trees](https://arxiv.org/abs/2211.06863).

Effect4 does not currently adopt either tree library as its canonical carrier.
An optional comparison may later relate Effect4 runs to an interaction-tree or
choice-tree model. Such a relation needs explicit trace, divergence, and
equivalence judgments; shared monad structure is not enough.

No separate executable `Behavior` datatype is introduced. Meaning remains in
judgments over `Flow`. In deterministic fragments, coherence can establish
that a colimit of finite observations is a partial function. In the general
case, the unpinned denotation remains relational.

### DB-04 — fixed fuel is an approximation, not a denotation

Status: adopted as a constraint; the Flow-specific receipts below are historical.

A bounded runner may report completion, an observable terminal result, or a
live frontier. A live frontier is distinct from typed failure, defect,
interruption, and profile refusal. In particular, fuel exhaustion must not be
encoded as `Refusal.failed`.

There is no general fixed-fuel bind law. Giving the same fuel independently to
a program and both sides of a bind changes how the budget is distributed, so
the runner cannot be a monad morphism for all programs. Composition and
coherence are proved at the unbounded big-step or interpreter face. The
Foldlab compatibility proof therefore targets its `interpretRef` observation,
not a universal equation over `run fuel`.

Finite approximations must instead satisfy monotonicity, compatibility, and
coherence laws. A completing observation cannot later become an unrelated
failure. A live leaf may be refined by more execution without first being
reclassified as an error.

Those three laws are now theorems, not requirements, for both runners over
`StateT σ Id` (`git:c407ab7:Effect4/Semantics/Approximation.lean`; battery
`git:c407ab7:Effect4Test/Semantics/ApproximationContract.lean`). What a bounded run *observes*
is `observe result log`: a fuel frontier contributes `live` and the log it had
reached, without the trailing marker and without the resumption block, and
every other result is `terminal`. `Observation.le` orders those observations —
a live observation is below every one whose log extends it, a terminal one is
maximal — and is reflexive, transitive and antisymmetric. Monotonicity is
`loop_obs_mono` / `run_obs_mono` / `region_obs_mono` / `runRegions_obs_mono`;
compatibility is `Chain.stable` (with the raw form `loop_fuel_stable`);
coherence is `Chain.colimit` with `Chain.colimit_below`,
`Chain.colimit_bound_mono` and `Chain.colimit_eq_of_settled`. For an admitted
plain flow the colimit is total, `runColimitDefault`, because
`run_fuelFor_finishes` (DB-04's own fuel argument, `git:c407ab7:Effect4/Semantics/Fuel.lean`)
proves the allotted fuel suffices; the region runner has no such theorem yet, so
`runRegionsColimit` is searched below a bound and returns an `Option`. The block
identity inside `Frontier.fuel` is deliberately not observed: it is where to
resume, not what was seen, and a jump cycle observes the same empty log at two
different blocks (receipt in `git:606918eb73daefcc235a261fce879bf910f2471e:Effect4Test/Semantics/ApproximationContract.lean`).

### DB-05 — first-order block IDs do not require `HHandler`

Status: adopted for first-order children; the block terminology below belongs to the archived route.

[Higher-order effect frameworks](https://arxiv.org/abs/2302.01415) show why an
operation that accepts an actual computation needs more structure than an
ordinary algebraic operation. The scoped calculus of
[Bosman, van den Berg, Tang, and Schrijvers](https://arxiv.org/abs/2304.09697)
also makes the inner and outer continuations of a scope explicit.

Effect4 applies that distinction at the reification boundary. A scoped
operation in `Flow` contains child `BlockId` values, not Lean computations.
Those children are first-order data interpreted through the same
defunctionalization used by every other block. A handler whose target monad
contains an environment and residual `Program` is already a value of the
existing `Handler` type, and `interpret_bind` plus `Handler.through` supplies
its composition law. Effect4 therefore introduces no `HHandler` carrier for
first-order block children.

`Scope` remains a separate signature summand because acquisition,
registration, delimitation, exit-aware finalization, and closing order are
observable. A Layer may be modeled semantically as a program that constructs
a service handler, but that does not merge Layer, Scope, or service lookup into
one operation family.

The no-`HHandler` decision is conditional on the first-order contract. If a
future public operation stores an actual subcomputation rather than a stable
block reference, its breaker packet must either prove an adequate
defunctionalization or introduce a separately justified higher-order calculus.

### DB-06 — EffHOL contributes the logic layer, not the carrier

Status: adopted as a design constraint; the proof receipts below belong to the archived route.

[EffHOL](https://arxiv.org/abs/2506.09458) parameterizes effectful realizability
by a monad and a program modality. That organization supports a logic over
Effect4 computations after the computational semantics is fixed. It does not
select `Program`, `Flow`, a scheduler, or Effect TypeScript as the meaning of
the monad.

Effect4 classifies EffHOL's angle modality
`<x <- p> phi` as a weakest liberal precondition, `wlp`, rather than a total
weakest precondition, `wp`. The paper explicitly permits
`<x <- p> false` to be derivable for some `p`; the modality therefore does not
itself require termination. Effect4's total-correctness layer must establish
the decomposition

```text
wp p post <-> wlp p post /\ total p
```

for the chosen semantics before calling a judgment `wp`. That theorem is discharged (2026-09-03) in `git:c407ab7:Effect4/Semantics/Logic.lean`,
over the semantics D1 fixed: `Effect4.Logic.wp_iff_wlp_and_total` for every
`Program` relative to an answer specification, and `Effect4.Flow.wp_iff` in the
flow reading, where the partiality `total` excludes is exactly the unanswered
frontier and the refusal (never fuel, per DB-04). `box_sound` ties the liberal
judgment to `interpret`, and `Flow.wlp_runDefault`/`wp_runDefault` to the runner
through T1/T2. The paper's constructive soundness theorem is evidence about
EffHOL, not a proof of Effect4's instance.

### DB-07 — runtime state remains observable on failure

Status: adopted.

The reference runtime floor uses `EStateM` or an equivalent result type whose
error arm retains state. Lean's law
[`EStateM.run_throw`](https://lean-lang.org/doc/api/Init/Control/Lawful/Instances.html)
returns `Result.error error state`. This is required because scope cleanup and
supervision must observe registrations and state changes made before a typed
failure, defect, or interruption.

The project compiles this choice against
[`leanprover/lean4:v4.33.1`](https://github.com/leanprover/lean4/tree/v4.33.1).
The unversioned documentation links explain the API; the pinned toolchain is
the source and kernel authority for Effect4 receipts.

The order is semantic, not cosmetic. Lean's official discussion of
[transformer ordering](https://lean-lang.org/functional_programming_in_lean/Monad-Transformers/Ordering-Monad-Transformers/)
shows that `StateT` outside `ExceptT` can lose state on error, while `ExceptT`
outside `StateT` retains it. Effect4 freezes state-outside-failure for the
runtime and resource machine. Rollback, when desired, is a separate
transactional operation with its own laws.

`EStateM` supplies neither concurrency nor resource correctness by itself.
The runtime still needs proved transitions for finalizer registration and
order, exactly-once close, interruption masking, fiber ownership, scheduler
decisions, and managed-runtime disposal.

### DB-08 — `Expr` is a metaprogramming input only

Status: restated in `AGENTS.md`, Representation rules (canonical program content).

Lean's [`Expr`](https://lean-lang.org/doc/api/Lean/Expr.html) represents kernel
and elaborator expressions, including metadata and metavariables. Effect4 may
inspect an elaborated `Expr`, but it must emit a checked first-order
declaration row before the value enters program identity, semantics, or target
generation. Raw `Expr`, syntax trees, metavariables, tactic closures, and
elaborator state are not semantic data.

Declaration metadata that must survive imports uses
[persistent environment extensions](https://lean-lang.org/doc/api/Lean/Environment.html).
The exported entries are deterministic serializable rows; any cache built from
them is derived state. Stable ordering and digests are established before
emission so parallel elaboration cannot change generated bytes.

[`Lean.collectAxioms`](https://lean-lang.org/doc/api/Lean/Util/CollectAxioms.html)
is the audit primitive for the transitive axiom dependencies of exported
theorems. Its output is an axiom receipt, not a semantic correctness proof and
not evidence about generated TypeScript behavior.

### DB-09 — Effect TypeScript is a versioned target profile

Status: restated in `AGENTS.md`, Representation rules (target profile).

The semantic authority for the first target profile is the Effect source tree
at commit
[`2600f62f4532026928454dcea8d1c48557b3f942`](https://github.com/Effect-TS/effect/tree/2600f62f4532026928454dcea8d1c48557b3f942/packages/effect/src),
paired with `effect@4.0.0-rc.112`. The target profile records the distinctions
observed in that version: success, typed failure, defect, interruption,
service requirements, scope, fibers, causes, exits, and runtime boundaries.
It does not make Effect's internal runtime representation part of Effect4's
canonical syntax.

Source revision and installed package bytes are separate evidence. The
upstream commit and tree identify source history. Foldlab's lockfile identifies
the exercised package by integrity
`sha512-wXxwuh1Ywnv4cPRM3Wfa0vDwuOHnZ1TsTgHJkG9XgzND6inhBH9n1vBxhg3iIXOia/OrpmvVmd3lrD4vq6bF3A==`.
The installed `src/Schema.ts` has SHA-256
`9358710e2c0d613371d8feeeccb3716fe98a43f67e6aa1076b00d4079a258784`,
while the file at the pinned upstream commit has SHA-256
`f0ecfa4511a62c2eb7ed820449d12653a2bbb8ef82ead842189a56b503d0de2f`.
This mismatch is not classified as package corruption; it is evidence that a
repository revision cannot stand in for installed bytes.

The
[`effect-ts/language-service`](https://github.com/Effect-TS/language-service/tree/5e4d380b6fcd20f048dd8d41515bcd9ea47ffda4)
pin is an auxiliary diagnostic source. Its Effect v4 harness targets
`4.0.0-beta.107`, so it cannot decide rc.112 surface membership or runtime
meaning. Acceptance requires direct rc.112 TypeScript typechecking, language-
service diagnostics, runtime vectors, negative fixtures, and mutation tests.

Generation must prove or test separate claims:

1. lowering preserves the admitted Effect4 typing judgment;
2. rendering and parsing preserve the target intermediate representation;
3. the TypeScript checker accepts positive vectors and rejects negative ones;
4. direct runtime observations match the reference semantics for the tested
   fragment; and
5. any unsupported or lossy operation receives a stable refusal rather than a
   fabricated implementation.

No one gate discharges the others.

### DB-10 — PolyFun is pinned prior art, not a public dependency

Status: adopted as prior art, not an Effect4 proof receipt.

The isolated audit of
[`Verified-zkEVM/PolyFun` at `3937f7ff0830cca33d6b35a24aef55bcbe3b6bc9`](https://github.com/Verified-zkEVM/PolyFun/tree/3937f7ff0830cca33d6b35a24aef55bcbe3b6bc9)
used Lean `v4.33.1`, Mathlib `v4.33.1`, and cslib `v4.33.1`. Its build, tests,
validation script, and declared axiom sweep passed in the isolated checkout.
That evidence applies to the pinned checkout and its stated theorems; it does
not establish an Effect TypeScript bridge.

Effect4 has no public PolyFun dependency. Pulling it into the foundation would
add Mathlib and cslib, substantially enlarge a full validation checkout, and
couple the public API to a rapidly changing library. Effect4 instead keeps its
small algebra self-contained and may adapt independently proved API shapes:
signature maps and lenses, first-class monad morphisms, finite paths, and an
optional interaction-tree comparison. Borrowed code, if any, must retain its
license and exact source provenance.

PolyFun's `FreeM` is still a higher-order proof representation. It cannot
replace first-order checked `Flow`, so adopting the dependency would not remove
the reification boundary.

### DB-11 — one value carrier, images over it, admission as a premise

Status: adopted 2026-09-07 (U0, U1a, U1b: `7cbd436`, `54c90a4`); the executable admission
is owed to X2.

Every value the runtime carries is one tree, `Effect4.Store.Val`
(`src/Effect4/Store/Val.lean`): the content store's frames plus `handle` (tag 12), a live
allocation index into a running machine's stores. `Machine.Val` and `Env.Val` are that type
by `abbrev` (`src/Effect4/Machine/Stores.lean`, `ContextMap.lean`); the runtime alphabets that
were inductives of their own — exits, causes, the fiber context, the service map — are images
over it (`Effect4.Store.Image`, `src/Effect4/Store/Image.lean`: `toVal`/`ofVal` with
`ofVal_toVal` and `ofVal_exact`), so a value is read back by a reader (`Val.context?`,
`Env.decode`, `Val.scope?`, `exitOfVal`) and never matched as a constructor. A handle is not
content: no store shape accepts it, and its kind table is the Machine's.

Well-formedness is a theorem premise, not a runtime check. `Val.WF` (frame sizes),
`Stores.WF` (every handle a live allocation, a closed scope's exit valid in the store, a memo
entry's Deferred and layer scope live) and `validIn` are the hypotheses the laws carry
(`syncOpStep_answer_valid`, `interpOf_keyBounded`), and `Stores.empty` satisfies every
family's conjunct so the store has a bottom. An executable admission — the checked decision
at `Api` that refuses a value the premise excludes and returns the machine and the position
— is X2's (`docs/research/2026-09-08-build-path.md` §3 (untracked working note)); until
then a forged handle is a refusal row (`E4-HANDLE-CE-001`), never a defect the model raises.

### DB-12 — one context, layers by path

Status: adopted 2026-09-07 (the join: `6305ce3`, `4aae12f`, `4d7c34e` and its records
commit).

The fiber context is one structure (`Machine.Ctx`, `src/Effect4/Machine/Stores.lean`): the
service map (`Env.Ctx`, `src/Effect4/Machine/ContextMap.lean`) and the two budget caches
rc.112's `setContext` stores off it (`internal/effect.ts:726-727`). `Ctx.withServices` is
the one constructor, so the cache law (`Ctx.CacheAgrees`) holds by construction and is not a
field; the ambient `Scope` is a lookup on the map (`Ctx.ambientScope`), cached nowhere.
There is no second context: `Effect.service`, `provideService`, `Effect.provide` and `scoped`
read and write this one map through `updateContext`'s region (`src/Effect4/Program/Compile.lean`:
`updateContextAt`, `updateThenK`).

A layer is a program subterm. `LayerTerm` is a member of the `Eff` mutual family
(`src/Effect4/Program/Eff.lean`: `succeed`, `effect`, `effectDiscard`, `provide`,
`provideMerge`, `merge`, `fresh`, `orDie`; `mergeAll` is a fold of `merge`, never a
constructor), reached through `Eff.provideLayer` with rc.112's `local` flag as a field, and
`Node.layer` addresses it. Its identity is its path: `LayerId := List Nat` is the memo world's
key (`Stores.memo`, `MemoWorld`), and `compileLayer` builds a layer at its point with the memo
map and the scope as `build`'s two arguments (`Layer.ts:230-232`) — the build protocol as
`EffName` continuations at Points (`fromBuildThen`, `withMemoMapThen`, `memoize`,
`provideThen`, `mergeChildren`, …) and `Region` as the first-order "what runs under a context
region". There is no layer table, no `Construction`, no `ProgName`-style program table and no
second `RunMachine` instantiation: the Layer machine
(`git:4aae12f:src/Effect4/Machine/Layer.lean`) retired with the join, its memo world and
operations joined into the one `Stores` verbatim.

What path identity refuses. rc.112 keys the memo map on the layer *object* (`Layer.ts:411`,
`:438`); a path is where a layer *is*, never what it says, so two sites of one printed term
are two keys and a memo *hit* is unreachable from any printed program: `harness/truth`'s
`pProvideTwice` pins the two-site protocol (two builds), not a hit, and grill call 10 (keep
the memo store) is settled by build order-independence, not by a fixture
(`docs/research/2026-09-08-build-path.md` §2 (untracked working note)). Inserting under one
path leaves every other path's entry untouched (`MemoWorld.find?_append_other_key`,
`LAYER-FB-LAYER-IDENTITY`); a forged path is the refusal row.

### DB-13 — one wake protocol, the family's policy on top

Status: adopted 2026-09-08 (the scheduler surface: `5347294`, `4ed61a7` and the records commit).

Every waiting family — Deferred now; Latch, Queue, Semaphore, Pool, PubSub and the timer as
they land — parks its waiters on one list, `WakeList π` (`src/Effect4/Machine/Wake.lean`),
generic in the family's payload `π`. The protocol fixes *when* a waiter is woken and how a
cancel is accounted; *which* waiters and *with what* is the family's policy (`WakePolicy`:
`broadcast`, `signal`, `sweep`), a function over the list, never a second list. A waiter is
`(fiber, token, phase, payload)`, captured at registration (the WHATWG capture rule: a later
list replacement cannot retarget it); the phase is the list's counter, advanced by every wake
(Eio's `In_transition` role). A wake owes resumes, `Owed κ` = `(waiter, token, code, mode)`,
and `WakeMode` says how an owed resume is delivered: `now` inline at the drain (Deferred,
`internal/effect.ts:5277`), or `scheduled owner priority` posted on the owner's dispatcher and
fired by the host's flush (the six `scheduleTask` sites, `Scheduler.ts:193-247`). A
`scheduled` wake coalesces: the first `schedule` captures the pending waiters into the batch
and posts one `Task.wake list phase`; a later one joins the batch and posts nothing
(`WakeList.schedule_coalesces`, `Latch.scheduleUnsafe`).

The cancelled-waiter clause is verbatim: a cancel on a waiter still pending removes it and
owes nothing; a cancel on a waiter no longer pending consumed a wake, and the cancelling step
owes one (`WakeList.cancel_owed_iff`; a `broadcast` list lost nothing,
`wakeAll_cancel_owed`). The machine side stays the token guard: a resume for a waiter no
longer parked is inert.

The dispatcher's address is its making fiber's id, and nothing else: the machine never
removes a fiber record (`spawn` appends, `RunMachine.update` maps in place), so a dispatcher
outlives its fiber's run exactly as rc.112's object does (`Queue.ts:455` stores it at make),
and a post to an exited fiber's dispatcher is delivered. There is no dispatcher table. A post
to an id the machine never minted is the frontier `Stuck.unknownFiber`
(`SCHED-FB-UNKNOWN-OWNER`).

The `Delay` reply (Riot's `Proc_state.step` third answer) is not a new machine answer: a row
that is not ready registers on the family's list with *the row itself* as the payload
(`WakeList.delay`) and parks on a fresh token; the wake re-presents the row and it is polled
again, consuming no frame (Queue's signal-then-repoll, `Queue.ts:1955-1975`, `:1432`). A
spurious wake is permitted by construction: the repoll may park again at the advanced phase.

What this basis refuses. A waiter list is FIFO in registration order and a family's non-FIFO
policy is a sweep over it, not a reordering (`sweep_keeps_order`, `SCHED-FB-NO-FIFO`);
`Task.wake` and `WakeList.delay` have no rc.112 producer in this tree until Latch and Queue
land, so their meaning is pinned by executed fixtures (`SchedulerCoreContract` §Wake), not by
the truth harness (`SCHED-FB-PRODUCER`); `TxRef` is its own subcalculus, not a policy on
this list.

### DB-14 — one logical clock, a duration decision, staged fires

Status: adopted 2026-09-08 (the timer, A4: the three commits of
`docs/research/2026-09-08-timer-dispatch.md` (untracked working note)).

Physical time is not modelled and never will be (DB-04 forbids fuel as time; wall-clock, drift,
the browser's floor and `setTimeout`'s ceiling are host facts). Logical time is one store on
the wake protocol (`src/Effect4/Machine/Timer.lean`, DB-13): `TimerStore` is the clock, the
pending sleeps as waiters whose payload is the deadline, and the end of an advance in
progress. Its shape is rc.112's `TestClock` (`testing/TestClock.ts`: a timestamp that moves
only when the host says so, a table ordered by deadline then registration, an `adjust` that
fires every due sleep in that order staging the clock at each fired deadline and letting
fibers run between fires); its registration meaning is the live `ClockImpl`'s
(`internal/effect.ts:6052-6066`): a cancelled sleep is removed.

The host moves the clock by one decision, `RunDecision.advance (millis : Nat)` — a duration,
never a timestamp — and the machine runs the staged loop (`advanceState`): fire the least due
sleep (`RunInterp.clockStep`, the one new interpreter field), resume it, flush the
dispatchers, repeat, then set the clock to the end. A sleep a woken fiber registers that is
due by the end fires in the same advance (finding 4 of
`docs/research/2026-09-04-timer-semantics-and-proofs.md` (untracked working note)). A fired sleep resumes inline
(`WakeMode.now`, as a Deferred's completion does); the latch-posted spelling rc.112 uses there
is Latch's to land. Two rows reach the store: `sleep d` with `0 < d < ∞` registers
(`Name.registerSleep`, cancel `Name.cancelSleep` = `clearTimeout`), and `clockNow` reads
(`SyncOp.clockNow`); `sleep 0` is `yieldNow` and `sleep ∞` is `never`, decided at the row.
`TimerStore.WF` — every pending deadline at or after the clock — is a conjunct of
`Stores.WF`, kept by every store step and every clock step.

What this basis refuses. `setTime` (`TIMER-FB-SET-TIME`): the clock never moves backwards. A
kept cancelled sleep (`TIMER-FB-KEPT-CANCEL`): the store models `clearTimeout`, not the test
clock's table. An infinite deadline (`TIMER-FB-INFINITE`). A `Psq` carrier: the wake list is
the one carrier and the earliest deadline is a policy on it (`WakeList.wakeBy`), measured
elsewhere as not worth a second structure; a keyed carrier is a later, measured change.

### DB-15 — strings are machine values; host records and errors cross as strings

Status: adopted 2026-09-08 (the host rows slice, decision 3 of
`docs/research/2026-09-08-host-rows-slice.md` §7 (untracked working note); step 1 of its
dispatch).

A `str` literal is a machine value on the native route: `Lit.toVal (.str s) = some (.str s)`
(`src/Effect4/Program/Native.lean`), and the value typing inhabits `.string` with the
carrier's `str` frame and `.option t` with its `none` and `some` frames (`Val.hasTy`,
`src/Effect4/Laws/Program/Typed.lean`). Every literal now evaluates, so `evalTerm_isSome`
carries no `noStr` premise and the register row `E4-TYPED-CE-001` is retired with its ID
kept. The provision route's `litVal` (`src/Effect4/Program/Typing.lean`) still refuses a
string as a layer value (`PROV-FB-STRING-VALUE`); that refusal is its own and is not moved
here.

What crosses a host row, so that a canonical row table can be typed with neither a record
nor a dynamic type in `Ty` (`src/Effect4/Program/Eff.lean` has neither and gains no `json`
leaf): a SQL row is `list (prod string string)`, one `(column, cell)` pair per column in the
order the package answered them; a row set is `list (list (prod string string))`; bind
parameters are `list string`; and every cell and parameter is JSON text (`7` is `"7"`, `"a"`
is `"\"a\""`, `null` is `"null"`). A bind outside `Lit` (a `Date`, a `Uint8Array`, an object)
is `E-ARG-DYNAMIC` at ingest. An error crosses as `prod string string`, the `_tag` and the
message: `SqlError` is a tagged union of eleven reasons (`unstable/sql/SqlError.ts:31-329`)
and `Ty` has no sum. A handle a row answers stays a `Ty.handle` target spelling (DB-11); an
optional answer (`KeyValueStore.get`) is `.option string`.

What this basis refuses. A `json` leaf in `Ty`: the value language is the carrier's frames
and a codec is a row. A record type in `Ty`: columns are pairs. `.int` stays uninhabited
(`TYPED-FB-INT`): `Val.nat` is a `.nat`, and the printer's identification of the two as
`number` is not the typing's.

## Native library boundaries

Effect4 does not place the whole Effect TypeScript API into one opcode family.
The following calculi have distinct indices and explicit embeddings:

- Schema separates representation, decoded value, encoded value, decoding
  services, and encoding services. A transformation composes its decoding
  direction forward and its encoding direction in reverse. Foldlab's CAS
  schema remains a checked downstream profile, not a duplicate generic
  carrier.
- Context and Service own stable typed keys, requirements, and environments.
  Layer owns construction, dependency order, memo identity, and cleanup —
  as program subterms addressed by path, on one context (DB-12).
- Scope and Resource own lifetime delimiters and exit-aware finalization.
  Their operations may be summed into a program without erasing the separate
  calculus.
- Runtime and ManagedRuntime own interpretation, lazy construction, cached
  context, scopes, fibers, and disposal. Runtime objects are target state, not
  program syntax.
- Fiber, scheduling, race, interruption, and supervision own concurrent
  transitions and decisions. Streams, channels, schedules, and transactions
  retain their own state machines rather than being reduced to lists,
  durations, or ordinary state updates.
- Cause and Exit are first-order result data outside `Program`. A richer cause
  tree may lower to an rc.112 ordered-reason representation only through a
  named, tested, and explicitly lossy quotient.

This organization keeps the generic algebra small while allowing the public
library to model the complete effectful interface through composition.

## Required proof graph

Each public type closes its own graph before cutover. A later theorem cannot
silently stand in for an earlier edge.

| Edge | Required judgment or evidence | Current state |
| --- | --- | --- |
| Algebra | monad equations; interpretation of `pure`, `bind`, and `perform`; sum laws; handler composition; freeness and initiality; axiom receipt | Implemented; independent assurance review remains separate |
| Admission | raw reference resolution, index well-formedness, type preservation, checked erasure, decidability, and stable refusal classification | Pending |
| `Program`/`Flow` bridge | sequential quotation, elaboration preservation, interpretation agreement, and the exact boundary where cyclic or unbounded recursive unfolding ceases to be an inductive `Program` value | Pending |
| Operational semantics | step preservation, terminal exclusivity, tape compatibility, per-tape determinism where applicable, and explicit scheduler assumptions | Pending |
| Recursive meaning | approximation monotonicity, coherence, finite adequacy, divergence adequacy, and no completion-to-failure regression | Pending |
| Logic | `wlp` laws, totality, `wp <-> wlp /\ total`, consequence, bind at the semantic face, and classification transfer soundness | Pending |
| Scope and runtime | state retention on failure, finalizer order and exactly-once execution, delimiter laws, interruption behavior, fiber ownership, and disposal | Pending |
| Schema and services | representation well-formedness, directional codec laws, service-key identity, Layer dependency laws, provision observations, and scope elimination | Pending |
| TypeScript target | typed lowering, deterministic rendering, decode round trips, direct rc.112 type/runtime vectors, diagnostic negatives, and simulation for each admitted fragment | Pending |
| Foldlab adapter | source digest, conversions in both directions, round trips, interpretation agreement, counterexample coverage, and axiom receipt for each moved type | Pending |

The strongest present claim is that the implemented well-founded algebra compiles
and has a dedicated proof and counterexample battery. The document makes no
claim that the pending flow, runtime, target, or compatibility edges are
proved.

## Source and evidence rules

The evidence classes answer different questions and are never substituted for
one another.

| Evidence | Answers | Does not answer |
| --- | --- | --- |
| Paper and mechanization | Which semantic construction and theorem shape is known in the cited system | Whether Effect4's definitions instantiate it correctly |
| Lean kernel proof | Whether a proposition follows from the imported declarations and recorded axioms | Whether the proposition specifies Effect TypeScript correctly |
| Upstream source commit | What repository state was reviewed | Which bytes a package manager installed |
| Package integrity and file digests | Which target bytes were exercised | Whether the upstream repository and package are semantically equivalent |
| Typechecker or language-service result | Whether a finite generated case satisfies that tool and version | Runtime behavior or surface exhaustiveness |
| Runtime vector | What happened for a finite execution | Denotational equivalence for all programs |
| Corpus census | Which public spellings appeared in a pinned sample | Completeness of the target API or semantic correctness |

The exact operational pins, source digests, and cutover dispositions are owned
by [`PORT-MANIFEST.md`](../PORT-MANIFEST.md). This document owns the
architectural consequences of that evidence.

## Designs excluded by this basis

The following choices require a new decision record and a breaker packet:

- a second free-program carrier beside `Program`;
- an `HHandler` whose only higher-order content is a first-order `BlockId`;
- a standalone executable `Behavior` datatype that duplicates relational
  semantics;
- a denotation defined by one fixed fuel value or a universal fixed-fuel bind
  law;
- treating a live frontier as failure, defect, interruption, or refusal;
- storing raw `Expr`, host closures, promises, or runtime objects as canonical
  program content;
- making PolyFun, Mathlib, Foldlab, Effect TypeScript, or the Effect language
  service the semantic owner of the core library; and
- claiming full reification from compilation, a finite corpus sweep, or a
  finite runtime test alone.

These exclusions keep the proof graph inspectable while leaving room for
explicit comparison models and target-specific implementations.

## Primary sources

- Gordon D. Plotkin and Matija Pretnar,
  [*Handling Algebraic Effects*](https://arxiv.org/abs/1312.1399).
- Andrej Bauer and Matija Pretnar,
  [*Programming with Algebraic Effects and Handlers*](https://arxiv.org/abs/1203.1539).
- Liron Cohen, Ariel Grunfeld, Dominik Kirst, and Étienne Miquey,
  [*Syntactic Effectful Realizability in Higher-Order Logic*](https://arxiv.org/abs/2506.09458),
  arXiv v1, 2025-06-11.
- Li-yao Xia et al.,
  [*Interaction Trees: Representing Recursive and Impure Programs in Coq*](https://arxiv.org/abs/1906.00046).
- Nicolas Chappe et al.,
  [*Choice Trees: Representing Nondeterministic, Recursive, and Impure Programs in Coq*](https://arxiv.org/abs/2211.06863).
- Birthe van den Berg and Tom Schrijvers,
  [*A Framework for Higher-Order Effects & Handlers*](https://arxiv.org/abs/2302.01415).
- Roger Bosman, Birthe van den Berg, Wenhao Tang, and Tom Schrijvers,
  [*A Calculus for Scoped Effects & Handlers*](https://arxiv.org/abs/2304.09697).
- Lean,
  [source at `v4.33.1`](https://github.com/leanprover/lean4/tree/v4.33.1),
  [`EStateM` lawful instances](https://lean-lang.org/doc/api/Init/Control/Lawful/Instances.html),
  [transformer ordering](https://lean-lang.org/functional_programming_in_lean/Monad-Transformers/Ordering-Monad-Transformers/),
  [`Environment`](https://lean-lang.org/doc/api/Lean/Environment.html),
  [`Expr`](https://lean-lang.org/doc/api/Lean/Expr.html), and
  [`collectAxioms`](https://lean-lang.org/doc/api/Lean/Util/CollectAxioms.html).
- Effect,
  [source at `2600f62f4532026928454dcea8d1c48557b3f942`](https://github.com/Effect-TS/effect/tree/2600f62f4532026928454dcea8d1c48557b3f942/packages/effect/src).
