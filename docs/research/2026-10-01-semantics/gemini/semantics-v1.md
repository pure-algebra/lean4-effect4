# Effect4 Semantics Specification (v1 Draft, 2026-10-01)

This document is the semantic description of Effect4, an operational and denotational reification
of the Effect runtime in Lean 4. It organizes the language's semantics concept-first across ten core
foundational concepts, establishes their proof obligations against standard lemma lists from the
type systems literature, records the architectural cuts made by project decisions, and connects
the formal judgments to verified in-tree theorems and tracked counterexamples.

---

## 1. Overview and Structural Principles

Effect4 programs are typed, first-order data structures (`Eff`). Programs are not Lean functions,
closures, or host runtime objects. They are interpreted by a small-step abstract machine
(`RunMachine`) operating on configurations consisting of instructions, execution frames, mutable
stores, and decision/event queues.

The metatheory is organized around ten stable domain concepts:
1. **Store Typing & Value Membership** (`store-typing`)
2. **Residual Program Typing** (`residual-program-typing`)
3. **Scope Lifetime & Finalization** (`scope-lifetime-finalization`)
4. **Reactive Scheduling & Machine Invariants** (`reactive-scheduling`)
5. **Exact Codecs & Data Plane Embeddings** (`exact-codecs`)
6. **Subtyping Algebra & Normalization** (`subtyping-algebra`)
7. **Initial Algebras & Catamorphic Folds** (`initial-algebras-folds`)
8. **Context Requirements & Provision** (`context-requirements`)
9. **Host Session Protocol & Boundary** (`host-session-protocol`)
10. **Translation & Simulation Metatheory** (`translation-simulation`)

Every claim in this document is backed by an explicit evidence class:
- **proved**: Verified kernel theorem located in the tree (`file:line`), quoted with exact signature.
- **tested**: Finite executable check or test suite executed and cited.
- **reading**: Verified by reading source code or vendored literature.
- **assumed**: Hypothesized claim or external host driver condition, with explicit bounds recorded.

### 1.1 Reading the Model and its Evidence

Stored `Eff` syntax uses program-tree continuations with positional inputs (`Eff.bind` stores two
child trees, [Eff.lean:277](file:///src/Effect4/Program/Eff.lean#L277)). `RProgram` is the proof-side semantic carrier
`Effects.Program RSig ExitV` ([Sched.lean:206](file:///src/Effect4/Laws/Program/Sched.lean#L206)); visible operations carry
Lean function continuations (`vis : Answer operation → Program signature A`,
`.lake/packages/effects/Effects/Algebra/Program.lean:33–38`). Those functions belong to the semantic
model and are not stored function values in `Eff` or `Val`.

`Fits` is value membership in a world. `TypedProg` is residual program typing: ordinary operation
clauses require certificate permission and typed continuations for permitted replies at later worlds. Its
`unguard` and `finishFinalizer` clauses require an exit payload without a continuation premise;
`scopeExit` separately requires a live scope and typed continuation. `DenotesTyped` connects admitted
source points to that residual judgment. These definitions resemble protocol-based program logics,
but identifying them with weakest preconditions would require a named execution interpretation and
a stated correspondence. The unrestricted bind counterexample (`E4-TYPED-CE-030`) alone does not
settle every possible weakest-precondition interpretation.

A claim's title, role and selected evidence express an authored interpretation. The printed
proposition states exactly what its theorem proves or its ledger goal requests. Checking a theorem
does not check the English interpretation. Refutation and contest links therefore expose the
registered attacked statement and revision alongside the witness. Historical attacks do not
automatically refute repaired propositions.

Progress, preservation, scheduling service and interpreter agreement ask different questions. An
invariant can exclude a halted configuration without establishing a successor. Progress must account
for finished states, permitted transitions and live frontiers; preservation concerns covered
transitions. Finite scheduling service concerns actual callback entry under its stated readiness
and bounds. Internal replay agreement retains its empty-host fragment. None of these statements
alone proves termination or eventual host cooperation.

The checked executable report currently covers strictly residual program typing (the 4-claim
slice); it does not yet execute checks for the other nine concepts in Lean. Those nine concepts
are authored registry entries awaiting adoption. Generated tables own evidence status, propositions,
and counts; prose explains meaning, scope, and boundaries. Cuts own applicability.

### 1.2 API and Evidence Boundary

This specification distinguishes authored descriptions from evidence checked in the loaded Lean
environment. A claim's title and role explain why its evidence matters; the printed proposition
states exactly what was proved or requested.

| Item | Owner | What readers can conclude |
| --- | --- | --- |
| Claim identity, concept, role, title and evidence pointer | `Tools.Semantics.registry` | Authored assignments identifying a theoretical question and its selected evidence. |
| Theorem statement, universes, module and axioms | Loaded Lean environment | A `witness` is checked as a theorem of its own printed proposition under the semantic axiom ceiling `[propext, Quot.sound]`. |
| Obligation proposition and checked/wanted evidence | Existing `ProofGraph` ledger | A `goal` is a declared question. Its checked witness or wanted placeholder must match that question, including binders and universes. Selected goals do not establish coverage of an entire ledger scope. |
| Refutation and contest associations | Registry links to `Test/Counterexamples/REGISTER.md` | Checks the referenced row and witness theorem. Read the row's attacked statement and revision alongside the printed evidence. |
| Applicability | Decisions register, referenced by `Cut` | A cut limits the question's domain. It does not prove, refute or discharge the question. |
| Declaration placement | Explicit concept tag, then registry module default | Each eligible declaration has one primary home; inherited placement is provisional. |

Status indicators describe the selected evidence: `absent` means no witness, goal, or refutation is
selected, distinguishing an owed obligation from a role outside the cut (citing decisions rows).
`assumed` denotes an external assumption outside the closed runtime. Status counts are evidence
inventories, not completion percentages.

### 1.3 Literature Connections and Boundaries

Literature relations use the verified repository vocabulary: `definitionUsed`, `proofTechnique`,
`adaptedResult`, `analogy`, and `excludedFeature`. A verified contents heading establishes a
locator, not a theorem's applicability. ATTAPL's logical-relations chapter is maintained at the
verified Chapter 6 (Crary).

| Source | Useful connection | Boundary to state |
| --- | --- | --- |
| Ahmed on mutable-state types | Worlds, monotonicity, semantic-store circularity | Does not impose step indexing on the current finite structural `Fits` definition |
| Interaction Trees | Semantic operation continuations as meta-level functions | That source is coinductive; the imported `Effects.Program` here is inductive |
| De Vilhena–Pottier | Effect protocols and weakest-precondition reasoning | An analogy until a particular local judgment and correspondence are stated; bind rules depend on the chosen judgment |
| PLF / Harper | Precise progress, preservation, canonical-forms and substitution questions | Apply each to the local judgment; do not substitute codec or invariant facts |
| Lynch–Vaandrager | Simulation and trace-inclusion methods | Their safety methods do not supply liveness; local one-step interfaces are particular instances, not the whole paper |

---

## 2. The Ten Semantic Concepts

### 2.1 Concept 1: Store Typing & Value Membership (`store-typing`)

#### 1. What the Literature Defines
- **Store Typings & Safety**: TAPL §13.4, pp. 162–164 (*Store Typings*, audit T7, T44, T91) and
  TAPL §13.5, pp. 165–169 (*Safety*, audit T1, T2, T7, T44). A store typing $\Sigma$ maps allocated
  locations to static types, breaking circular dependency during mutable assignment.
- **Monotonicity (Store Weakening)**: TAPL §13.5 (audit T7); PLF `References.v` (`store_weakening`,
  line 1539, audit F5, F17). Allocating fresh cells preserves the typing of previously allocated
  locations under store extension ($\Sigma \subseteq \Sigma'$).
- **World Indexing & Kripke Models**: ATTAPL ch. 6 (Karl Crary, *Logical Relations and a Case Study
  in Equivalence Checking*, pp. 223–244; §6.7 *A Monotone Logical Relation*, p. 236, audit A2, A4,
  A8, A12–A15); Amal Ahmed (2004, *Semantics of Types for Mutable State*, PhD thesis, Princeton,
  audit P1, C1). World-indexed semantic interpretations with future-world accessibility ($w \le w'$).

#### 2. Effect4 Adaptation, Assumptions, and Exclusions
- **Adapting Kripke Worlds**: Effect4 adapts Kripke store typings into `Effect4.Program.Typed.World`
  with explicit partitioned tables for fibers ($\Gamma$), promises ($\Pi$), heap references ($\mathrm{P}$),
  and ghost resume states ($\Theta$).
- **Exclusion of Stored Functions (Row 163)**: Stored `Eff` syntax and stored values `Val` contain
  no function values or closures (`language-cut.md` §1). Consequently, `Fits` contains **no arrow clause**,
  and step-indexing is unnecessary for this finite structural membership relation. (Analogy to Ahmed's
  worlds, but excluding semantic-store circularity).
- **Checker Order & Normalization (Rows 96, 137)**: Handle arm subtyping uses `Equiv` under `subN`
  (normalized subtyping both ways), as raw subtyping does not distribute products over unions (`E4-TYPED-CE-009`).
- **Scope Handle Persistence (Row 156)**: Scope handles require `ScopeLive w sc`; dangling handles do not fit `Ty.scope`.

#### 3. Project Definition and Judgment
Value membership in Effect4 is defined by the judgment `Effect4.Program.Typed.Fits`:
```lean
def Fits (w : World) (v : Val) : Ty → Prop
```
([Membership.lean:112](file:///src/Effect4/Laws/Program/Typed/Membership.lean#L112)). It asserts that runtime value `v` inhabits semantic type `ty`
under world `w`. Handle leaves verify capability declarations against `w.Ρ`, `w.«Π»`, `w.Γ`, and scope
persistence `ScopeLive w sc`. At exit types (`.exitOf a e`), the reified cause is checked to be `ShapeFree`
(excluding defects `badName` and `notImplemented`, decisions row 152).

#### 4. Required Properties and Obligations
- **Monotonicity (`fits-mono`)**: World extension preserves value membership:
  `w.leHost w' → Fits w v ty → Fits w' v ty` ([`fits_mono`](file:///src/Effect4/Laws/Program/Typed/Membership.lean#L886)). Proved witness.
- **Subtyping preservation (`fits-subn`)**: Subtyping in normalized order preserves membership:
  `Ty.subN a b = true → Fits w v a → Fits w v b` ([`fits_subN`](file:///src/Effect4/Laws/Program/Typed/Membership.lean#L1262)). Proved witness.
- **Normalization compatibility (`fits-normalize`)**: Value membership is invariant under type normalization:
  `Fits w v t.normalize ↔ Fits w v t` ([`fits_normalize`](file:///src/Effect4/Laws/Program/Typed/Membership.lean#L1156)). Proved witness.
- **Scope inversion (`fits-scope-inv`)**: Inversion on scope handle values:
  `Fits w v Ty.scope → ∃ sc, v = Val.scopeHandle sc ∧ ScopeLive w sc` ([`fits_scope_inv`](file:///src/Effect4/Laws/Program/Typed/Membership.lean#L896)). Proved witness.
- **Store safety invariant (`store-safety`)**: Well-typed machine stores produce values that Fit their
  declared types across write operations (D5 / decisions row 180). Required absent obligation.

#### 5. Next Bounded Coding Task and Completion Evidence
- **Next Slice**: Data Path W4 signed integer (`Val.int64`) and binary64 float (`Val.float64`) value/type appends.
- **Owner**: Seat W4 ([Data Wave README](file:///docs/research/2026-10-01-data-wave/README.md)).
- **Completion Evidence**: Compiling `Effect4.Machine.Value`, `Effect4.Program.Ty`, and `Effect4.Laws.Program.Typed.Membership`,
  with unit tests in `Test/Program/DataWaveNumeric.lean`. See [implementation-inventory.md](file:///docs/research/2026-10-01-semantics/gemini/implementation-inventory.md#L71-L92) §2.1.

---

### 2.2 Concept 2: Residual Program Typing (`residual-program-typing`)

#### 1. What the Literature Defines
- **Effect Systems & Typing**: ATTAPL ch. 3 (Henglein, Makholm, Niss, pp. 87–136, audit A1, A5, A16).
  Tracks computational effects and region operations statically.
- **Protocol Typing for Handlers**: de Vilhena & Pottier (2021, *A Separation Logic for Effect Handlers*,
  POPL '21, Article 33, audit P8, C11). Protocol-directed verification of effectful continuations.
- **Interaction Trees**: Xia et al. (2020, *Interaction Trees*, POPL '20, Article 51, audit P37, C12).
  Monadic representation where operations yield interaction nodes carrying continuations.

#### 2. Effect4 Adaptation, Assumptions, and Exclusions
- **Adapting Protocol-Directed Free Monads**: `TypedProg` is an inductive free-monad residual typing
  judgment over `RProgram` (`Effects.Program (SyncOp ⊕ FiberOp) ExitV`). Visible operations carry Lean
  function continuations in the semantic carrier.
- **Stored Syntax vs. Semantic Continuations (Row 163)**: Stored `Eff` syntax uses first-order program
  trees with positional inputs. Lean function continuations exist solely in the semantic carrier `RProgram`.
- **Refutation of Unrestricted Bind (Row 148, `E4-TYPED-CE-030`)**: `TypedProg` is **not closed under
  unrestricted monadic bind**. Closing markers (`unguard ex`) carry exit values directly; sequencing across
  non-local control flow violates naive bind typing. Sequencing is therefore established per-construct via
  explicit compatibility lemmas (`seq_typed`, `onFailure_typed`).
- **Closed Root Requirement Rows (Row 117)**: Admitted programs enforce `rootTy.requires = empty` at load time,
  reflecting rc.112's `runPromise` contract (`Effect.ts:17494-17497`).

#### 3. Project Definition and Judgment
Residual programs resulting from elaboration are typed by `Effect4.Program.Typed.TypedProg`:
```lean
inductive TypedProg (root : ProgramSource) : World → EffTy → RProgram → Prop
```
([Residual.lean:266](file:///src/Effect4/Laws/Program/Typed/Residual.lean#L266)). Operation clauses require certificate validation and enforce that
continuations type for all permitted replies at later worlds. Dedicated typing arms govern control
bracket markers: `.guard`, `.unguard`, `.finishFinalizer`, and `.scopeExit`.

#### 4. Required Properties and Obligations
- **Sequence compatibility (`seq-typed`)**: Compatibility lemma for sequence composition:
  `TypedProg root w mid a → (∀ w', w.leHost w' → ∀ v, Fits w' v mid.answer → TypedProg root w' ty (k v)) → mid.error = ty.error → TypedProg root w ty ((guardR .onSuccess a).bind (seqR k))`
  ([`seq_typed`](file:///src/Effect4/Laws/Program/Typed/Seq.lean#L153)). Proved witness.
- **Close invariance (`close-typed`)**: Invariance of `TypedProg` under closing `unguard` markers
  ([`close_typed`](file:///src/Effect4/Laws/Program/Typed/Seq.lean#L49)). Proved witness.
- **Bind refutation (`bind-closed`)**: Refutation of unrestricted bind closure
  ([`typedProg_not_bind_closed`](file:///Test/Program/TypedProgBindRed.lean#L32), register row `E4-TYPED-CE-030`). Refuted claim.
- **Fundamental elaboration property (`denote-typed`)**: Denotation of a checked program is `TypedProg`:
  `typeOfProgram root.sig root.prog = some ty → TypedProg root w ty (denoteR root)`
  ([`denoteR_typed`](file:///src/Effect4/Laws/Program/Typed/Assembly.lean#L1650)). Open ledger goal.
- **Failure handler compatibility (`on-failure-typed`)**: Compatibility lemma for error recovery bracket `onFailure`
  (decisions row 148, M5). Required absent obligation.

#### 5. Next Bounded Coding Task and Completion Evidence
- **Next Slice**: Assurance Path D2 constructor group compatibility for `onFailure` (`onFailure_typed`).
- **Owner**: Seat D2 ([brief-gemini-implementation.md](file:///docs/research/2026-10-01-semantics/seat-B/brief-gemini-implementation.md)).
- **Completion Evidence**: Compiling `Effect4.Laws.Program.Typed.Seq`, zero new axioms outside `[propext, Quot.sound]`,
  and registering `on-failure-typed` as a proved witness. See [implementation-inventory.md](file:///docs/research/2026-10-01-semantics/gemini/implementation-inventory.md#L94-L116) §2.2 and §3.

---

### 2.3 Concept 3: Scope Lifetime & Finalization (`scope-lifetime-finalization`)

#### 1. What the Literature Defines
- **Region-Based Resource Management**: ATTAPL ch. 3 (Henglein, Makholm, Niss, pp. 87–136, audit A1, A5).
  Lexically scoped memory regions and lifetime-bounded resource allocation.
- **Control Stacks & Unwinding**: Harper PFPL ch. 28 (*Control Stacks*, pp. 261–268; §28.1 *Machine Definition*,
  §28.2 *Safety*, audit H1, H2, H3, H7). Frame allocation, stack unwinding, and safety during abnormal termination.

#### 2. Effect4 Adaptation, Assumptions, and Exclusions
- **Adapting Scopes**: Scopes in Effect4 are dynamic resource containers (`Scope`) holding an
  insertion-ordered finalizer table.
- **State-First Unwinding (Row 156, `E4-RUN-CE-001`)**: `closeState` updates the machine state to `Closed`
  *before* invoking finalizers, ensuring re-entrant additions observe closed state immediately.
- **LIFO Finalizer Execution (`E4-RUN-CE-002`)**: Finalizers execute in strict reverse registration order (`closeOrder_eq`).
- **Close Idempotence (`E4-RUN-CE-003`)**: Closing an already closed scope returns `Exit.void` without re-running finalizers.
- **Exclusion of Absent Scopes (Row 156, `E4-SCHED-CE-020`)**: Exiting or closing an absent scope halts the machine;
  dangling scope handles are invalid. Defect transmission is restricted by `ShapeFree` (row 152).

#### 3. Project Definition and Judgment
Scope state and finalization lifecycles are modeled in `src/Effect4/Machine/Scope.lean`:
```lean
structure Scope (κ φ β ε δ ι α : Type u) where
  state : ScopeState κ φ β ε δ ι α
```
([Scope.lean:750](file:///src/Effect4/Machine/Scope.lean#L750)). A scope transitions from `openEmpty` or `openMap` to `closed exit`. Scope presence
in the typed world is governed by `ScopeLive w sc` ([World.lean](file:///src/Effect4/Laws/Program/Typed/World.lean)), witnessed by `fits_scope_inv`.

#### 4. Required Properties and Obligations
- **Close idempotence (`close-idempotent`)**: Closing an already closed scope is a no-op:
  `self.isClosed = true → close run self ex = (self, Exit.void)` ([`close_idempotent`](file:///src/Effect4/Machine/Scope.lean#L950)). Proved witness.
- **Consecutive close idempotence (`close-twice`)**: Applying close twice produces void:
  `close run (close run self first).1 second = ((close run self first).1, Exit.void)` ([`close_twice`](file:///src/Effect4/Machine/Scope.lean#L960)). Proved witness.
- **LIFO execution order (`close-order-eq`)**: Finalizers run in reverse registration order:
  `self.closeOrder = (self.finalizers.map Prod.snd).reverse` ([`closeOrder_eq`](file:///src/Effect4/Machine/Scope.lean#L978)). Proved witness.
- **Re-entrant addition semantics (`close-reentrant-add`)**: Adding to closed scope executes immediately:
  `self.isClosed = false → addExit run (closeState self ex) k φ = (closeState self ex, run φ ex)` ([`close_reentrant_add`](file:///src/Effect4/Machine/Scope.lean#L969)). Proved witness.
- **Close iterator protocol (`close-seq-protocol`)**: Close walk satisfies iterator protocol for clean finalizers
  ([`closeSeq_protocol`](file:///Test/Program/ProtocolPosts.lean#L970)). Proved witness.
- **Scope validity under nesting (`scope-validity-open`)**: General scope validity under dynamic parent-child nesting
  (D4 hand-back, row 156). Required absent obligation.

#### 5. Next Bounded Coding Task and Completion Evidence
- **Next Slice**: Reconcile D4 scope lifetime hand-back and prove scope handle validity across nested forks and joins.
- **Owner**: Seat D4.
- **Completion Evidence**: Compiling `Effect4.Laws.Machine.ScopeMachine` and verifying scope postcondition invariants.
  See [implementation-inventory.md](file:///docs/research/2026-10-01-semantics/gemini/implementation-inventory.md#L118-L137) §2.3.

---

### 2.4 Concept 4: Reactive Scheduling & Machine Invariants (`reactive-scheduling`)

#### 1. What the Literature Defines
- **Type Soundness for Abstract Machines**: Wright & Felleisen (1994, *A Syntactic Approach to Type Soundness*,
  Information and Computation 115(1): 38–94, audit P36, C24). Type safety formulated as progress and subject reduction.
- **Concurrent & Distributed Execution**: Harper PFPL chs. 39–41 (*Process Calculus*, *Concurrent Algol*,
  *Distributed Algol*, pp. 371–406, audit H9). Small-step concurrent transition systems.
- **Invariance & Liveness**: Owicki & Gries (1976); Manna & Pnueli (1991, *The Temporal Logic of
  Reactive and Concurrent Systems*, Springer, audit C22). Invariants over execution traces.
- **Trace Inclusions & Simulations**: Lynch & Vaandrager (1995, audit P38, C4). Safety methods
  establish trace inclusion, not general liveness.

#### 2. Effect4 Adaptation, Assumptions, and Exclusions
- **Adapting Small-Step Machines**: The Effect4 runtime machine is an operational small-step state machine
  (`RunMachine`) executing commands from decision queues (`RunDecision`).
- **Theoretical Distinction (Row 139)**: `machineTyped_not_halted` establishes an invariant consequence:
  `stuck = none`. It does **not** establish operational progress (producing a successor transition).
  Calling it "progress" would conflate an invariant consequence with transition existence. Operational
  progress additionally requires classifying configurations into finished, stepping, or live frontier states.
- **Finite Fairness**: `flush_fair` guarantees actual callback entry within a round bound for armed owners
  in a duplicate-free queue (`FlushReady`). It does not promise eventual callback termination or external host response.
- **Exclusions (Rows 106, 107, 134)**: Unbounded tokens are excluded by `GuardState.keysBelow` in `QueueOk`.
  Defect-bearing exits are excluded by `NoShapeDefect`. Timer and race columns are separated in configuration typing.

#### 3. Project Definition and Judgment
The operational configuration and decision types are defined in `src/Effect4/Machine/Fibers.lean`:
```lean
structure RunMachine (ν σ : Type u) (β : Type v) (ε δ ι α χ : Type u) (St : Type (max u v)) ...
inductive RunDecision ...
```
([Fibers.lean:438, 461](file:///src/Effect4/Machine/Fibers.lean#L438)). Machine type safety is maintained by the configuration invariant `MachineTyped root rootTy w m`
([Assembly.lean:251](file:///src/Effect4/Laws/Program/Typed/Assembly.lean#L251)).

#### 4. Required Properties and Obligations
- **Invariant non-halted consequence (`machine-typed-not-halted`)**: A halted machine cannot satisfy `MachineTyped`:
  `MachineTyped root rootTy w (m.halt why) → False` ([`machineTyped_not_halted`](file:///src/Effect4/Laws/Program/Typed/Assembly.lean#L311)). Proved witness.
- **Finite queue fairness (`flush-fair`)**: Callback entry within rounds bound:
  `m.armed.Nodup → FlushReady interp fuel m.armed.length m = true → m.armed.length ≤ rounds → ∀ owner ∈ m.armed, FiredWithin interp fuel rounds m owner = true`
  ([`flush_fair`](file:///src/Effect4/Laws/Machine/Scheduling.lean#L413)). Proved witness.
- **Step invariant lifting (`drivestate-lift`)**: Step invariant lifting for sequential command loops
  ([`driveState_lift`](file:///src/Effect4/Laws/Machine/Lift.lean#L56)). Proved witness.
- **Scheduler step preservation (`step-loop-preserves`, `step-deliver-preserves`)**: Preservation of `MachineTyped`
  across `stepDecision` on loop and deliver decisions ([`M6Ledger.step_loop`](file:///src/Effect4/Laws/Program/Typed/Assembly.lean#L1683), [`M6Ledger.step_deliver`](file:///src/Effect4/Laws/Program/Typed/Assembly.lean#L1694)). Open ledger goals.
- **Operational progress (`scheduler-progress`)**: Every typed state is either terminal, takes a step, or is at a live frontier
  (decisions row 139). Required absent obligation.
- **Infinite liveness (`fair-scheduling`)**: Temporal liveness under weak fairness (Requirement R12). Required absent obligation.

#### 5. Next Bounded Coding Task and Completion Evidence
- **Next Slice**: D5 command and field invariant preservation census across scheduler commands (rows 134, 181).
- **Owner**: Seat D5.
- **Completion Evidence**: Proof of `M6Ledger.step_loop` and `M6Ledger.step_deliver` closing goals in `M6Ledger`.
  See [implementation-inventory.md](file:///docs/research/2026-10-01-semantics/gemini/implementation-inventory.md#L139-L161) §2.4.

---

### 2.5 Concept 5: Exact Codecs & Data Plane Embeddings (`exact-codecs`)

#### 1. What the Literature Defines
- **Invertible Syntax Descriptions**: Rendel & Ostermann (2010, *Invertible Syntax Descriptions:
  Unifying Parsing and Pretty Printing*, Haskell '10, pp. 1–12, audit P32, C5, C18). Round-trip
  guarantees between concrete syntax and abstract syntax trees.
- **Bidirectional Tree Lenses**: Foster et al. (2007, *Combinators for Bi-Directional Tree Transformations*,
  TOPLAS 29(3), audit P11, C5, C18). Well-behaved lenses satisfying GetPut and PutGet laws.
- **Lawful Prisms & Profunctor Optics**: Pickering, Gibbons, Wu (2017, *Profunctor Optics: Modular Data
  Accessors*, Programming 1(2), audit P44, C18).

#### 2. Effect4 Adaptation, Assumptions, and Exclusions
- **Adapting Exact Embeddings**: An exact embedding `write : A → F`, `read : F → Option A` satisfies:
  1. Totality on its domain.
  2. Retraction: `read (write a) = some a`.
  3. Exactness: `read v = some a → norm v = write a` modulo an explicit normaliser.
- **Normalisers (Row 128)**: `normJ` sorts JSON object keys; `normS` normalises Schema representation ASTs.
- **Approved Erasure List (Row 179)**: `normS` erases **only nine approved annotation keys** (`identifier`,
  `title`, `description`, `examples`, `default`, `documentation`, `message`, `arbitrary`, and check annotations).
  Arbitrary metadata (`effect4/*`) is **not** unconditionally erased.
- **Pinned Limitation (`E4-SCHEMA-CE-059`)**: Overlapping union variants decode with left bias; exactness
  holds on unambiguous disjoint sums.
- **Planned Feature (Row 165)**: Positional record codecs (`record-codec-layout`) planned for data wave W5.

#### 3. Project Definition and Judgment
Data plane conversions in Effect4 are exact embeddings between syntactic carriers and serializable formats:
```lean
theorem decode_iff {t : Ty} {j : Json} {v : Val} :
    decode t j = some v ↔ ∃ j', encode t v = some j' ∧ Codec.normJ j' = Codec.normJ j
theorem ofSchema_exact (r : Representation) : ∀ t, ofSchema r = some t → normS r = schema t
```
([Codec.lean:1052](file:///src/Effect4/Laws/Schema/Codec.lean#L1052), [Bridge.lean:492](file:///src/Effect4/Schema/Bridge.lean#L492)).

#### 4. Required Properties and Obligations
- **Exactness modulo key sorting (`decode-iff`)**: JSON decoding is exact modulo `normJ`
  ([`decode_iff`](file:///src/Effect4/Laws/Schema/Codec.lean#L1052)). Proved witness.
- **Retraction on canonical values (`decode-encode`)**: Decoding an encoded canonical value recovers it
  ([`decode_encode`](file:///src/Effect4/Laws/Schema/Codec.lean#L1065)). Proved witness.
- **Schema exactness modulo nine keys (`of-schema-exact`)**: Schema decoding is exact modulo `normS`
  ([`ofSchema_exact`](file:///src/Effect4/Schema/Bridge.lean#L492)). Proved witness.
- **Schema retraction (`of-schema-schema`)**: Inverting schema representations on reserved-free types
  ([`ofSchema_schema`](file:///src/Effect4/Schema/Bridge.lean#L412)). Proved witness.
- **Record layout codecs (`record-codec-layout`)**: Exact codec representation for positional record layouts
  (decisions row 165, Data-Wave W5). Planned feature claim.

#### 5. Next Bounded Coding Task and Completion Evidence
- **Next Slice**: Data Path W5 exact codecs for numeric and record forms following W4 value appends.
- **Owner**: Seat W5.
- **Completion Evidence**: Round-trip proofs `decode_encode` and `decode_iff` for new forms under `src/Effect4/Laws/Schema/Codec.lean`.
  See [implementation-inventory.md](file:///docs/research/2026-10-01-semantics/gemini/implementation-inventory.md#L163-L182) §2.5.

---

### 2.6 Concept 6: Subtyping Algebra & Normalization (`subtyping-algebra`)

#### 1. What the Literature Defines
- **Subtyping Metatheory**: TAPL ch. 15 (*Subtyping*, pp. 181–208; §15.1 *Subsumption*, §15.2 *The Subtype
  Relation*, §15.4 *Top and Bottom*, audit T9, T48, T49). Preorder properties: reflexivity, transitivity.
- **Algorithmic Subtyping & Joins**: TAPL ch. 16 (*Metatheory of Subtyping*, pp. 209–220; §16.1 *Algorithmic
  Subtyping*, §16.2 *Algorithmic Typing*, §16.3 *Joins and Meets*, audit T10, T50, T51). Algorithmic soundness,
  completeness, and join-semilattice properties.
- **Set-Theoretic & Semantic Subtyping**: Giuseppe Castagna (2024, *Programming with Union, Intersection,
  and Negation Types*, audit P6, C6). Subtyping in the presence of union and bottom types.

#### 2. Effect4 Adaptation, Assumptions, and Exclusions
- **Adapting Preorder to Canonical Forms**: `Ty.subN` computes subtyping by evaluating raw subtyping `sub`
  on normalized canonical forms `Ty.normalize`. Canonical types `CTy` form a bounded join-semilattice with `Ty.join`.
- **Exclusion & Repair of Raw Subtyping (Row 137, `E4-TYPED-CE-009`)**: Raw `sub` does not distribute products
  over unions; subtyping equivalence and comparisons are defined through `subN`.
- **Exclusion of Function Types (Row 163)**: No function arrow types exist in `Ty`; arrow subtyping is excluded.
- **Planned Feature (Row 119)**: `Ty` currently has 20 constructors without record or app constructors. Record
  and app subtyping rules (`record-app-subtyping`) are planned for data-wave stages W2/W4.

#### 3. Project Definition and Judgment
The static type language `Ty` possesses a decidable subtyping preorder `Ty.subN` evaluated on normalized forms:
```lean
def subN (a b : Ty) : Bool := sub a.normalize b.normalize
theorem subN_equiv_iff (a b : Ty) : (subN a b = true ∧ subN b a = true) ↔ a.normalize = b.normalize
```
([TypeAlgebra.lean:1067, 1088](file:///src/Effect4/Laws/Program/TypeAlgebra.lean#L1067)). Canonical types `CTy` form a bounded join-semilattice.

#### 4. Required Properties and Obligations
- **Reflexivity (`subn-refl`)**: Normalized subtyping is reflexive:
  `Ty.subN a a = true` ([`subN_refl`](file:///src/Effect4/Laws/Program/TypeAlgebra.lean#L1069)). Proved witness.
- **Transitivity (`subn-trans`)**: Normalized subtyping is transitive:
  `Ty.subN a b = true → Ty.subN b c = true → Ty.subN a c = true` ([`subN_trans`](file:///src/Effect4/Laws/Program/TypeAlgebra.lean#L1071)). Proved witness.
- **Equivalence characterization (`subn-equiv-iff`)**: Subtyping equivalence coincides with normal-form equality
  ([`subN_equiv_iff`](file:///src/Effect4/Laws/Program/TypeAlgebra.lean#L1088)). Proved witness.
- **Normalization idempotence (`normalize-idem`)**: Normalization is idempotent:
  `(a.normalize).normalize = a.normalize` ([`normalize_idem`](file:///src/Effect4/Laws/Program/TypeAlgebra.lean#L1081)). Proved witness.
- **Antisymmetry on canonical types (`sub-antisymm-canonical`)**: `subN` is antisymmetric on canonical representatives:
  `Canonical a → Canonical b → subN a b = true → subN b a = true → a = b` ([`sub_antisymm_canonical`](file:///src/Effect4/Laws/Program/TypeAlgebra.lean#L1035)). Proved witness.
- **Record and application subtyping (`record-app-subtyping`)**: Subtyping, join, and normalization laws for record and app constructors
  (decisions row 119, Data-Wave W2/W4). Planned feature claim.

#### 5. Next Bounded Coding Task and Completion Evidence
- **Next Slice**: Data-Wave W2/W4 generator integration for `Ty.record` and `Ty.app`, extending normalization and subtyping order.
- **Owner**: Seat W2/W4.
- **Completion Evidence**: Reflexivity and transitivity proofs for new constructors in `Effect4.Laws.Program.TypeAlgebra`.
  See [implementation-inventory.md](file:///docs/research/2026-10-01-semantics/gemini/implementation-inventory.md#L184-L203) §2.6.

---

### 2.7 Concept 7: Initial Algebras & Catamorphic Folds (`initial-algebras-folds`)

#### 1. What the Literature Defines
- **Initial Algebra Semantics**: Meijer, Fokkinga, Paterson (1991, *Functional Programming with Bananas,
  Lenses, Envelopes and Barbed Wire*, FPCA '91, LNCS 523, pp. 124–144, audit P24, C7, C14).
  Catamorphisms, anamorphisms, and the universal property of initial algebras.
- **Algebraic Calculation & Fusion**: Jeremy Gibbons (2002, *Calculating Functional Programs*, LNCS 2297,
  pp. 149–203, audit P12, C19). Catamorphism fusion and fold uniqueness laws.
- **Algebraic Handlers**: Plotkin & Pretnar (2009, *Handlers of Algebraic Effects*, ESOP 2009, LNCS 5502,
  pp. 80–94, audit P29). Handlers as folds over free monads.

#### 2. Effect4 Adaptation, Assumptions, and Exclusions
- **Adapting Initial Algebras**: Free syntax sorts (`Eff`, `Ty`, `Term`, `Store.Val`, `Representation`)
  are generated from algebraic signatures with explicit algebra structures (`EffAlgebra`, `TyAlgebra`).
  Traversals are catamorphisms (`cata_eff`, `cata_ty`).
- **Single-Owner & Census Rule**: Hand `match` statements across syntax sorts are prohibited unless admitted
  in `#traversal_census` (`docs/core/traversal-census.md`).
- **Provable Uniqueness vs. Defeq**: Fold uniqueness (`hom_eq_cata_eff`) is a **provable proposition** via induction,
  not a definitional equality (`rfl`).
- **Finite Syntax Folding (Row 127)**: `inhabited` is a fold over finite syntax, not an infinite equi-recursive unfolding.

#### 3. Project Definition and Judgment
Catamorphic folds and algebra homomorphisms are defined in `src/Effect4/Program/Fold.lean`:
```lean
theorem hom_eq_cata_eff {Op : Type} {R : EffFam → Type u}
    {alg : EffAlgebra Op R} (hom : EffHom alg) (node : Effect4.Program.Eff Op) :
    hom.f_eff node = cata_eff alg node
def inhabited (t : Ty) : Bool := cata_ty inhabitedAlg t
```
([Fold.lean:1270](file:///src/Effect4/Program/Fold.lean#L1270), [Admission.lean:79](file:///src/Effect4/Program/Admission.lean#L79)).

#### 4. Required Properties and Obligations
- **Uniqueness of catamorphism (`hom-eq-cata-eff`)**: Any algebra homomorphism out of `Eff` is pointwise equal to `cata_eff`
  ([`hom_eq_cata_eff`](file:///src/Effect4/Program/Fold.lean#L1270)). Proved witness.
- **Inhabitation characterization (`inhabited-iff-fits`)**: Syntactic `inhabited` fold characterizes semantic non-emptiness in `Fits`:
  `inhabited t = true ↔ ∃ w v, Fits w v t` ([`inhabited_iff_fits`](file:///src/Effect4/Laws/Program/Typed/Membership.lean#L2614)). Proved witness.
- **Fold congruence (`cata-eff-congr-on`)**: Fold congruence over agreeing algebra implementations
  ([`cata_eff_congr_on`](file:///src/Effect4/Laws/Program/Signature.lean#L518)). Proved witness.
- **Traversal census maintenance**: 100% fold coverage enforced by `#traversal_census`.

#### 5. Next Bounded Coding Task and Completion Evidence
- **Next Slice**: Regenerate fold signatures and catamorphisms when adding new `Ty` and `Val` constructors in Data Wave W2/W4 (row 182).
- **Owner**: Seat W2/W4.
- **Completion Evidence**: Passing `make gen-data` and `#traversal_census` verification.
  See [implementation-inventory.md](file:///docs/research/2026-10-01-semantics/gemini/implementation-inventory.md#L205-L221) §2.7.

---

### 2.8 Concept 8: Context Requirements & Provision (`context-requirements`)

#### 1. What the Literature Defines
- **Coeffect Calculi & Context Dependence**: Petricek, Orchard, Mycroft (2014, *Coeffects: A Calculus of
  Context-Dependent Computation*, ICFP '14, pp. 1–13, audit C8). Context requirements as indexed comonadic
  or graded structural modalities.
- **Row Polymorphism & Subeffecting**: Daan Leijen (2014, *Koka: Programming with Row-Polymorphic Effect
  Types*, MSFP 2014, EPTCS 153, pp. 100–126, audit P22, C8, C31). Row operations (union, diff) for ambient
  capability tracking.

#### 2. Effect4 Adaptation, Assumptions, and Exclusions
- **Adapting Flat Coeffects**: Static environmental service dependencies are modeled as flat canonical rows
  `Row ServiceKey`. Context satisfaction is simple subset inclusion (`r.Subset ctx.keysRow`), avoiding comonadic
  adjunctions or complex semirings.
- **Closed Root Rows (Row 117)**: Top-level program execution requires closed requirement rows (`rootTy.requires = empty`).
  Frames carrying `missingService` across boundaries are excluded at load time (`E4-TYPED-CE-008`).
- **Closed Layer Bodies (Rows 104, 105)**: Layer bodies are built at closed lexical points (`Point.layerBuild`),
  and layer values must fit declared service types (`E4-PROV-CE-005`, `-006`).

#### 3. Project Definition and Judgment
Context structures and satisfaction are modeled in `src/Effect4/Machine/Context.lean`:
```lean
abbrev Requirement : Type := Row ServiceKey
def Satisfies (self : Context U) (r : Requirement) : Prop := r.Subset self.keysRow
```
([Context.lean:76, 123](file:///src/Effect4/Machine/Context.lean#L76)). Layer composition and capability discharge are governed by `LayerTy`
([Provision.lean:87, 99](file:///src/Effect4/Program/Provision.lean#L87)).

#### 4. Required Properties and Obligations
- **Empty requirement satisfaction (`satisfies-empty`)**: Empty requirements are unconditionally satisfied:
  `Satisfies ctx Row.empty = true` ([`satisfies_empty`](file:///src/Effect4/Machine/Context.lean#L149)). Proved witness.
- **Single requirement lookup (`satisfies-single`)**: Singleton requirements check key membership:
  `Satisfies ctx (Row.single k) = true ↔ k ∈ ctx.keys` ([`satisfies_single`](file:///src/Effect4/Machine/Context.lean#L153)). Proved witness.
- **Union requirement splitting (`satisfies-union`)**: Union requirements split into conjunction:
  `Satisfies ctx (r₁ ∪ r₂) = (Satisfies ctx r₁ && Satisfies ctx r₂)` ([`satisfies_union`](file:///src/Effect4/Machine/Context.lean#L164)). Proved witness.
- **Weakening monotonicity (`satisfies-weaken`)**: Monotonicity under context extension:
  `r.Subset r' → Satisfies ctx r' = true → Satisfies ctx r = true` ([`satisfies_weaken`](file:///src/Effect4/Machine/Context.lean#L176)). Proved witness.
- **Service capability discharge (`provide-discharges`)**: Layer provision discharges output capabilities:
  `k ∈ t.out → k ∉ t.requires → k ∉ (s.provide t).requires` ([`provide_discharges`](file:///src/Effect4/Program/Provision.lean#L87)). Proved witness.
- **Closed layer composition (`provide-closed`)**: Composing closed layers yields closed requirements:
  `t.Closed → s.requires.Subset t.out → (s.provide t).Closed` ([`provide_closed`](file:///src/Effect4/Program/Provision.lean#L99)). Proved witness.
- **Layer sharing invariants (`layer-sharing-contract`)**: Dynamic layer memoization and sharing invariants
  (`LayerSharingContract.lean`). Required work.

#### 5. Next Bounded Coding Task and Completion Evidence
- **Next Slice**: Reconcile `LayerSharingContract.lean` and finalize layer certificate representation in M5 (rows 170, 176).
- **Owner**: Seat D2 / Coordinator.
- **Completion Evidence**: Clean compilation of `Test/Program/LayerSharingContract.lean`.
  See [implementation-inventory.md](file:///docs/research/2026-10-01-semantics/gemini/implementation-inventory.md#L223-L244) §2.8.

---

### 2.9 Concept 9: Host Session Protocol & Boundary (`host-session-protocol`)

#### 1. What the Literature Defines
- **Session Types & Propositions as Sessions**: Philip Wadler (2012 ICFP / 2014 JFP, *Propositions as Sessions*,
  JFP 24(2-3): 384–418, audit P35, P41, C46); Honda, Vasconcelos, Kubo (1998, *Language Primitives and
  Type Discipline for Structured Communication-Based Programming*, ESOP '98, audit P16, C9).
  Duality, session sequencing, and protocol safety.
- **I/O Automata & Labeled Transitions**: Lynch & Vaandrager (1995, *Forward and Backward Simulations I:
  Untimed Systems*, Information and Computation 121, pp. 214–233, audit C4, C47).

#### 2. Effect4 Adaptation, Assumptions, and Exclusions
- **Adapting 4-State Session Automaton**: The interaction between the Effect4 runtime machine and the
  external host is governed by a 4-state protocol automaton (`.idle`, `.awaitingAsync`, `.parked`, `.terminated`).
- **External Driver Assumption (`host-progress`)**: Host progress (supplying answers to pending async requests)
  is an **external driver assumption** (`docs/core/host-boundary.md`), outside the closed runtime. It is **not**
  an owed internal proof obligation.
- **Exclusion of Boundary Handles (Row 97, `E4-HOST-CE-007`)**: Internal handle kinds (`cell`, `promise`,
  `fiber`, `scope`, `context`) are strictly refused at table admission.
- **Route A Boundary Decoding (Decision 12, Row 122)**: Boundary decoding checks value membership before runtime admission.

#### 3. Project Definition and Judgment
The host protocol automaton and transition checks are modeled in `src/Effect4/Api/HostProtocol.lean`:
```lean
structure Protocol where
  version : Nat
  initial : State
  states : List State
  transitions : List Edge
  records : List RecordShape
def allows (source : State) (label : Label) (target : State) : Bool :=
  hostProtocol.transitions.contains ⟨source, label.tag, target⟩
```
([HostProtocol.lean:48, 88](file:///src/Effect4/Api/HostProtocol.lean#L48)). External answers are submitted through `HostSession.submit` and applied via `HostSession.answer`.

#### 4. Required Properties and Obligations
- **Allowed answer step (`allows-answer`)**: Async answering is an allowed transition from `.awaitingAsync`:
  `allows .awaitingAsync (.answerAsync id tok ans) target = true` ([`allows_answer`](file:///src/Effect4/Laws/Run.lean#L289)). Proved witness.
- **Host reply commutativity (`reply-commute`)**: Independent host answers commute in session queues:
  `submit r₁ (submit r₂ s) = submit r₂ (submit r₁ s)` ([`reply_commute`](file:///src/Effect4/Laws/Api/HostSession.lean#L112)). Proved witness.
- **Frontier awaitHost inversion (`frontier-awaithost`)**: Machine awaitingAsync state matches frontier reason:
  characterization of frontier state matching `.awaitingAsync` ([`observe_awaitingAsync_iff`](file:///src/Effect4/Laws/Api/Frontier.lean#L40)). Proved witness.
- **External host progress (`host-progress`)**: External driver progress assumed under `docs/core/host-boundary.md`. External assumption.
- **Typed replay under session (`typed-replay-session`)**: Public typed replay route under keyed host session
  (decisions row 98). Required work.

#### 5. Next Bounded Coding Task and Completion Evidence
- **Next Slice**: Connect `HostSession` driver submission queue to `Typed.replay` under decisions row 98.
- **Owner**: API / Laws.
- **Completion Evidence**: Compiling session replay test in `Test/Api/HostSessionReplay.lean`.
  See [implementation-inventory.md](file:///docs/research/2026-10-01-semantics/gemini/implementation-inventory.md#L246-L263) §2.9.

---

### 2.10 Concept 10: Translation & Simulation Metatheory (`translation-simulation`)

#### 1. What the Literature Defines
- **Compiler Correctness & Semantic Preservation**: Xavier Leroy (2009, *Formal Verification of a
  Realistic Compiler*, CACM 52(7), audit C10). Semantic preservation relating source and target behaviors.
- **Forward & Backward Simulations**: Lynch & Vaandrager (1995, *Forward and Backward Simulations I:
  Untimed Systems*, Information and Computation 121, pp. 214–233, audit C4). Trace inclusion and simulation relations.
- **Coalgebraic Moore Behaviors**: Bart Jacobs (2012 draft, *Introduction to Coalgebra: Mathematics
  of State and Observation*, ch. 2, audit P17, C23). Deterministic behavior functors on decision words.
- **Syntactic Soundness**: Wright & Felleisen (1994, audit P36). Safety on closed programs.

#### 2. Effect4 Adaptation, Assumptions, and Exclusions
- **Adapting Simulation Relations**: Behavioral agreement between operational execution (`Api.run`) and
  denotational meaning (`meaning`) is established as equal-observation theorems over restricted fragments
  (`Straight`, `Looped`, and `M7Fragment`).
- **Separation of Route vs. Goals**: `m7_of_ledger` proves a **conditional implication** ($M5 \land M6 \implies M7$),
  not the capstone premises or conclusions themselves. In the registry, `m7-route` is `.fundamentalProperty`
  (a proved witness for the route theorem), while the capstone results are `.adequacy` (`.goal`s: `M7Exits`,
  `M7Stores`, `M7NoHalt`, `ExitHandlesValid`).
- **Boundary & Fragment Exclusions (Rows 138, 95, 117)**: M7 is stated strictly on `M7Fragment` with the host
  row table **fixed empty** (`root.table = []`), decision tapes answer-free, and requirement rows closed
  (`rootTy.requires = empty`). Non-empty host tables are deferred to R6 (DI-57).

#### 3. Project Definition and Judgment
Agreement theorems and fragment definitions are modeled in `src/Effect4/Laws/Program/Agreement/Machine.lean`
and `src/Effect4/Laws/Program/Typed/Assembly.lean`:
```lean
theorem run_eq_meaning (e : NativeEff) (fuel : Nat) (hs : Straight e = true) ...
structure M7Fragment (root : ProgramSource) (rootTy : EffTy) (tape : List Api.Decision) : Prop where
  lawful : LawfulSource root
  emptyTable : root.table = []
  checked : Program.typeOfProgram root.signature root.program = some rootTy
  closed : ClosedEff rootTy
  closedRow : rootTy.requires = Env.Requirement.empty
  answerFree : ∀ d ∈ tape, NoHostAnswer d
```
([Machine.lean:1922](file:///src/Effect4/Laws/Program/Agreement/Machine.lean#L1922), [Assembly.lean:1478](file:///src/Effect4/Laws/Program/Typed/Assembly.lean#L1478)).

#### 4. Required Properties and Obligations
- **Straight program agreement (`run-eq-meaning`)**: Frame machine execution matches denotational meaning on `Straight`:
  `Straight e → Api.run e fuel = finished ∧ exit = meaning e` ([`run_eq_meaning`](file:///src/Effect4/Laws/Program/Agreement/Machine.lean#L1922)). Proved witness.
- **Loop agreement (`loop-agreement`)**: Replay agreement holds across straight loop steps
  ([`loopAgreement_of_straight`](file:///src/Effect4/Laws/Program/LoopAgreement.lean#L42)). Proved witness.
- **Reference machine simulation (`run-eq-ref`)**: Frame machine replay matches term reference replay at empty host table
  ([`run_eq_ref`](file:///src/Effect4/Laws/Program/RuntimeR.lean#L211)). Proved witness.
- **M7 conditional route (`m7-route`)**: Derivation of M7 capstone conditionally from M5 and M6 ledger components
  ([`m7_of_ledger`](file:///src/Effect4/Laws/Program/Typed/Assembly.lean#L1593)). Proved witness.
- **Capstone M7 goals (`m7-capstone-goals`)**: Exit value agreement, final store agreement, non-halting, and exit handle
  validity on `M7Fragment` ([`M7.exits_typed`](file:///src/Effect4/Laws/Program/Typed/Assembly.lean#L1789)). Open ledger goal.

#### 5. Next Bounded Coding Task and Completion Evidence
- **Next Slice**: Discharge M5 residual typing and M6 scheduler step preservation premises to activate the `m7_of_ledger`
  conditional route on `M7Fragment`.
- **Owner**: Coordinator / Capstone.
- **Completion Evidence**: Discharging `M7Exits`, `M7Stores`, `M7NoHalt`, and `ExitHandlesValid` without ledger obligations.
  See [implementation-inventory.md](file:///docs/research/2026-10-01-semantics/gemini/implementation-inventory.md#L265-L286) §2.10.

---

## 3. The Object-Language Glossary (Object-Language vs. Host Metatheory)

A frequent point of confusion is that words used to describe Effect4 object-language concepts
("syntax", "elaborate", "print", "read") are identical to names in Lean 4's metaprogramming framework.
The table below disambiguates each term, giving its object-language denotation, its in-tree type
and file location, its Lean 4 metaprogramming counterpart, and whether the two denote the same concept.

| Our Word | What It Denotes Here | Our Type and File:Line | Lean's Layer with Same Word | Same Thing or Not? |
|---|---|---|---|---|
| **syntax** | First-order free objects representing abstract syntax trees: programs, types, terms, values, representations. | `Eff Op` ([Eff.lean:28](file:///src/Effect4/Program/Eff.lean#L28)), `Ty` ([Ty.lean:37](file:///src/Effect4/Program/Ty.lean#L37)), `Term` ([Term.lean:100](file:///src/Effect4/Machine/Term.lean#L100)), `Store.Val` ([Value.lean:24](file:///src/Effect4/Machine/Value.lean#L24)), `Representation` ([Bridge.lean:56](file:///src/Effect4/Schema/Bridge.lean#L56)). | `Lean.Syntax` (host concrete syntax tree produced by Lean's parser). | **No.** Lean's `Syntax` is host syntax for source code, used only by our authoring macros and custom commands. Our syntax types are first-order data structures. |
| **elaborate** *(Sense 1: Lean)* | Translation of Lean host syntax into Lean core expressions. | N/A (Lean metaprogramming framework). | `Lean.Elab.TermElabM`, `Lean.Elab.CommandElabM`. | **Host only.** Standard Lean compilation pass. |
| **elaborate** *(Sense 2: Authoring)* | Desugaring the authoring surface DSL into `Eff` programs; total by refusal. | `elaborate` ([Authoring.lean:307](file:///src/Effect4/Program/Authoring.lean#L307)), `elaborateModule` ([Authoring.lean:386](file:///src/Effect4/Program/Authoring.lean#L386)). Signature: `Src Op → Except Refusal (Eff Op)`. | `Lean.Elab.Term.elabTerm`. | **No.** Our authoring elaboration is an AST-to-AST desugaring returning `Except Refusal`, entirely independent of Lean `Expr`. *(Proposed distinct word: `surfaceElaborate` or `ingest`)*. |
| **elaborate** *(Sense 3: Hefty)* | Lowering scoped syntax into first-order residual operations with bracket markers (`denoteR`). | `denoteR` ([DenoteR.lean:799](file:///src/Effect4/Laws/Program/DenoteR.lean#L799)). Signature: `NativeEff → NativeEff → Point → RProgram`. | None (analogous to compiler lowering / desugaring passes). | **No.** It is a denotational translation from `Eff` to `RProgram` (system map §9 line 284). *(Proposed distinct word: `residualize` or `denote`)*. |
| **print** | Emitting formatted target text from first-order AST data. Invertible on its domain. | `printT` ([Templates.lean:438](file:///src/Effect4/Codegen/Templates.lean#L438)), `printModule` ([Print.lean:142](file:///src/Effect4/Codegen/Print.lean#L142)). | `Lean.PrettyPrinter.ppCategory`, `Lean.Widget.InteractiveCode`. | **No.** Our `print` is part of a verified partial isomorphism with `read` (Rendel–Ostermann). Lean's `pp` is a best-effort display formatter without retraction laws. |
| **read** | Parsing target text back into first-order program ASTs. | `readEff` ([Read.lean:736](file:///src/Effect4/Codegen/Read.lean#L736)), `readModule` ([Read.lean:758](file:///src/Effect4/Codegen/Read.lean#L758)). Signature: `String → Except ReadRefusal Module`. | `Lean.Parser.runParserCategory`. | **No.** Our `read` is an exact retraction of `print` on the readable domain (`read_print`, `Laws/Codegen/ReadPrint.lean:1904`). |
| **render** | Producing string representations of types and atoms for TypeScript or OCaml. | `Ty.render` ([Ty.lean:756](file:///src/Effect4/Program/Ty.lean#L756)), `renderAll` ([Atoms.lean:64](file:///tools/Effect4Gen/Atoms.lean#L64)). | `Lean.PrettyPrinter.delab`. | **No.** Our `render` is a deterministic catamorphic fold into target string templates. |
| **lift** | Authoring macros that lift host Lean literals/expressions into program constructors. | `eff { ... }` macros ([Authoring.lean:42](file:///src/Effect4/Program/Authoring.lean#L42)). | `Lean.Macro`, `Lean.MacroM`. | **Yes in implementation, No in semantics.** Implemented using Lean macros, but semantically represents embedding into the initial algebra. |
| **sugar** | High-level syntax convenience forms in the authoring surface (e.g. `let*`, `try*`). | Authoring DSL syntax rules ([Authoring.lean:80-150](file:///src/Effect4/Program/Authoring.lean#L80)). | `syntax` and `macro_rules` declarations. | **Yes in implementation.** Concrete syntax sugar expanding into AST constructors. |
| **census** | Meta-command auditing repository-wide completeness against an explicit model. | `#traversal_census` ([Census.lean:32](file:///src/Effect4/Laws/Auto/Census.lean#L32)), `#semantics_census` ([Semantics.lean:45](file:///src/Effect4/Laws/Auto/Semantics.lean#L45)). | Custom command elab (`Lean.Elab.Command.elabCommand`). | **Tooling only.** Diagnostic commands inspecting Lean's `Environment`. |
| **gate** | Build-time audit ensuring no axioms outside the ceiling `[propext, Quot.sound]`. | `AxiomGate` ([AxiomGate.lean:376](file:///Test/Audit/AxiomGate.lean#L376)). | `#print axioms`, kernel verification. | **Verification.** Directly verifies Lean environment axioms across all compiled modules. |

---

## 4. Metatheoretical Bounds & Evidence Summary

1. **Axiom Ceiling**: All theorems cited in this document are held to the strict repository axiom
   ceiling: `[propext, Quot.sound]`. Any use of `Classical.choice` is rejected by the axiom gate
   (`Test/Audit/AxiomGate.lean`).
2. **First-Order Data Discipline**: Stored `Eff` syntax is first-order data: its bind continuation
   is another program tree with positional inputs ([Eff.lean:277](file:///src/Effect4/Program/Eff.lean#L277)). `RProgram` is the proof-side
   semantic carrier `Effects.Program RSig ExitV`, whose visible operation nodes carry Lean function
   continuations (`vis : Answer op → Program sig A`). Those functions belong to the semantic model
   and are not stored function values in `Eff` or `Val`.
3. **Simulations vs. Equivalence**: Behavioral relationships are stated strictly as equal-observation
   theorems over specified fragments (`Straight`, `Looped`, empty host table `M7Fragment`), never
   as unqualified "equivalence".
4. **Literature Tracking**: Every textbook chapter and academic paper citation is audited against
   vendored copies in `docs/research/2026-10-01-semantics/citations-audit.md`.
