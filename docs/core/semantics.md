# Semantics: the language's judgments, their literature and their obligations

The authority for what Effect4's semantic judgments mean, which literature each adopts or adapts,
where the language cuts away from that literature, and which properties each must have. Ten
concepts, each in four parts: what the literature defines; our adaptation, assumptions and
exclusions; the definition and judgment in the tree; the required properties.

What this document does not own, and who does:

- **Status.** Whether a property is proved, wanted, refuted, absent or assumed is measured, never
  written here: `generated/semantics.json` and `generated/semantics.md` (`make gen-semantics`;
  `docs/GENERATED.md`, group `semantics`), produced from the registry
  `tools/Tools/SemanticsRegistry.lean` and the loaded environment, every status derived through
  `ProofRef.validate` and `ProofGraph.check`.
- **Decisions.** `docs/core/decisions.md`; the cuts below cite its rows by number.
- **The goal, the sorts, the arrows and the requirements.** `docs/core/system-map.md`.
- **What is next.** `docs/STATE.md`.
- **Counterexamples.** `Test/Counterexamples/REGISTER.md`.
- **The sources.** `docs/research/2026-10-01-semantics/sources/README.md` (vendored with
  checksums) and `docs/research/2026-10-01-semantics/citations-audit.md` (every locator read off a
  vendored page). A theorem, rule or in-section page number of TAPL or ATTAPL is not verified
  until the owner's copies are vendored; those references are marked as cited.

Drafted by Gemini from the semantics pass of 2026-10-01 (concept-first after Codex's review),
reviewed against the tree by the coordinator and checked mechanically (every declaration named
with a `path:line` locator is declared within three lines of it:
`python3 docs/research/2026-10-01-semantics/check-gemini-drafts.py docs/core/semantics.md`).

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
child trees, `src/Effect4/Program/Eff.lean:277`). `RProgram` is the proof-side semantic carrier
`Effects.Program RSig ExitV` (`src/Effect4/Laws/Program/Sched.lean:206`); visible operations carry
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

The generated report checks every concept's selected claims in the loaded environment. A
concept's claims are a selection, not a complete inventory: an owed property is made visible as
an `absent` claim, and a ledger goal the registry does not name is not in the report. Generated tables own evidence status, propositions,
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
(`src/Effect4/Laws/Program/Typed/Membership.lean:112`). It asserts that runtime value `v` inhabits semantic type `ty`
under world `w`. Handle leaves verify capability declarations against `w.Ρ`, `w.«Π»`, `w.Γ`, and scope
persistence `ScopeLive w sc`. At exit types (`.exitOf a e`), the reified cause is checked to be `ShapeFree`
(excluding defects `badName` and `notImplemented`, decisions row 152).

#### 4. Required Properties and Obligations
- **Monotonicity (`fits-mono`)**: World extension preserves value membership.
  (`fits_mono` (`src/Effect4/Laws/Program/Typed/Membership.lean:886`)).
- **Subtyping preservation (`fits-subn`)**: Subtyping in normalized order preserves membership.
  (`fits_subN` (`src/Effect4/Laws/Program/Typed/Membership.lean:1262`)).
- **Normalization compatibility (`fits-normalize`)**: Value membership is invariant under type normalization.
  (`fits_normalize` (`src/Effect4/Laws/Program/Typed/Membership.lean:1156`)).
- **Scope inversion (`fits-scope-inv`)**: Inversion on scope handle values.
  (`fits_scope_inv` (`src/Effect4/Laws/Program/Typed/Membership.lean:896`)).
- **Store safety invariant (`store-safety`)**: Well-typed machine stores produce values that Fit their
  declared types across write operations (seat D5; decisions rows 134, 139 and 181).

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
  explicit compatibility lemmas: `guardBind_typed`, the general form, and its shapes `seqGuard_typed`
  (`onSuccess`), `catchGuard_typed` (`onFailure`), `allGuard_typed` (`all`, `onExit`), `onExit_typed`
  and `seq_typed` (seat D2, `src/Effect4/Laws/Program/Typed/Seq.lean`).
- **Closed Root Requirement Rows (Row 117)**: Admitted programs enforce `rootTy.requires = empty` at load time,
  reflecting rc.112's `runPromise` contract (`Effect.ts:17494-17497`).

#### 3. Project Definition and Judgment
Residual programs resulting from elaboration are typed by `Effect4.Program.Typed.TypedProg`:
```lean
inductive TypedProg (root : ProgramSource) : World → EffTy → RProgram → Prop
```
(`src/Effect4/Laws/Program/Typed/Residual.lean:266`). Operation clauses require certificate validation and enforce that
continuations type for all permitted replies at later worlds. Dedicated typing arms govern control
bracket markers: `.guard`, `.unguard`, `.finishFinalizer`, and `.scopeExit`.

#### 4. Required Properties and Obligations
- **Sequence compatibility (`seq-typed`)**: Compatibility lemma for sequence composition.
  `TypedProg root w mid a → (∀ w', w.leHost w' → ∀ v, Fits w' v mid.answer → TypedProg root w' ty (k v)) → mid.error = ty.error → TypedProg root w ty ((guardR .onSuccess a).bind (seqR k))`
  (`seq_typed` (`src/Effect4/Laws/Program/Typed/Seq.lean:153`)).
- **Close invariance (`close-typed`)**: Invariance of `TypedProg` under closing `unguard` markers
  (`close_typed` (`src/Effect4/Laws/Program/Typed/Seq.lean:49`)).
- **Bind refutation (`bind-closed`)**: Refutation of unrestricted bind closure
  (`typedProg_not_bind_closed` (`Test/Program/TypedProgBindRed.lean:32`), register row `E4-TYPED-CE-030`).
- **Fundamental elaboration property (`denote-typed`)**: Denotation of a checked program is `TypedProg`.
  `typeOfProgram root.sig root.prog = some ty → TypedProg root w ty (denoteR root)`
  (`denoteR_typed` (`src/Effect4/Laws/Program/Typed/Assembly.lean:1669`)).
- **Failure handler compatibility (`on-failure-typed`)**: Compatibility lemma for the error recovery bracket `onFailure` (decisions row 148), proved by
  `catchGuard_typed` (`src/Effect4/Laws/Program/Typed/Seq.lean:123`).
- **M5 on the layer-free fragment (`denote-typed-layer-free`)**: every arm of `denoteR` but the layer
  family's is proved, and the arms are assembled by induction on fuel (`childDenotes_upto`
  (`src/Effect4/Laws/Program/Typed/Denotation.lean:3025`)): at no fuel the frontier, at positive fuel
  each constructor's arm with its children's hypotheses taken at the children's nodes. The layer
  family's arm enters as the hypothesis `ProvideLayerArm`
  (`src/Effect4/Laws/Program/Typed/Denotation.lean:3014`), so `denotesTyped_of_provideLayer`
  (`src/Effect4/Laws/Program/Typed/Assembly.lean:1221`) is conditional and does not close
  `denoteR_typed`; the remaining arm is the open goal `denoteR_typed_provideLayer`
  (`src/Effect4/Laws/Program/Typed/Assembly.lean:1680`, decisions row 176 (b)). On programs no node of
  which is a `provideLayer` (`LayerFree`, `src/Effect4/Laws/Program/Typed/Denotation.lean:3074`) the arm
  cannot be reached (`provideLayerArm_of_layerFree`), so M5 holds there unconditionally:
  `denotesTyped_of_layerFree` (`src/Effect4/Laws/Program/Typed/Assembly.lean:1229`). The store-row arm
  is the textbook's reference-read argument in its adapted form (TAPL §13.4's store typing; PLF
  `References.v`'s `store_weakening`): membership in the cell type exposes a declaration
  (`fits_refTy_inv`, `src/Effect4/Laws/Program/Typed/Denotation.lean:2161`) at a type equivalent to
  `nat` under normalized subtyping, not syntactic equality; `leHost` keeps the declaration; the reply's
  lookup identifies it, and `fits_subN` transports the reply (`refRead_nat`,
  `src/Effect4/Laws/Program/Typed/Denotation.lean:2213`), consumed by `syncRow_typed`
  (`src/Effect4/Laws/Program/Typed/Denotation.lean:2224`) and `perform_arm`
  (`src/Effect4/Laws/Program/Typed/Denotation.lean:2671`). The service arm keeps the source/world
  service-table agreement as a premise and admits the missing-service defect, which is not a service
  value (`service_arm`, `src/Effect4/Laws/Program/Typed/Denotation.lean:2758`); `exit` covers its inline
  branch through `inlineYield_typed` (`src/Effect4/Laws/Program/Typed/Denotation.lean:2859`).
  The load connector needs only the fundamental property: typed root code is never a race
  registration marker, so `loadsTyped_of_denotesTyped_typed`
  (`src/Effect4/Laws/Program/Typed/Commands/Finish.lean:48`) discharges the marker premise, and a
  checked layer-free program loads into `J` (`loadsTyped_of_layerFree`,
  `src/Effect4/Laws/Program/Typed/Commands/Finish.lean:68`).

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
(`src/Effect4/Machine/Scope.lean:750`). A scope transitions from `openEmpty` or `openMap` to `closed exit`. Scope presence
in the typed world is governed by `ScopeLive w sc` (World.lean (`src/Effect4/Laws/Program/Typed/World.lean`)), witnessed by `fits_scope_inv`.

#### 4. Required Properties and Obligations
- **Close idempotence (`close-idempotent`)**: Closing an already closed scope is a no-op.
  (`close_idempotent` (`src/Effect4/Machine/Scope.lean:950`)).
- **Consecutive close idempotence (`close-twice`)**: Applying close twice produces void.
  (`close_twice` (`src/Effect4/Machine/Scope.lean:960`)).
- **LIFO execution order (`close-order-eq`)**: Finalizers run in reverse registration order.
  (`closeOrder_eq` (`src/Effect4/Machine/Scope.lean:978`)).
- **Re-entrant addition semantics (`close-reentrant-add`)**: Adding to closed scope executes immediately.
  (`close_reentrant_add` (`src/Effect4/Machine/Scope.lean:969`)).
- **Close iterator protocol (`close-seq-protocol`)**: Close walk satisfies iterator protocol for clean finalizers
  (`closeSeq_protocol` (`Test/Program/ProtocolPosts.lean:970`)).
- **Scope validity under nesting (`scope-validity-open`)**: General scope validity under dynamic parent-child nesting
  (D4 hand-back, row 156).

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
(`src/Effect4/Machine/Fibers.lean:438`). Machine type safety is maintained by the configuration invariant `MachineTyped root rootTy w m`
(`src/Effect4/Laws/Program/Typed/Assembly.lean:251`).

#### 4. Required Properties and Obligations
- **Invariant non-halted consequence (`machine-typed-not-halted`)**: A halted machine cannot satisfy `MachineTyped`.
  (`machineTyped_not_halted` (`src/Effect4/Laws/Program/Typed/Assembly.lean:311`)).
- **Finite queue fairness (`flush-fair`)**: Callback entry within rounds bound.
  `m.armed.Nodup → FlushReady interp fuel m.armed.length m = true → m.armed.length ≤ rounds → ∀ owner ∈ m.armed, FiredWithin interp fuel rounds m owner = true`
  (`flush_fair` (`src/Effect4/Laws/Machine/Scheduling.lean:413`)).
- **Step invariant lifting (`drivestate-lift`)**: Step invariant lifting for sequential command loops
  (`driveState_lift` (`src/Effect4/Laws/Machine/Lift.lean:56`)).
- **Scheduler step preservation (`step-loop-preserves`, `step-deliver-preserves`)**: Preservation of `MachineTyped`
  across `stepDecision` on loop and deliver decisions (`M6Ledger.step_loop` (`src/Effect4/Laws/Program/Typed/Assembly.lean:1708`), `M6Ledger.step_deliver` (`src/Effect4/Laws/Program/Typed/Assembly.lean:1719`)).
- **Operational progress (`scheduler-progress`)**: Every typed state is either terminal, takes a step, or is at a live frontier
  (decisions row 139).
- **Infinite liveness (`fair-scheduling`)**: Temporal liveness under weak fairness (Requirement R12).

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
(`src/Effect4/Laws/Schema/Codec.lean:1052`, `src/Effect4/Schema/Bridge.lean:492`).

#### 4. Required Properties and Obligations
- **Exactness modulo key sorting (`decode-iff`)**: JSON decoding is exact modulo `normJ`
  (`decode_iff` (`src/Effect4/Laws/Schema/Codec.lean:1052`)).
- **Retraction on canonical values (`decode-encode`)**: Decoding an encoded canonical value recovers it
  (`decode_encode` (`src/Effect4/Laws/Schema/Codec.lean:1065`)).
- **Schema exactness modulo nine keys (`of-schema-exact`)**: Schema decoding is exact modulo `normS`
  (`ofSchema_exact` (`src/Effect4/Schema/Bridge.lean:492`)).
- **Schema retraction (`of-schema-schema`)**: Inverting schema representations on reserved-free types
  (`ofSchema_schema` (`src/Effect4/Schema/Bridge.lean:412`)).
- **Record layout codecs (`record-codec-layout`)**: Exact codec representation for positional record layouts
  (decisions row 165, Data-Wave W5).

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
(`src/Effect4/Laws/Program/TypeAlgebra.lean:1067`). Canonical types `CTy` form a bounded join-semilattice.

#### 4. Required Properties and Obligations
- **Reflexivity (`subn-refl`)**: Normalized subtyping is reflexive.
  (`subN_refl` (`src/Effect4/Laws/Program/TypeAlgebra.lean:1069`)).
- **Transitivity (`subn-trans`)**: Normalized subtyping is transitive.
  (`subN_trans` (`src/Effect4/Laws/Program/TypeAlgebra.lean:1071`)).
- **Equivalence characterization (`subn-equiv-iff`)**: Subtyping equivalence coincides with normal-form equality
  (`subN_equiv_iff` (`src/Effect4/Laws/Program/TypeAlgebra.lean:1088`)).
- **Normalization idempotence (`normalize-idem`)**: Normalization is idempotent.
  (`normalize_idem` (`src/Effect4/Laws/Program/TypeAlgebra.lean:1081`)).
- **Antisymmetry on canonical types (`sub-antisymm-canonical`)**: `subN` is antisymmetric on canonical representatives.
  (`sub_antisymm_canonical` (`src/Effect4/Laws/Program/TypeAlgebra.lean:1035`)).
- **Record and application subtyping (`record-app-subtyping`)**: Subtyping, join, and normalization laws for record and app constructors
  (decisions row 119, Data-Wave W2/W4).

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
(`src/Effect4/Program/Fold.lean:1270`, `src/Effect4/Program/Admission.lean:79`).

#### 4. Required Properties and Obligations
- **Uniqueness of catamorphism (`hom-eq-cata-eff`)**: Any algebra homomorphism out of `Eff` is pointwise equal to `cata_eff`
  (`hom_eq_cata_eff` (`src/Effect4/Program/Fold.lean:1270`)).
- **Inhabitation characterization (`inhabited-iff-fits`)**: Syntactic `inhabited` fold characterizes semantic non-emptiness in `Fits`.
  (`inhabited_iff_fits` (`src/Effect4/Laws/Program/Typed/Membership.lean:2614`)).
- **Fold congruence (`cata-eff-congr-on`)**: Fold congruence over agreeing algebra implementations
  (`cata_eff_congr_on` (`src/Effect4/Laws/Program/Signature.lean:518`)).
- **Traversal census maintenance**: 100% fold coverage enforced by `#traversal_census`.

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
(`src/Effect4/Machine/Context.lean:76`). Layer composition and capability discharge are governed by `LayerTy`
(`src/Effect4/Program/Provision.lean:87`).

#### 4. Required Properties and Obligations
- **Empty requirement satisfaction (`satisfies-empty`)**: Empty requirements are unconditionally satisfied.
  (`satisfies_empty` (`src/Effect4/Machine/Context.lean:149`)).
- **Single requirement lookup (`satisfies-single`)**: Singleton requirements check key membership.
  (`satisfies_single` (`src/Effect4/Machine/Context.lean:153`)).
- **Union requirement splitting (`satisfies-union`)**: Union requirements split into conjunction.
  (`satisfies_union` (`src/Effect4/Machine/Context.lean:164`)).
- **Weakening monotonicity (`satisfies-weaken`)**: Monotonicity under context extension.
  (`satisfies_weaken` (`src/Effect4/Machine/Context.lean:176`)).
- **Service capability discharge (`provide-discharges`)**: Layer provision discharges output capabilities.
  (`provide_discharges` (`src/Effect4/Program/Provision.lean:87`)).
- **Closed layer composition (`provide-closed`)**: Composing closed layers yields closed requirements.
  (`provide_closed` (`src/Effect4/Program/Provision.lean:99`)).
- **Layer sharing invariants (`layer-sharing-contract`)**: Dynamic layer memoization and sharing invariants
  (`LayerSharingContract.lean`).

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
(`src/Effect4/Api/HostProtocol.lean:48`). External answers are submitted through `HostSession.submit` and applied via `HostSession.answer`.

#### 4. Required Properties and Obligations
- **Allowed answer step (`allows-answer`)**: Async answering is an allowed transition from `.awaitingAsync`.
  (`allows_answer` (`src/Effect4/Laws/Run.lean:289`)).
- **Host reply commutativity (`reply-commute`)**: Independent host answers commute in session queues.
  (`reply_commute` (`src/Effect4/Laws/Api/HostSession.lean:112`)).
- **Frontier awaitHost inversion (`frontier-awaithost`)**: Machine awaitingAsync state matches frontier reason.
  characterization of frontier state matching `.awaitingAsync` (`observe_awaitingAsync_iff` (`src/Effect4/Laws/Api/Frontier.lean:40`)).
- **External host progress (`host-progress`)**: External driver progress assumed under `docs/core/host-boundary.md`.
- **Typed replay under session (`typed-replay-session`)**: Public typed replay route under keyed host session
  (decisions row 98).

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
(`src/Effect4/Laws/Program/Agreement/Machine.lean:1922`, `src/Effect4/Laws/Program/Typed/Assembly.lean:1478`).

#### 4. Required Properties and Obligations
- **Straight program agreement (`run-eq-meaning`)**: Frame machine execution matches denotational meaning on `Straight`.
  (`run_eq_meaning` (`src/Effect4/Laws/Program/Agreement/Machine.lean:1922`)).
- **Loop agreement (`loop-agreement`)**: Replay agreement holds across straight loop steps
  (`loopAgreement_of_straight` (`src/Effect4/Laws/Program/LoopAgreement.lean:42`)).
- **Reference machine simulation (`run-eq-ref`)**: Frame machine replay matches term reference replay at empty host table
  (`run_eq_ref` (`src/Effect4/Laws/Program/RuntimeR.lean:211`)).
- **M7 conditional route (`m7-route`)**: Derivation of M7 capstone conditionally from M5 and M6 ledger components
  (`m7_of_ledger` (`src/Effect4/Laws/Program/Typed/Assembly.lean:1612`)).
- **Capstone M7 goals (`m7-capstone-goals`)**: Exit value agreement, final store agreement, non-halting, and exit handle
  validity on `M7Fragment` (`M7.exits_typed` (`src/Effect4/Laws/Program/Typed/Assembly.lean:1814`)).

## 3. The Object-Language Glossary (Object-Language vs. Host Metatheory)

A frequent point of confusion is that words used to describe Effect4 object-language concepts
("syntax", "elaborate", "print", "read") are identical to names in Lean 4's metaprogramming framework.
The table below disambiguates each term, giving its object-language denotation, its in-tree type
and file location, its Lean 4 metaprogramming counterpart, and whether the two denote the same concept.

| Our Word | What It Denotes Here | Our Type and File:Line | Lean's Layer with Same Word | Same Thing or Not? |
|---|---|---|---|---|
| **syntax** | First-order free objects representing abstract syntax trees: programs, types, terms, values, representations. | `Eff Op` (`src/Effect4/Program/Eff.lean:28`), `Ty` (`src/Effect4/Program/Ty.lean:37`), `Term` (`src/Effect4/Machine/Term.lean:100`), `Store.Val` (`src/Effect4/Machine/Value.lean:24`), `Representation` (`src/Effect4/Schema/Bridge.lean:56`). | `Lean.Syntax` (host concrete syntax tree produced by Lean's parser). | **No.** Lean's `Syntax` is host syntax for source code, used only by our authoring macros and custom commands. Our syntax types are first-order data structures. |
| **elaborate** *(Sense 1: Lean)* | Translation of Lean host syntax into Lean core expressions. | N/A (Lean metaprogramming framework). | `Lean.Elab.TermElabM`, `Lean.Elab.CommandElabM`. | **Host only.** Standard Lean compilation pass. |
| **elaborate** *(Sense 2: Authoring)* | Desugaring the authoring surface DSL into `Eff` programs; total by refusal. | `elaborate` (`src/Effect4/Program/Authoring.lean:307`), `elaborateModule` (`src/Effect4/Program/Authoring.lean:386`). Signature: `Src Op → Except Refusal (Eff Op)`. | `Lean.Elab.Term.elabTerm`. | **No.** Our authoring elaboration is an AST-to-AST desugaring returning `Except Refusal`, entirely independent of Lean `Expr`. *(Proposed distinct word: `surfaceElaborate` or `ingest`)*. |
| **elaborate** *(Sense 3: Hefty)* | Lowering scoped syntax into first-order residual operations with bracket markers (`denoteR`). | `denoteR` (`src/Effect4/Laws/Program/DenoteR.lean:799`). Signature: `NativeEff → NativeEff → Point → RProgram`. | None (analogous to compiler lowering / desugaring passes). | **No.** It is a denotational translation from `Eff` to `RProgram` (system map §9 line 284). *(Proposed distinct word: `residualize` or `denote`)*. |
| **print** | Emitting formatted target text from first-order AST data. Invertible on its domain. | `printT` (`src/Effect4/Codegen/Templates.lean:438`), `printModule` (`src/Effect4/Codegen/Print.lean:142`). | `Lean.PrettyPrinter.ppCategory`, `Lean.Widget.InteractiveCode`. | **No.** Our `print` is part of a verified partial isomorphism with `read` (Rendel–Ostermann). Lean's `pp` is a best-effort display formatter without retraction laws. |
| **read** | Parsing target text back into first-order program ASTs. | `readEff` (`src/Effect4/Codegen/Read.lean:736`), `readModule` (`src/Effect4/Codegen/Read.lean:758`). Signature: `String → Except ReadRefusal Module`. | `Lean.Parser.runParserCategory`. | **No.** Our `read` is an exact retraction of `print` on the readable domain (`read_print`, `Laws/Codegen/ReadPrint.lean:1904`). |
| **render** | Producing string representations of types and atoms for TypeScript or OCaml. | `Ty.render` (`src/Effect4/Program/Ty.lean:756`), `renderAll` (`tools/Effect4Gen/Atoms.lean:64`). | `Lean.PrettyPrinter.delab`. | **No.** Our `render` is a deterministic catamorphic fold into target string templates. |
| **lift** | Authoring macros that lift host Lean literals/expressions into program constructors. | `eff { ... }` macros (`src/Effect4/Program/Authoring.lean:42`). | `Lean.Macro`, `Lean.MacroM`. | **Yes in implementation, No in semantics.** Implemented using Lean macros, but semantically represents embedding into the initial algebra. |
| **sugar** | High-level syntax convenience forms in the authoring surface (e.g. `let*`, `try*`). | Authoring DSL syntax rules (`src/Effect4/Program/Authoring.lean:80`). | `syntax` and `macro_rules` declarations. | **Yes in implementation.** Concrete syntax sugar expanding into AST constructors. |
| **census** | Meta-command auditing repository-wide completeness against an explicit model. | `#traversal_census` (`src/Effect4/Laws/Auto/Census.lean:32`), `#semantics_census` (`src/Effect4/Laws/Auto/Semantics.lean:45`). | Custom command elab (`Lean.Elab.Command.elabCommand`). | **Tooling only.** Diagnostic commands inspecting Lean's `Environment`. |
| **gate** | Build-time audit ensuring no axioms outside the ceiling `[propext, Quot.sound]`. | `AxiomGate` (`Test/Audit/AxiomGate.lean:376`). | `#print axioms`, kernel verification. | **Verification.** Directly verifies Lean environment axioms across all compiled modules. |

---

## 4. Metatheoretical Bounds & Evidence Summary

1. **Axiom Ceiling**: Every theorem the registry cites is checked by the producer at `[propext,
   Quot.sound]`; the whole-library gate (`Test/Audit/AxiomGate.lean`) holds every declaration
   there too, except the rendering and instrumentation modules it admits by name.
2. **First-Order Data Discipline**: Stored `Eff` syntax is first-order data: its bind continuation
   is another program tree with positional inputs (`src/Effect4/Program/Eff.lean:277`). `RProgram` is the proof-side
   semantic carrier `Effects.Program RSig ExitV`, whose visible operation nodes carry Lean function
   continuations (`vis : Answer op → Program sig A`). Those functions belong to the semantic model
   and are not stored function values in `Eff` or `Val`.
3. **Simulations vs. Equivalence**: Behavioral relationships are stated strictly as equal-observation
   theorems over specified fragments (`Straight`, `Looped`, empty host table `M7Fragment`), never
   as unqualified "equivalence".
4. **Literature Tracking**: Every textbook chapter and academic paper citation is audited against
   vendored copies in `docs/research/2026-10-01-semantics/citations-audit.md`.
