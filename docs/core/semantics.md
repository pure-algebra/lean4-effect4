# Semantics: the language's judgments, their literature and their obligations

The authority for what Effect4's semantic judgments mean, which literature each adopts or adapts,
where the language cuts away from that literature, and which properties each must have. Ten
concepts, each in four parts: what the literature defines; our adaptation, assumptions and
exclusions; the definition and judgment in the tree; the required properties.

What this document does not own, and who does:

- **Status.** Whether a property is proved, wanted, refuted, absent or assumed is measured, never
  written here: `generated/semantics.md` (`make gen-semantics`;
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
child trees, `src/Effect4/Program/Eff.lean`). `RProgram` is the proof-side semantic carrier
`Effects.Program RSig ExitV` (`src/Effect4/Laws/Program/Sched.lean`); visible operations carry
Lean function continuations (`vis : Answer operation → Program signature A`,
`.lake/packages/effects/Effects/Algebra/Program.lean:33–38`). Those functions belong to the semantic
model and are not stored function values in `Eff` or `Val`.

`Fits` is value membership in a world. `TypedProg` is residual program typing: ordinary operation
clauses require certificate permission and typed continuations for permitted replies at later worlds. Its
`unguard` and `finishFinalizer` clauses require an exit payload without a continuation premise.
The scope-exit marker is typed only at the run position of the guard the `scoped` arm installs
(`scopedGuard`, with a live scope and a fitting restored context; decisions row 188 (a)): as current
code the counted step answers it `badShapeExit` (`E4-TYPED-CE-034`). `DenotesTyped` connects admitted
source points to that residual judgment. These definitions resemble protocol-based program logics,
but identifying them with weakest preconditions would require a named execution interpretation and
a stated correspondence. The unrestricted bind counterexample (`E4-TYPED-CE-030`) alone does not
settle every possible weakest-precondition interpretation.

A claim's title, role and selected evidence express an authored interpretation. The printed
proposition states exactly what its theorem proves or its planned goal requests. Checking a theorem
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
an `absent` claim. A planned goal placed at a requirement (`@[semantics "concept" (requirement :=
Rn)]`, decisions row 207) is one of that requirement's nodes; a goal neither placed nor reached is
listed as unplaced. Generated tables own evidence status, propositions,
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

### 1.4 Applying the textbook proof method

TAPL §8.3 splits safety into progress and preservation, here `StepPreserves`; §§13.4–13.5 develop store typing.
The verified [contents](https://www.cis.upenn.edu/~bcpierce/tapl/contents.pdf) locates these sections.
The vendored PLF `References.v` supplies inspectable definitions: `store_weakening`,
`store_well_typed_app`, `preservation` and `progress`.
These are different sources, not interchangeable theorem attributions.

Effect4 applies that proof discipline to its own judgments:

| Proof responsibility | Effect4 meaning and owner | Boundary |
| --- | --- | --- |
| Formation and inversion | Source and checker admission, and `Fits` inversion at the consumer | A shape check alone does not establish declared handle types |
| Environment and binder reasoning | Positional input and capture typing in admission and the denotation | Stored syntax has no lambda values; binders use environment extension and lookup lemmas, not a beta-substitution theorem |
| Store weakening | Existing membership preserved along `World.leHost` | Does not establish validity of new contents or declarations |
| Store operation safety | `StoreImplements` and `storeStep_typed`: an actual answer, an extended world, a typed store and a typed continuation | The configuration invariant also keeps stacks, queues and its other clauses |
| Preservation | `StepPreserves` under `ConfigTyped`, lifted through decisions and reachability | Each added invariant holds at load and at each writer; world monotonicity alone does not suffice |
| Progress | An explicit finished, transition or live-frontier classification | `stuck = none` alone supplies no successor; waiting, missing decisions and exhausted fuel are not errors |
| Subtyping | Membership under normalized `subN`, with handle variance justified by permitted reads and writes | Transports a value along types, not a machine along execution |

This table states responsibilities, not completed claims. Each proof slice records four things:
the cited definition or technique, the local adaptation and cut, the exact proposition, and its caller.
A missing textbook role is an explicit scoped omission or a named obligation.
Assigning every theorem to a chapter does not establish metatheory coverage.

### 1.5 Constructing and explaining the proofs

The inspected TYPES 2003 chapters add methods for organizing proofs. They supply no new Effect4
semantic result. The [source audit](../research/2026-10-01-semantics/types-2003-scout/book-scout.md)
records the edition, checksum, pages and limits of each connection.

Ballarin's *Locales and Locale Expressions in Isabelle/Isar* (§§3.2–3.5, pp. 37–41) explains how
fixed parameters and assumptions stay visible when derived facts are exported. In Lean, the proofs
reuse the existing parameters, predicate bundles and conditional theorems. A constructor arm keeps
point admission, service-table agreement and its child hypotheses explicit. A handler also
establishes the protocol's actual postcondition and the resulting state invariants. Erasing a
shared assumption at a boundary changes the theorem.

Wiedijk's *Formal Proof Sketches* (§§3–4, pp. 383–386; §7, pp. 388–389) motivates a short account
of the essential argument with named justification tasks. Here a sketch is planning prose; the Lean
proposition and its checked evidence remain the authority. A conditional assembly leaves its
parameters open until they are discharged. An explanation names what each lemma enables and does
not reproduce tactic logs.

Adams's *A Modular Hierarchy of Logical Frameworks* (§3.4, pp. 11–12) proves conservativity for the
features of his framework hierarchy. Here it is an analogy for reviewing a change's judgments, rules
and dependencies. It establishes neither `StepPreserves` for a step nor Kripke persistence. Strengthening an
invariant after a counterexample names the changed program admission premise and re-establishes the
affected transitions.

For each slice, the prose records the literature relation, the local adaptation and cuts, the
argument and the consumer. The semantics registry and the generated report own the exact statement and its
evidence status. The [tooling follow-up](../research/2026-10-01-semantics/types-2003-scout/tooling-adoption.md)
records the source-resolution and rendering gaps and two bounded adoption slices. Planned
prerequisites stay distinct from checked theorem applications.

The plan (`tools/ProofGraph/Plan.lean`) holds that distinction mechanically (decisions row 203). A
planned goal (`proof_goal`) states a wanted proposition before its proof exists, as a theorem whose
body is `sorry`. Downstream proofs use it, so a decomposition is an ordinary theorem whose proof
uses goals, in the style of `m7_of_ledger`. The kernel checks it when it is added. A node's status
is read from its proof, with goals as leaves: goal, modulo the goals it rests on, or proved. The
plan section of `generated/semantics.md` renders them per requirement. This is the blueprint
method of formalization projects, with the edges read from proof terms rather than authored.

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
  with explicit partitioned tables for fibers ($\Gamma$), promises ($\Pi$), heap references (`Ρ`, Greek rho, field `w.Ρ`),
  and ghost resume states ($\Theta$).
- **Exclusion of Stored Functions (Row 163)**: Stored `Eff` syntax and stored values `Val` contain
  no function values or closures (`../research/history/language-cut.md` §1). Consequently, `Fits` contains **no arrow clause**
  and recurses over finite type structure. Worlds carry syntactic type declarations. Reference
  membership reads those declarations instead of recursively interpreting stored contents. These
  choices avoid a recursive semantic-store definition here. No-arrow syntax alone would not justify
  excluding step indices from every future extension (Ahmed §2.2.5 and §3.2.3).
- **Accessibility and state validity**: a future world is accessible through `World.leHost`, not
  necessarily reachable by execution. `Fits` is a unary Kripke logical predicate (Ahmed §2.2.5),
  not a binary equivalence between programs. `StoreTyped`, `WorldValid` and the full configuration
  invariant are separate obligations; accessibility alone does not give them. An actual store
  operation produces a suitable extended world, typed contents and the promised reply.
  `StoreImplements` and `storeStep_typed` own that connection (`src/Effect4/Laws/Program/Typed/Adequacy.lean`).
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
- **Monotonicity (`fits-mono`)**: `World.leHost` preserves value membership for a fixed value and type.
  (`fits_mono` (`src/Effect4/Laws/Program/Typed/Membership.lean`)).
- **Subtyping preservation (`fits-subn`)**: Subtyping in normalized order preserves membership.
  (`fits_subN` (`src/Effect4/Laws/Program/Typed/Membership.lean`)).
- **Normalization compatibility (`fits-normalize`)**: Value membership is invariant under type normalization.
  (`fits_normalize` (`src/Effect4/Laws/Program/Typed/Membership.lean`)).
- **Scope inversion (`fits-scope-inv`)**: Inversion on scope handle values.
  (`fits_scope_inv` (`src/Effect4/Laws/Program/Typed/Membership.lean`)).
- **Term-map monotonicity (`term-maps-mono`)**: A read-modify-write row demands that its binder term
  map one type into another (decisions row 43). The map holds at every world later than one where it
  holds. It quantifies over later worlds, so `Fits` gains no arrow clause (row 163).
  (`TermMaps.mono` (`src/Effect4/Laws/Program/Typed/Residual.lean`)).
- **Typed terms map (`term-typed-maps`)**: The term typer admits a binder term at the node's
  environment extended by the cell's type. Over an environment that fits, the term then maps the
  cell's type into its own type, at every later world.
  This is the term relation's fundamental property for the term typer.
  A typed read-modify-write row takes its pre from it (decisions row 43; the state plan's T3b).
  It establishes nothing about a term that the checker refuses.
  (`termMaps_of_typed` (`src/Effect4/Laws/Program/Typed/Denotation.lean`)).
- **The list fold (`fold-typed-atomic-update`)**: A list fold binds its accumulator at the fold's
  level and its element one level above (decisions row 228).
  The claim holds the fold's rules as one statement, `ListFoldRules`.
  The rules are scope, evaluation, failure, weakening, typing, typed evaluation and the two
  equations of the printed leaf.
  A fold that the checker types answers a member of its type, over values that fit, in a fixed
  world.
  One `Ref.modify` whose term the checker types is one store step: it answers `B` and stores `A`.
  It establishes nothing about a module that uses the fold, and no agreement with a target.
  (`fold_typed_atomic_update` (`src/Effect4/Laws/Program/Typed/ListFold.lean`)).
- **The identity of a handle (`handle-identity-laws`)**: `sameHandle` compares two handles of one
  kind by their keys (decisions row 229). It reads no payload, no cell and no world.
  It is total on two members of one handle type, at any payload types.
  It is reflexive and symmetric, and it decides the equality of the two keys.
  A handle that an allocation just made is the same as no handle of a value that fits the earlier
  world. A later world keeps the membership of a list of handles.
  The handles of a term's answer are handles of its environment.
  It establishes no correspondence in a target: that is each target's relation.
  (`handle_identity_laws` (`src/Effect4/Laws/Program/Typed/ListFold.lean`)).
- **The mask's saved state (`saved-mask-image-membership`)**: A mask saves its caller's
  interruptibility at an opaque host type, `Ty.maskRestore`, with a reserved target (decisions
  row 244).
  Its value is the saved bit in one frame of its own, `Val.savedMask`.
  Membership at the type is exactly the two images, in `Fits` and in the shape check `Val.hasTy`.
  An image is no member of `bool`, and a Boolean is no member of the type.
  No subtyping relates the two types.
  No external allocation takes the target, and no service carries it in the first profile.
  The column scan finds it in a host answer column, so table admission refuses that table.
  An image holds no handle, so every world and every store keep its membership.
  It establishes no reply admission.
  (`saved_mask_image_membership` (`src/Effect4/Laws/Program/Typed/Mask.lean`)).
- **Store safety invariant (`store-safety`)**: Well-typed machine stores produce values that Fit their
  declared types across write operations (seat D5; decisions rows 134, 139 and 181).
- **Pool's profile on the model (`pool-profile-closed`, `pool-lease-enrols`)**: Each of the
  five transitions of Pool's abstract model keeps the first profile. The law has no premise
  on a request. An idle item beside enrolled waiters is a state of the profile. A lease enrols its
  request exactly when the pool is open and a lease holds every item. Neither states
  fairness, liveness or anything of a program.
  (`profile_closed`, `lease_enrols_iff` (`src/Effect4/Laws/Modules/Pool/Profile.lean`)).

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
bracket markers: `.guard`, `.unguard`, `.finishFinalizer`, and the `scoped` guard whose run arm is the
scope-exit callback (`.scopedGuard`, decisions row 188 (a)); the saved slot of that guard is
`FrameAccepts.scopedResume`.

#### 4. Required Properties and Obligations
- **Sequence compatibility (`seq-typed`)**: Compatibility lemma for sequence composition.
  `TypedProg root w mid a → (∀ w', w.leHost w' → ∀ v, Fits w' v mid.answer → TypedProg root w' ty (k v)) → mid.error = ty.error → TypedProg root w ty ((guardR .onSuccess a).bind (seqR k))`
  (`seq_typed` (`src/Effect4/Laws/Program/Typed/Seq.lean`)).
- **Close invariance (`close-typed`)**: Invariance of `TypedProg` under closing `unguard` markers
  (`close_typed` (`src/Effect4/Laws/Program/Typed/Seq.lean`)).
- **Bind refutation (`bind-closed`)**: Refutation of unrestricted bind closure
  (`typedProg_not_bind_closed` (`Test/Program/TypedProgBindRed.lean`), register row `E4-TYPED-CE-030`).
- **Fundamental elaboration property (`denote-typed`)**: Denotation of a checked program is `TypedProg`.
  `typeOfProgram root.sig root.prog = some ty → TypedProg root w ty (denoteR root)`
  (`denoteR_typed` (`src/Effect4/Laws/Program/Typed/Assembly.lean`)), proved at every source by
  `denotesTyped` (`src/Effect4/Laws/Program/Typed/LayerArm.lean`); the load
  (`load-typed`) by `loadsTyped` (`src/Effect4/Laws/Program/Typed/LayerArm.lean`), through
  the load connector whose race-marker premise the root code's typing discharges
  (`loadsTyped_of_denotesTyped_typed`, `src/Effect4/Laws/Program/Typed/Commands/Finish.lean`).
  The displayed implication abbreviates the premises of `DenotesTyped`. They are well-formed layer
  references, a world whose service table equals the source's, and an admitted source point whose path selects an effect node.
- **Failure handler compatibility (`on-failure-typed`)**: Compatibility lemma for the error recovery bracket `onFailure` (decisions row 148), proved by
  `catchGuard_typed` (`src/Effect4/Laws/Program/Typed/Seq.lean`).
- **M5 on the layer-free fragment (`denote-typed-layer-free`), and the layer family's arm
  (`provide-layer-arm`)**: every arm of `denoteR` is assembled by induction on fuel
  (`childDenotes_upto` (`src/Effect4/Laws/Program/Typed/Denotation.lean`)): at no fuel the
  frontier, at positive fuel each constructor's arm with its children's hypotheses taken at the
  children's nodes. The layer family's arm enters there as the hypothesis `ProvideLayerArm`
  (`src/Effect4/Laws/Program/Typed/Denotation.lean`), so `denotesTyped_of_provideLayer` (`src/Effect4/Laws/Program/Typed/Assembly.lean`) is conditional;
  on programs no node of which is a `provideLayer` (`LayerFree`, `src/Effect4/Laws/Program/Typed/Denotation.lean`) the arm cannot
  be reached (`denotesTyped_of_layerFree`, `src/Effect4/Laws/Program/Typed/Assembly.lean`). The arm itself is proved at every
  source (`provideLayerArm`, `src/Effect4/Laws/Program/Typed/LayerArm.lean`, decisions rows 176 (b), 185–187;
  `E4-TYPED-CE-023` and `-031` repaired): every `LayerTerm` constructor's build at an admitted layer
  point answers the built context at the layer's checked error type (`layerBuild_typed`,
  `src/Effect4/Laws/Program/Typed/LayerArm.lean`, structural on the term inside an induction on the fuel a reference's hop
  spends; the hop's point typed because expansion fixes checked terms and checking is
  path-independent, `ExpandFix`), a memo hit is typed by the memo-table clause (`memoize_typed`,
  `src/Effect4/Laws/Program/Typed/LayerArm.lean`), a merge's awaited exits either all read back or fail with reasons that fit
  (`mergeContexts_typed`, `src/Effect4/Laws/Program/Typed/LayerArm.lean`), and the protocol around the build is typed
  (`provideLayer_arm`, `src/Effect4/Laws/Program/Typed/LayerArm.lean`). The store-row arm
  is the textbook's reference-read argument in its adapted form (TAPL §13.4's store typing; PLF
  `References.v`'s `store_weakening`): membership in `refOf A` exposes a declaration
  (`fits_refOf_inv`, `src/Effect4/Laws/Program/Typed/Denotation.lean`) at a type equivalent to
  `A` under normalized subtyping, not syntactic equality; `leHost` keeps the declaration; the reply's
  lookup identifies it, and `fits_subN` transports the reply (`refRead`,
  `src/Effect4/Laws/Program/Typed/Denotation.lean`). The `Ref` and `Deferred` rows are templates
  (the state plan's T3a). `syncRow_typed` (`src/Effect4/Laws/Program/Typed/Denotation.lean`)
  reads the node's checked instance off the row's match (`rowTy_fits`). It is consumed by
  `perform_arm`
  (`src/Effect4/Laws/Program/Typed/Denotation.lean`). The service arm keeps the source/world
  service-table agreement as a premise and admits the missing-service defect, which is not a service
  value (`service_arm`, `src/Effect4/Laws/Program/Typed/Denotation.lean`); `exit` covers its inline
  branch through `inlineYield_typed` (`src/Effect4/Laws/Program/Typed/Denotation.lean`).
  The load connector needs only the fundamental property: typed root code is never a race
  registration marker, so `loadsTyped_of_denotesTyped_typed`
  (`src/Effect4/Laws/Program/Typed/Commands/Finish.lean`) discharges the marker premise, and a
  checked layer-free program loads into `J` (`loadsTyped_of_layerFree`,
  `src/Effect4/Laws/Program/Typed/Commands/Finish.lean`).
- **The restore site's body (`scoped-body-substitution-boundary`)**: The mask adds no scoped
  constructor (decisions rows 245 and 246).
  A restore site is one node that binds nothing, and its checked body is child 0.
  Both saved choices run that one body in the node's environment.
  A false bit is the body's own code, and a true bit is `interruptible` over it.
  At a typed point the saved term evaluates to an image, and the node denotes a typed program.
  The body's point is typed at the node's type.
  A saved value that a program passes as data keeps its choice and holds no handle.
  The claim's other half, a later constructor that binds a scope, has no statement.
  It establishes no agreement with a target.
  (`scoped_body_substitution_boundary` (`src/Effect4/Laws/Program/Typed/Mask.lean`)).

The `sound-at-app-signature` claim carries `meaning_typed`, `run_typed` and `meaningB_typed` to an application's signature: any table, service declarations at fresh codes (`src/Effect4/Laws/Program/SoundAnySignature.lean`). A looped program is a program of the built-in signature, so C3's reflection (`effTy_restrict`) transfers its typing.

The `straight-meaning-typed` claim requires `Straight e = true` and successful native program typing in the empty environment.
`Denote.meaning_typed` establishes `ExitHasTy` at the resulting stores, starting from empty stores.
Its declaration lives in `src/Effect4/Laws/Program/MeaningSound.lean`.
`Denote.sound` keeps the typed state's invariant: the environment fits at a world, and the store fits (`Denote.StoreFits`, decisions row 209).
A value that fits is valid in a store whose cell columns are typed (`CellsTyped.fits_validIn`, `src/Effect4/Laws/Program/Typed/Adequacy.lean`).
It establishes no scheduled-program liveness or external host execution property.

The `instantiated-formation` claim requires actual row use to check map keys and a deferred's error column after substitution.
It serves `rowTy` and M5 under decision row 193.
It establishes no host reply admission or liveness property.

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
  (`close_idempotent` (`src/Effect4/Machine/Scope.lean`)).
- **Consecutive close idempotence (`close-twice`)**: Applying close twice produces void.
  (`close_twice` (`src/Effect4/Machine/Scope.lean`)).
- **LIFO execution order (`close-order-eq`)**: Finalizers run in reverse registration order.
  (`closeOrder_eq` (`src/Effect4/Machine/Scope.lean`)).
- **Re-entrant addition semantics (`close-reentrant-add`)**: Adding to closed scope executes immediately.
  (`close_reentrant_add` (`src/Effect4/Machine/Scope.lean`)).
- **Close iterator protocol (`close-seq-protocol`)**: Close walk satisfies iterator protocol for clean finalizers
  (`closeSeq_protocol` (`Test/Program/ProtocolPosts.lean`)).
- **The mask's flag at the boundaries of regions (`saved-mask-restoration`)**: The claim holds
  the mask's law as one statement, `MaskRestoration`.
  The statement has five parts (decisions rows 227 and 244 to 246).
  Each part is a step of the frame machine or a pass of a saved frame.
  The getter masks the fiber and answers the image of the flag at its entry.
  A restore site at a true bit is the `interruptible` region over its body.
  At a false bit it is its body's own code, so it leaves the flag as it is.
  A region's entry sets its own flag at every fiber.
  It saves the earlier flag in a frame exactly when it changes the flag.
  That frame's pass returns the flag on every exit.
  With a cause pending, an exit that leaves the fiber interruptible fails there with that cause.
  It states nothing for a region that changes no flag, and nothing about a module.
  It establishes no progress.
  (`saved_mask_restoration` (`src/Effect4/Laws/Program/Typed/Mask.lean`)).
- **The saved mask's chain through a pop (`saved-mask-pop-discipline`)**: At one fixed base
  bit, the restoring frames of a fiber's stack alternate from the negation of the flag
  (`MaskChain`). The frame machine's pop keeps the chain, from an empty scratch stack.
  `getCont`, the finished frame's path and the entry of each region keep it too. Two fibers
  with one base and one stack have one flag. It is a local law of the frame machine. It
  states no law of a run, no completed exit and no bracket of a region.
  (`saved_mask_pop_discipline` (`src/Effect4/Laws/Machine/MaskDiscipline.lean`)).
- **The saved mask's chain at every live fiber of a run (`saved-mask-chain-runs`)**: The
  machine holds one table of start flags. Each live fiber holds the chain at its own flag of
  the table (`MaskRuns`). Each command keeps the invariant under one condition: just before a
  command clears a fiber, that fiber has exited, or its stack is empty, or its flag is its
  base. The command loop discharges the condition, so every decision, tape and fuel keeps the
  invariant. The claim's pointer states it at the compiled program's interpreter
  (`compiled_mask_chain_runs` (`src/Effect4/Laws/Program/MaskRuns.lean`)). Its general form is
  at the frame evaluator (`saved_mask_chain_runs`
  (`src/Effect4/Laws/Machine/MaskRuns.lean`)). Each entry of the program interface that
  returns a machine holds it with no premise (`src/Effect4/Laws/Api/MaskRuns.lean`). Along a
  run, a live fiber's flag is a function of its stack (`MaskRuns.flag_eq`). It states no
  bracket of a region: that a body's run returns to the entry's stack stays open. It states
  nothing of an exited fiber, of cleanup, of delivery or of progress.
- **Scope validity under nesting (`scope-validity-open`)**: General scope validity under dynamic parent-child nesting
  (D4 hand-back, row 156).
- **Pool's return and close on the model (`pool-return-front`, `pool-return-once`,
  `pool-close-refuses`)**: A return of a lease that holds its item puts the item at the front
  of the idle items and keeps every item. The lease then holds nothing (`giveBack_front`). A
  second return of that lease changes nothing (`giveBack_once`). After the close's first
  step every lease is refused (`close_refuses`). They state no finalizer's run and no close
  that waits. The three theorems are in `src/Effect4/Laws/Modules/Pool/Profile.lean`.

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
- **Exclusions (Rows 106, 107, 134, 188, 189)**: Unbounded tokens are excluded by `GuardState.keysBelow` in `QueueOk` (Row 106).
  Defect-bearing exits are excluded by `NoShapeDefect` (Row 107). Timer and race columns are separated in configuration typing;
  queued enrollment children are bounded below `nextId` (`EnrollRaceOk`, row 134 (e), `E4-TYPED-CE-032`).
  Administrative markers are excluded from ordinary program typing: the raw `scopeExit` marker remains in the semantic carrier
  but is excluded by `TypedProg`, admitting the callback only at the `scoped` guard's run position and saved slot (`scopedGuard`, `scopedResume`,
  row 188 (a), `E4-TYPED-CE-034`); registration callbacks under injected yields are admitted by the host-stack judgment as correlated arrows
  carrying race existence and token typing (`HostStack`, `PositionStack`, row 188 (b), `E4-TYPED-CE-033`).
  Queued observe sources are bounded below `nextId` (`QueueOk.observer`, `HeadOk.observer`, row 189, `E4-TYPED-CE-035`) to prevent vacuous
  antitone $\Gamma$-reads admitting unallocated future fibers.

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
  (`machineTyped_not_halted` (`src/Effect4/Laws/Program/Typed/Assembly.lean`)).
- **Finite queue fairness (`flush-fair`)**: Callback entry within rounds bound.
  `m.armed.Nodup → FlushReady interp fuel m.armed.length m = true → m.armed.length ≤ rounds → ∀ owner ∈ m.armed, FiredWithin interp fuel rounds m owner = true`
  (`flush_fair` (`src/Effect4/Laws/Machine/Scheduling.lean`)).
- **Finite fair-tape endpoint (`fair-tape-drains-armed`)**: A fair finite tape that suffices leaves
  no armed owner at its live end.
  `FairTape interp fuel m tape → Suffices interp fuel tape m = true → (replayEval interp fuel tape m).machine.stuck = none → (replayEval interp fuel tape m).machine.armed = []`
  (`fairTape_unarmed` (`src/Effect4/Laws/Machine/Scheduling.lean`)). It is the finite half of R12.
  It says nothing about infinite tapes, termination or host progress. `flush_fair` permits
  rearming, so it is not general scheduler fairness.
- **Frontier names work (`frontier-names-work`)**: At a live, unfinished machine whose tape ran
  out, the frontier is empty exactly at a deadlock: no runnable fiber, no armed owner, no host
  request, no timer and no compile budget.
  `m.stuck = none → m.finished = false → (frontierReasons .tape m = [] ↔ Deadlocked m)`
  (`frontier_empty_iff_deadlocked` (`src/Effect4/Laws/Api/Frontier.lean`)). It is R12-b, the
  frontier half of `scheduler-progress`'s classification. It says nothing about what a decision
  does at a deadlock, about progress or about infinite tapes.
- **Decision preservation (`decision-keeps-typed`)**: One tape decision keeps `J` when its host
  answer, if any, is admitted (`decision_preserves`
  (`src/Effect4/Laws/Program/Typed/Commands/Clauses/All.lean`)). It is a premise node of M7's
  plan edge.
- **Step invariant lifting (`drivestate-lift`)**: Step invariant lifting for sequential command loops
  (`driveState_lift` (`src/Effect4/Laws/Machine/Lift.lean`)).
- **Scheduler step preservation (`step-loop-preserves`, `step-deliver-preserves`)**: Preservation of `ConfigTyped`
  across the actual `driveStep` command at an extending world (`StepPreserves`, `loop_preserves`,
  `deliver_preserves` in `src/Effect4/Laws/Program/Typed/Assembly.lean`). The later decision
  and reachability statements use `MachineTyped`; they are distinct assembly goals.
- **Operational progress (`scheduler-progress`)**: Every typed state is either terminal, takes a step, or is at a live frontier
  (decisions row 139).
- **Infinite liveness (`fair-scheduling`)**: Temporal liveness under weak fairness (Requirement R12).
- **The Queue model's run invariant on the first profile (`queue-first-step-invariant`,
  `queue-first-run-flags`)**: One step of a first operation keeps the run invariant
  `FirstRunInv`: the profile, the buffer's bound, `tidy`, `quiet`, and the run's two flags.
  So both flags hold after every list of first operations from the empty queue of a positive
  capacity. It is the model's half of `wait-registration-no-gap` and of
  `waiting-request-obligation-preserved`. It states nothing of a program, of a signal's
  delivery or of liveness.
  (`first_step_inv`, `first_run_flags` (`src/Effect4/Laws/Modules/Queue/Invariant.lean`)).
- **Pool's wake selection on the model (`pool-select-takes-first`)**: One selection takes the
  first waiters of the state that it finds, at most its count, and it changes the waiters
  alone. It is one selection: it states no run and no liveness.
  (`select_takes_first` (`src/Effect4/Laws/Modules/Pool/Profile.lean`)).

#### 5. How the scheduler proofs use the theory

The proof structure is induction on executions: establish the loaded configuration, prove each
command and decision case, then assemble reachability. This follows the invariant method in
Lynch and Vaandrager, *Forward and Backward Simulations I*, §6 (audit C4), rather than inferring
whole-machine typing from isolated command tests. `decisionKeeps_of_steps` and
`typedState_reachable_of_steps` expose the remaining premises; their formal consumers are
`decision_preserves` and `typedState_reachable`.

Within a command, two smaller arguments meet. `configTyped_frame` transports clauses across a
store edit under its explicit unchanged-view, typing, key and due-owner hypotheses.
`completionStrong_await` moves a completed Deferred's answer and error evidence to a declared
waiter type. `wake_preserves` uses both arguments at the actual machine step, and supplies
`wake_preserves`'s checked witness. The analogy to the frame rule and protocol subsumption in
de Vilhena and Pottier, *A Separation Logic for Effect Handlers*, §3.3 and §4.2.4 (audit P8), guides
this decomposition. Our ordinary Lean predicates do not implement that paper's Iris resource
algebra or separation logic; the displayed theorem premises are the local contract.

Registration completion adds a pending record at one race key. `ObsViewOff` and
`configTyped_rupdate_park` permit that one lookup change while transporting countdown
correlations at other keys. Decisions row 134(d) supplies the stored and queued observer
exclusions. `registrationDone_preserves` combines this transport, race payload typing and
cancellation-frame typing for the accepted, deferred-interrupt and ordinary park branches.
It supplies the unchanged `registrationDone_preserves` goal; the CE-028 battery separately
checks refusal of the historical countdown collision and acceptance after removing only that
countdown. The [receipt](../research/2026-10-02-codex-lead/registration-receipt.md) records each
helper's concrete consumer. This remains a local invariant proof, with the same limits as above.

The machine generates two internal administrative markers during execution that are not user-space programs, and the typing invariant places each strictly where the operational semantics expects it (decisions row 188):
1. **Scope-Exit Callbacks (`E4-TYPED-CE-034`)**: When a `.scoped` block executes, it creates a scope-exit callback to close the scope and restore the surrounding context. The raw `scopeExit` marker remains in the semantic program carrier, but ordinary `TypedProg` admission excludes it. The scope callback is admitted at the `scoped` guard's run position and saved slot (`scopedGuard`, `scopedResume`). This repairs the typing contract around the evaluator's explicit `badShapeExit` fallback (`evaluateFiberR`); it does not remove syntax or prove general loop/delivery preservation. The evaluation walk yields the `CallbackSaved` alternative of `WalkTyped`, which `prepareScopedExitR` consumes directly.
2. **Race Registration Callbacks under Injected Yields (`E4-TYPED-CE-033`)**: When `beginRace` sets up a race, budget preemption (`injectYield`) can save the registration marker inside a success continuation on the stack. The host-stack judgment composes ordinary frames and registration arrows that carry race existence, the matching host and token typing. It admits the injected-callback shapes while requiring those correlations. Preservation by the actual injected yield and subsequent walk remains part of the open loop/delivery proofs.

All saved-stack judgments are factored through a unified typed-path relation (`Contracts.FramePath Edge`, decisions row 48):
- `Contracts.FramePath Edge` is a Prop-valued typed-path relation over frame lists, interpreting composition through existential middle types.
- It provides generic identity (`nil`), append (`append`), splitting (`split`), and transport along edge implications (`map`).
- `HostStack` and `PositionStack` instantiate it over `HostEdge` and `PositionEdge` respectively.
- The unchanged `StackAccepts` is connected by the two conversion theorems (`framePath_of_stackAccepts`, `stackAccepts_of_framePath`).
- Conversions (`positionStack_of_host`, `hostStack_of_stackAccepts`) and Kripke-monotonicity transports (`hostStack_mono`, `positionStack_mono`) are derived as single functorial edge maps (`FramePath.map`).


Queued command arguments are bounded below `nextId` wherever an antitone declaration reading would otherwise admit unallocated future fibers (decisions rows 134 (e) and 189). In particular, `RCmdOk`'s `observe` arm reads the static fiber environment $\Gamma$ antitonically:
$$\forall ty,\; \Gamma(\text{source}) = \text{some } ty \implies \text{ExitOk } ty \text{ exit}$$
If a queued command names an unallocated fiber ID, this premise is satisfied vacuously. When `launch` subsequently allocates that ID below the race's column, the retained exit can violate the child's declared type (`E4-TYPED-CE-035`). Requiring `source.value < m.nextId` in `QueueOk.observer` and `HeadOk.observer` closes this gap, mirroring the enrollment bound for race children (`EnrollRaceOk`).


In particular, token bounds, disjointness from external requests, and race/observer separation
are different properties. They do not state that every internal key occurs at most once, nor
that a reply will eventually arrive. A “sender transfer” is explanatory language for a checked
implication between two typing demands. Unique ownership, at-most-once delivery and liveness
require their own stated invariants or operational theorems. The CE-026 battery checks the old
wrong-column witness is refused and the corrected wake is typed; its repeated-wake equation is
a finite control, not a general exclusivity theorem.

The generated feature view selects all M6 command goals and the actual frame, transfer and
assembly declarations. Its proof-reference arrows come from Lean expressions; its authored
prerequisite arrows explain the intended assembly. The TYPES 2003 basis—Adams's feature
structure, Ballarin's preservation of context assumptions, and Wiedijk's significant proof
steps—is documented in the [proof-view method](../research/2026-10-02-proof-feature-graph/method.md).
Neither kind of arrow proves an open goal. Full statements, hypotheses, literature associations
and checked/wanted evidence remain available through the existing report and architecture page.

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
  `title`, `description`, `documentation`, `examples`, `default`, `message`, `expected`, `arbitrary`:
  `Schema.Bridge.erasedKeys`).
  Arbitrary metadata (`effect4/*`) is **not** unconditionally erased.
- **Pinned Limitation (`E4-SCHEMA-CE-059`)**: Overlapping JSON images can defeat unchecked left-biased
  recovery. The public encoder (`Schema.encode`) refuses those values, so every successful encoding still
  round-trips (`decode_of_encode`, at every type), and `decode_iff` stays exact modulo `normJ`.
- **Records (rows 119, 165)**: a record value carries its canonical field names (row 165 (a), ruled). The
  Schema bridge, which describes record types, refuses `record` by name, and the JSON codec, which
  encodes record values, has no record arm yet, so record codecs (`record-codec-layout`) are open.

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
  (`decode_iff` (`src/Effect4/Laws/Schema/Codec.lean`)).
- **Retraction on codec-admitted values (`decode-encode`)**: at a canonical type (`CTy`), decoding the
  encoding of a value that passes the shape check and is codec-admitted (`Ty.isCodecValue`) recovers it
  (`decode_encode`, `src/Effect4/Laws/Schema/Codec.lean`).
- **Schema exactness modulo nine keys (`of-schema-exact`)**: Schema decoding is exact modulo `normS`
  (`ofSchema_exact` (`src/Effect4/Schema/Bridge.lean`)).
- **Schema retraction (`of-schema-schema`)**: Inverting schema representations on reserved-free types
  (`ofSchema_schema` (`src/Effect4/Schema/Bridge.lean`)).
- **Record codecs (`record-codec-layout`)**: JSON decoding reconstructs named record values exactly under `normJ`
  (`decode_iff`, `src/Effect4/Laws/Schema/Codec.lean`; decisions row 165 (a)).
- **Term reconstruction (`collection-term-print-read`)**: structural reading reconstructs every scoped term after printing
  (`readTerm_printTerm`, `src/Effect4/Laws/Codegen/ReadLeaf.lean`).
  This includes raw record declarations and every natural tuple index.
  A payload class construction prints as `new Tag({ … })` and reads back under the module's classes (decisions row 120).
  Its premise is that the classes cover the term's class constructions (`Term.covers`).
  The scope premise remains unchanged; rendered-source recognition and target execution remain separate boundaries.
  An operation's binder term prints as a function of the cell's current value, after the row's call.
  It reads back one level up (`readPerform_printPerform` and `readPerform_exact`, the same file; the state plan's T5).
  `read_print` and `read_exact` keep their statements at such a row.
  An operation's type arguments print on the call's head and read back at the readable types
  (`readCall_printCall` and `readCall_exact`, the same file; `ReadableTy`, `src/Effect4/Codegen/Classes.lean`).
  A loop's stated cursor type reads back through the same checked type reader
  (`readTyChecked_exact` and `readTyChecked_of_readable`, `src/Effect4/Laws/Codegen/Classes.lean`).
  A list fold's stated accumulator type is printed and not read.
- **Service key identity (`service-identifier-injective`)**: at one signature's scope key, distinct service keys print
  distinct target Identifier types (`keyIdentifier_injective`, `src/Effect4/Laws/Codegen/ReadLeaf.lean`).
  An ordinary key prints its full key text; the scope key prints `Scope.Scope`.
  Identity holds within one pinned link table, not across modules; tsgo controls test the target reading.
- **Error payload exactness (`error-payload-exact`)**: a typed failure's record payload reads back exactly through the
  error image (`errOf_valOfErr`, `src/Effect4/Laws/Program/Admit.lean`; decisions row 120, part E1).
  The payload image (`Payload.image`) restricts the identity image to handle-free record frames, and `Store.Image` carries its laws.
  Its JSON image is the hexadecimal of its canonical bytes (`decodeErr_exact`, `src/Effect4/Laws/Schema/Codec.lean`).
  Part E2 prints one `Data.TaggedError` class per tagged payload type, and the printed module reads back.
  `read_print`, `read_exact` and `readModule_printModule` state the round trip.
- **Payload class declarations (`payload-class-decl-exact`)**: an admitted module's payload class declarations are the
  printed ones (`admitModule_classDecls`, `src/Effect4/Laws/Codegen/Admit.lean`; decisions row 120, part E2).
  The class reader accepts only the declaration that it prints back (`readClassDecl_exact`).
  The printer refuses a class whose declaration does not read back, by name, with its tag.
  The tsgo verdict on the printed forms is a finite check with a red twin (`ts/eff/test/payload-classes.test.ts`).
- **The mask's two rows (`mask-rows-table-premises`)**: The getter prints as the mask that
  answers its own restore (decisions row 245).
  A restore site prints as `pipe(body, saved)`.
  Both heads are reserved, and the row table's nine decided premises hold at the extended table.
  A restore site is readable exactly when its saved term is a readable leaf and its body is
  readable.
  `read_print` and `read_exact` keep their statements.
  It is a claim of program syntax: it establishes no typing and no behaviour of a target.
  (`mask_rows_table_premises` (`src/Effect4/Laws/Codegen/Mask.lean`)).

The `type-metadata-exact` claim requires an exact embedding of stored `Ty` declarations into structural TypeScript metadata.
It retains raw declaration order and absent optional fields.
Its retraction has no byte-frame size premise.
It supports record print/read reconstruction under decision row 196.
It establishes no execution property for generated TypeScript.

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
- **Row templates and the match (row 42; the state plan's T3a)**: A row's columns may hold parameters.
  `Ty.matchTemplate` infers bindings from the request, reading a request union member by member.
  It keeps them exactly when the request is below the template's instance, both sides normalized.
  The guard is the law (`matchTemplate_sound`), so inference can lose completeness and never soundness.
- **Records, maps, tuples and applications (rows 119, 162)**: the constructors are in `Ty`. `Ty.sub` compares
  records with the same canonical names and optionality field by field, covariantly (no width rule); maps
  exactly in the key and covariantly in the value; tuples of one length pointwise; and applications of one
  name and arity argument by argument, by each argument's declared variance (`argVariance`). The laws below
  quantify over every `Ty`, so they cover these constructors.

#### 3. Project Definition and Judgment
The static type language `Ty` possesses a decidable subtyping preorder `Ty.subN` evaluated on normalized forms:
```lean
def subN (a b : Ty) : Bool := sub a.normalize b.normalize
theorem subN_equiv_iff (a b : Ty) : (subN a b = true ∧ subN b a = true) ↔ a.normalize = b.normalize
```
(`src/Effect4/Laws/Program/TypeAlgebra.lean:1067`). Canonical types `CTy` form a bounded join-semilattice.

#### 4. Required Properties and Obligations
- **Raw formation (`raw-formation`)**: The raw check agrees with distinct record names, the admitted map-key predicate
  and a deferred's admitted error column.
  Rows 192 and 193 require this check before normalization at each checked public boundary.
  Open map keys and open error columns are deferred only in row templates.
  Formation establishes no inhabitance, codec admission or execution property.
- **Reflexivity (`subn-refl`)**: Normalized subtyping is reflexive.
  (`subN_refl` (`src/Effect4/Laws/Program/TypeAlgebra.lean`)).
- **Transitivity (`subn-trans`)**: Normalized subtyping is transitive.
  (`subN_trans` (`src/Effect4/Laws/Program/TypeAlgebra.lean`)).
- **Equivalence characterization (`subn-equiv-iff`)**: Subtyping equivalence coincides with normal-form equality
  (`subN_equiv_iff` (`src/Effect4/Laws/Program/TypeAlgebra.lean`)).
- **Normalization idempotence (`normalize-idem`)**: Normalization is idempotent.
  (`normalize_idem` (`src/Effect4/Laws/Program/TypeAlgebra.lean`)).
- **Antisymmetry on canonical types (`sub-antisymm-canonical`)**: `subN` is antisymmetric on canonical representatives.
  (`sub_antisymm_canonical` (`src/Effect4/Laws/Program/TypeAlgebra.lean`)).
- **Anchored completeness of the match (`template-match-anchored`)**: The statement fixes a normal, admissible
  template whose parameters each first occur as an invariant handle's argument (`Ty.anchored`).
  A normal request that some substitution places under its instance then has a match.
  The request holds no `never` outside such an argument (`Ty.bottomFree`); without that premise the
  statement is false (`E4-CHECK-CE-018`'s boundary).
  It is proved (`Ty.matchTemplate_complete_anchored`, `src/Effect4/Laws/Program/Template.lean`; seat
  T4).
  It establishes no match at a parameter first met covariantly, under a union template or under a
  nominal reference.
  `Ref.modify`'s `B` is such a parameter: it first occurs in the result of the row's binder term.
  The checker binds `B` from the term's raw type (`bindTerm`, `src/Effect4/Program/Typing/Rules.lean`)
  and claims no completeness there (the state plan's T3b).

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
- **Free-Category Path Interpretation (Row 48)**: Saved-stack judgments are factored through `Contracts.FramePath Edge`, a Prop-valued typed-path relation over frame lists interpreting composition through existential middle types. Identity (`nil`), append (`append`), splitting (`split`), and transport along edge implications (`map`) are proved once. Concrete stack judgments (`HostStack`, `PositionStack`) instantiate `FramePath` over `HostEdge` and `PositionEdge`; the unchanged `StackAccepts` is connected by two conversion theorems, with conversions and transports realized as functorial edge maps (`FramePath.map`).

#### 3. Project Definition and Judgment
Catamorphic folds and algebra homomorphisms are defined in `src/Effect4/Program/Fold.lean`:
```lean
theorem hom_eq_cata_eff {Op : Type} {R : EffFam → Type u}
    {alg : EffAlgebra Op R} (hom : EffHom alg) (node : Effect4.Program.Eff Op) :
    hom.f_eff node = cata_eff alg node
def inhabited (t : Ty) : Bool := cata_ty inhabitedAlg t
```
(`hom_eq_cata_eff`, `src/Effect4/Program/Fold.lean`; `inhabited`, `src/Effect4/Program/Columns.lean`).

#### 4. Required Properties and Obligations
- **Uniqueness of catamorphism (`hom-eq-cata-eff`)**: Any algebra homomorphism out of `Eff` is pointwise equal to `cata_eff`
  (`hom_eq_cata_eff` (`src/Effect4/Program/Fold.lean`)).
- **Inhabitation characterization (`inhabited-iff-fits`)**: Syntactic `inhabited` fold characterizes semantic non-emptiness in `Fits`.
  (`inhabited_iff_fits` (`src/Effect4/Laws/Program/Typed/Membership.lean`)).
- **Fold congruence (`cata-eff-congr-on`)**: Fold congruence over agreeing algebra implementations
  (`cata_eff_congr_on` (`src/Effect4/Laws/Program/Signature.lean`)).
- **Traversal census maintenance**: 100% fold coverage enforced by `#traversal_census`.
- **Operation data scoped (`operation-data-scoped`)**: the scope fold decides a `perform` node
  from its operation's own data, read by the alphabet's `ScopedOp`, and from its request
  (`Eff.perform_scoped_iff` (`src/Effect4/Laws/Program/Authoring.lean`)). Scope is not typing.
  Weakening is the frontier fold over the same data: it maps an operation's binder term with the
  program (`ScopedOp.mapTerm`, `src/Effect4/Program/ScopedOp.lean`).
  The checker's weakening law holds at every signature that is natural in that term
  (`check_weaken` and `Signature.WeakenNatural`, `src/Effect4/Program/Typing.lean`).
- **Reference expansion leaves no reference (`reference-expansion-complete`)**: a program
  whose layer references are well formed (`Eff.layerRefsWF`) expands to a program with no
  reference site. The bound is that of `Eff.expandRefs`: one more round than the program has
  reference sites (`expanded_refs_nil_of_wf`
  (`src/Effect4/Laws/Program/ReferenceExpansion.lean`)). The one premise is the formation of
  the references. Scope, type formation and typing are not conclusions. So the whole-program
  checker tests the references' formation only (`typeOfProgram`,
  `src/Effect4/Program/Typing.lean`). The program interface's refusal has no arm for a kept
  reference site (`Api.explain`, `src/Effect4/Api.lean`). Each equation is its definition's
  own (`typeOfProgram_eq_if_refsWF`, `src/Effect4/Laws/Program/ReferenceTyping.lean`;
  `Api.explain_eq_if_refsWF`, `src/Effect4/Laws/Api/Codegen.lean`). The property is about the
  expansion that typing reads. The compile does not expand: it redirects a reference to its
  target, and a run shares the layer by its path.

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
  (`satisfies_empty` (`src/Effect4/Machine/Context.lean`)).
- **Single requirement lookup (`satisfies-single`)**: Singleton requirements check key membership.
  (`satisfies_single` (`src/Effect4/Machine/Context.lean`)).
- **Union requirement splitting (`satisfies-union`)**: Union requirements split into conjunction.
  (`satisfies_union` (`src/Effect4/Machine/Context.lean`)).
- **Weakening monotonicity (`satisfies-weaken`)**: Monotonicity under context extension.
  (`satisfies_weaken` (`src/Effect4/Machine/Context.lean`)).
- **Complete emitted requirements (`emission-requirements-complete`)**: a checked emission's main declaration carries
  `Effect.Effect<A, E, R>` with its complete requirement row
  (`ModuleEmission.annotation_complete`, `src/Effect4/Laws/Codegen/Checked.lean`).
  It certifies generated syntax, not target type checking or execution.
- **Service capability discharge (`provide-discharges`)**: Layer provision discharges output capabilities.
  (`provide_discharges` (`src/Effect4/Program/Provision.lean`)).
- **Closed layer composition (`provide-closed`)**: Composing closed layers yields closed requirements.
  (`provide_closed` (`src/Effect4/Program/Provision.lean`)).
- **Build totality (`build-total`)**: Under a typed leaf semantics, a layer the checker types
  builds under every context that satisfies its requirement row, and the built context satisfies
  its output row (`build_total` (`src/Effect4/Laws/Program/BuildTotal.lean`), restored under
  decisions row 147). The machine's build refining `build` is the row's other half, still owed.
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
  (`allows_answer` (`src/Effect4/Laws/Run.lean`)).
- **Host reply commutativity (`reply-commute`)**: Independent host answers commute in session queues.
  (`reply_commute` (`src/Effect4/Laws/Api/HostSession.lean`)).
- **Frontier awaitHost inversion (`frontier-awaithost`)**: Machine awaitingAsync state matches frontier reason.
  characterization of frontier state matching `.awaitingAsync` (`observe_awaitingAsync_iff` (`src/Effect4/Laws/Api/Frontier.lean`)).
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
  (`run_eq_meaning` (`src/Effect4/Laws/Program/Agreement/Machine.lean`)).
- **Loop agreement (`loop-agreement`)**: Replay agreement holds across straight loop steps
  (`loopAgreement_of_straight` (`src/Effect4/Laws/Program/LoopAgreement.lean`)).
- **Reference machine simulation (`run-eq-ref`)**: Frame machine replay matches term reference replay at empty host table
  (`run_eq_ref` (`src/Effect4/Laws/Program/RuntimeR.lean`)).
- **M7 conditional route (`m7-route`)**: Derivation of M7 capstone conditionally from M5 and M6 ledger components
  (`m7_of_ledger` (`src/Effect4/Laws/Program/Typed/Assembly.lean`)).
- **Capstone M7 goals (`m7-capstone-goals`)**: Exit value agreement, final store agreement, non-halting, and exit handle
  validity on `M7Fragment` (`m7_proved` (`src/Effect4/Laws/Program/Typed/Assembly.lean`)).
- **The mask's printed form (`mask-printed-form-profile`)**: The mask is a derived form: the
  getter bound to its body under `uninterruptible` (decisions rows 245 and 246).
  The surface's builder is that expansion, and the form types as its body does under the saved
  state's binder.
  It is readable exactly when its body is, so it prints and reads back.
  Its entry has two checkpoints that the native mask does not have, stated on the frame machine.
  Inside the getter the fiber is masked, and a pending cause fails it at the getter's saved frame.
  After that frame an interruptible caller is interruptible until the body's mask.
  A client keeps one premise: nothing is acquired or registered before the body begins.
  It establishes no equality with the native spelling and no agreement with a release.
  (`mask_printed_form_profile` (`src/Effect4/Laws/Codegen/Mask.lean`)).
- **A journal's position replays (`journal-position-replay`)**: The machine after a position
  of a journal's tape is the raw replay of the decisions up to that position. The replay
  starts at the machine of the run that the tape was read from. A journal splits into a
  completed prefix and an unread rest, and the prefix's machine is the replay of its
  positions (`tapeFrom_cut_replays`). The laws say nothing about the machine after a stopped
  row: that row may change the machine before it reports its frontier.
  (`tapeFrom_position_replays` (`Test/Dogfood/Scenario.lean`)).
- **Pool's steps agree with the model (`pool-steps-agree`)**: Each of Pool's five step terms
  agrees with the model's step, on every state of the model. The agreement covers the reply,
  the stored value through the table, and the selected waiters' records. It is a part of the proposed claim
  `pool-expansion-agrees`. It states no order of the wake across helpers, no cancellation
  law, no close that waits and no wrapper.
  (`pool_steps_agree` (`src/Effect4/Laws/Modules/Pool/Steps.lean`)).

## 3. The object-language glossary (moved 2026-10-03)

The glossary that set our words against Lean's moved to the dictionary,
`docs/core/controlled-english.md` §3.2 and §3.3. It covers syntax, the three senses of
elaboration, print, read, render, lift, sugar, census and gate, each with its Lean counterpart.
Each site is now cited by name and path, not by line.

---

## 4. Metatheoretical Bounds & Evidence Summary

1. **Axiom Ceiling**: Every theorem the registry cites is checked by the producer at `[propext,
   Quot.sound]`; the whole-library gate (`Test/Audit/AxiomGate.lean`) holds every declaration
   there too, except the rendering and instrumentation modules it admits by name.
2. **First-Order Data Discipline**: Stored `Eff` syntax is first-order data: its bind continuation
   is another program tree with positional inputs (`src/Effect4/Program/Eff.lean`). `RProgram` is the proof-side
   semantic carrier `Effects.Program RSig ExitV`, whose visible operation nodes carry Lean function
   continuations (`vis : Answer op → Program sig A`). Those functions belong to the semantic model
   and are not stored function values in `Eff` or `Val`.
3. **Simulations vs. Equivalence**: Behavioral relationships are stated strictly as equal-observation
   theorems over specified fragments (`Straight`, `Looped`, empty host table `M7Fragment`), never
   as unqualified "equivalence".
4. **Literature Tracking**: Every textbook chapter and academic paper citation is audited against
   vendored copies in `docs/research/2026-10-01-semantics/citations-audit.md`.
