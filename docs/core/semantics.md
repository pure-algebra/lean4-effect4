# Semantics: the language's judgments, their literature and their obligations

This document owns Effect4's semantic judgments, their literature, their cuts and their required properties. Eleven
concepts, each in four parts: what the literature defines; our adaptation, assumptions and
exclusions; the definition and judgment in the tree; the required properties.

What this document does not own, and who does:

- **Status.** `generated/semantics.md` measures whether each property is proved, wanted, refuted, absent or assumed.
  `make gen-semantics` produces it from `tools/ProofGraph/Registry.lean` and the loaded environment (`docs/GENERATED.md`, group `semantics`).
  `ProofRef.validate` and `ProofGraph.check` derive every status.
- **Decisions.** `docs/core/decisions.md`; the cuts below cite its rows by number.
- **The goal, the sorts, the arrows and the requirements.** `docs/core/system-map.md`.
- **What is next.** `docs/STATE.md`.
- **Counterexamples.** `Test/Counterexamples/REGISTER.md`.
- **The sources.** `git:98a29895b800556365a2edc9924f3ed12787b820:docs/research/2026-10-01-semantics/sources/README.md` (vendored with
  checksums) and `git:98a29895b800556365a2edc9924f3ed12787b820:docs/research/2026-10-01-semantics/citations-audit.md` (every locator read off a
  vendored page). TAPL and ATTAPL locators remain unverified until the owner's copies are vendored.
  This includes theorem numbers, rule numbers and in-section page numbers. Those references are marked as cited.

Gemini drafted this document on 2026-10-01, concept-first after Codex's review.
The coordinator reviewed it against the tree and ran the historical locator check:
`python3 docs/research/2026-10-01-semantics/check-gemini-drafts.py docs/core/semantics.md`.
That check found every declaration with a `path:line` locator within three lines of its cited position.

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
11. **Typed Editing** (`typed-editing`; decisions row 414 (5); prose only while semantics
    generation is paused, row 418 (6))

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
The scope-exit marker is typed only at the run position of the guard the `scoped` arm installs (`scopedGuard`).
This requires a live scope and a fitting restored context (decisions row 188 (a)).
As current code, the counted step answers it `badShapeExit` (`E4-TYPED-CE-034`). `DenotesTyped` connects admitted
source points to that residual judgment. These definitions resemble protocol-based program logics,
but identifying them with weakest preconditions would require a named execution interpretation and
a stated correspondence. The unrestricted bind counterexample (`E4-TYPED-CE-030`) alone does not
settle every possible weakest-precondition interpretation.

A claim's title, role and selected evidence express an authored interpretation. The rendered
proposition states exactly what its theorem proves or its planned goal requests. Checking a theorem
does not check the English interpretation. Refutation and contest links therefore expose the
registered attacked statement and revision alongside the witness. Historical attacks do not
automatically refute repaired propositions.

Progress, preservation relative to a step relation, scheduling service and interpreter agreement ask different questions. An
invariant can exclude a halted configuration without establishing a successor. Progress must account
for finished states, permitted transitions and live frontiers.
Preservation relative to a step relation concerns its covered transitions. Finite scheduling service concerns actual callback entry under its stated readiness
and bounds. Internal replay agreement retains its empty-host fragment. None of these statements
alone proves termination or eventual host cooperation.

The generated report checks every concept's selected claims in the loaded environment. A
concept's claims are a selection, not a complete inventory: an owed property is made visible as
an `absent` claim. A planned goal placed at a requirement (`@[semantics "concept" (requirement :=
Rn)]`, decisions row 207) is one of its nodes.
A goal neither placed nor reached is listed as unplaced. Generated tables own evidence status, propositions,
and counts; prose explains meaning, scope, and boundaries. Cuts own applicability.

### 1.2 API and Evidence Boundary

This specification distinguishes authored descriptions from evidence checked in the loaded Lean
environment. A claim's title and role explain why its evidence matters; the rendered proposition
states exactly what was proved or requested.

| Item | Owner | What readers can conclude |
| --- | --- | --- |
| Claim identity, concept, role, title and evidence pointer | `Tools.Semantics.registry` | Authored assignments identifying a theoretical question and its selected evidence. |
| Theorem statement, universes, module and axioms | Loaded Lean environment | A `witness` is checked as a theorem of its own printed proposition under the semantic axiom ceiling `[propext, Quot.sound]`. |
| Obligation proposition and checked/wanted evidence | Existing `ProofGraph` ledger | A `goal` is a declared question. Its checked witness or wanted declaration must match that question, including binders and universes. Selected goals do not establish coverage of an entire ledger scope. |
| Refutation and contest associations | Registry links to `Test/Counterexamples/REGISTER.md` | Checks the referenced row and witness theorem. Read the row's attacked statement and revision alongside the printed evidence. |
| Applicability | Decisions register, referenced by `Cut` | A cut limits the question's domain. It does not prove, refute or discharge the question. |
| Declaration placement | Explicit concept tag, then semantics registry module default | Each eligible declaration has one primary home; inherited placement is provisional. |

Status indicators describe the selected evidence. `absent` means no witness, goal, or refutation is selected.
It distinguishes an owed obligation from a role outside the cut, which cites decisions rows.
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
| PLF / Harper | Precise progress, preservation relative to a step relation, canonical-forms and substitution questions | Apply each to the local judgment; do not substitute codec or invariant facts |
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
semantic result. The source audit (`git:98a29895b800556365a2edc9924f3ed12787b820:docs/research/2026-10-01-semantics/types-2003-scout/book-scout.md`)
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
evidence status. The tooling follow-up (`git:98a29895b800556365a2edc9924f3ed12787b820:docs/research/2026-10-01-semantics/types-2003-scout/tooling-adoption.md`)
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
  line 1539, audit F5, F17). Under store extension ($\Sigma \subseteq \Sigma'$), allocating fresh cells keeps previously allocated locations typed.
- **World Indexing & Kripke Models**: ATTAPL ch. 6, Karl Crary, "Logical Relations and a Case Study in Equivalence Checking", pp. 223–244.
  Section 6.7 is *A Monotone Logical Relation*, p. 236 (audit A2, A4, A8, A12–A15).
  Amal Ahmed (2004), *Semantics of Types for Mutable State*, PhD thesis, Princeton (audit P1, C1).
  These works give world-indexed semantic interpretations with future-world accessibility ($w \le w'$).

#### 2. Effect4 Adaptation, Assumptions, and Exclusions
- **Adapting Kripke Worlds**: Effect4 adapts Kripke store typings into `Effect4.Program.Typed.World`.
  Its explicit partitions hold fibers ($\Gamma$), promises ($\Pi$), heap references (`Ρ`, Greek rho, field `w.Ρ`), and ghost resume states ($\Theta$).
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
  (normalized subtyping both ways). Raw subtyping does not distribute products over unions (`E4-TYPED-CE-009`).
- **Scope Handle Persistence (Row 156)**: Scope handles require `ScopeLive w sc`; dangling handles do not fit `Ty.scope`.

#### 3. Project Definition and Judgment
Value membership in Effect4 is defined by the judgment `Effect4.Program.Typed.Fits`:
```lean
def Fits (w : World) (v : Val) : Ty → Prop
```
(`src/Effect4/Laws/Program/Typed/Membership.lean`). It asserts that runtime value `v` inhabits semantic type `ty`
under world `w`. Handle leaves verify capability declarations against `w.Ρ`, `w.«Π»`, `w.Γ`, and scope
persistence `ScopeLive w sc`. At exit types (`.exitOf a e`), the reified cause is checked to be `ShapeFree`
(excluding defects `badName` and `notImplemented`, decisions row 152).

#### 4. Required Properties and Obligations
- **A declared source uses its declarations (`stream-source-declarations`)**: Adapter acceptance relates the source's protocol and state requests to the supplied operations.
  Every invocation uses the corresponding declaration's name.
  Application to an installed module requires matching declarations at those names.
  The law is `Source.fromDefinitions_declarations` (`src/Effect4/Laws/Library/Stream/Definitions.lean`).
  The module checker still owns argument typing, formation, errors, requirements and definition bodies.
  The adapter establishes no batch nonemptiness, execution, finalization or host behavior.
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
  (`handle_identity_laws` (`src/Effect4/Laws/Program/Typed/HandleIdentity.lean`)).
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
- **A modeled value inhabits its type (`modeled-membership`)**: The carrier fold gives each
  supported `Ty` its Lean carrier and its exact embedding together (`Model.alg`,
  `src/Effect4/Schema/Modeled.lean`).
  The refusal fold names the first reason a type is outside the checked domain
  (`Model.refusalAlg`).
  It refuses an identity type, an optional field and each constructor with no carrier yet.
  It refuses a record whose names are not strictly ascending by their bytes.
  On the checked domain, every carrier value's encoding inhabits its type at every allocation
  table (`Model.member`, `src/Effect4/Laws/Schema/Modeled.lean`).
  An instance of `Modeled` proves its type checked, and its image is the fold's.
  So an instance inherits the law with no proof of its own (`Modeled.member`).
  It establishes nothing for an identity type, an optional field or a refused constructor, and
  no codec admission (decisions row 330).
- **Membership under a declaration table (`recursive-types-decided`)**: a table of monomorphic
  type declarations is read iso-recursively (decisions rows 124, 158 and 400).
  Its other claims are `recursive-types-unfold`, `recursive-types-conservative`,
  `recursive-types-sub`, `recursive-types-inhabited`, `recursive-types-normalize` and
  `guarded-fixed-point-unique`.
  A body refers to a declared name by `app n args`, which normalization keeps (decisions row
  406 (1)).
  A host handle `handle n` is never a declared name: the signature's admission refuses one.
  Membership under the table is an inductive predicate, the least fixed point
  (`MemberIn`, `src/Effect4/Laws/Program/TyDecls.lean`).
  A union holds its sides' members, and a declared reference holds its body's members.
  A head holds a value when the value's shape fits and every question of the step holds
  (`Val.obligations`, `src/Effect4/Program/TyDecls.lean`).
  The checker `Val.hasTyIn` decides it on every table, guarded or not (`hasTyIn_iff`).
  Its measure is the value's size, then the declared names not yet unfolded, with no fuel.
  A reference has exactly its body's members (`memberIn_unfold_iff`).
  On the empty table the checker, the predicate and inhabitance are `Val.hasTy`, its answer and
  `inhabited` (`tyDecls_conservative`).
  The unchanged `Ty.sub` keeps the members of every table (`memberIn_sub`).
  The proof reads the predicate as the fold `Val.hasTy.alg` with each declared name read from
  the checker (`memberIn_iff_cata`).
  Inhabitance under the table, iterated to its least fixed point, is sound against membership
  (`inhabited_of_memberIn`).
  Three properties are planned goals: inhabitance complete against membership, membership
  invariant under normalization, and one fixed point on a guarded table.
  It establishes nothing of `Fits`, a world, a parameter or a face.
  The formal note is `git:98a29895b800556365a2edc9924f3ed12787b820:docs/research/2026-10-15-recursive-types/formal.md`.
- **A step types at its type (`step-language-typed`)**: A step is data over typed inputs
  (`Step`, `src/Effect4/Step.lean`), and it has a source term at every scope.
  Let the caller's terms type at the inputs' types, and let the step's typing facts hold.
  Then its term types at the step's type, under each literal flag (`Step.typed`,
  `src/Effect4/Laws/Step.lean`).
  A caller proves the facts from premises where a type is a parameter, as Pool and the Queue do
  from `A.normalize = A`.
  Or the typing check proves them (`Step.typed_of_normal`): it certifies normal forms by a fold
  of `Ty` (`Ty.normalize_of_certNormal`, `src/Effect4/Laws/Program/TyNormal.lean`).
  So it closes by `rfl` on a concrete step, a product included.
  The signature assigns the native types to atoms.
  A fold also requires the caller's type list to match the source scope length.
  Record construction retains type formation and normality.
  Empty-value subtyping follows from the shared construction law.
  It establishes no run, optional field, allocation or host behavior (decisions row 330).
- **Store safety invariant (`store-safety`)**: Well-typed machine stores produce values that Fit their
  declared types across write operations (seat D5; decisions rows 134, 139 and 181).
- **Pool's profile on the model (`pool-profile-closed`, `pool-lease-enrols`)**: Each of the
  six transitions of Pool's abstract model keeps the first profile. The sixth is the closer's
  step (decisions row 276, point 2). The law has no premise on a request. An idle item beside enrolled waiters is a state of the profile. On a state of the
  profile, a lease enrols its request exactly when the pool is open and a lease holds every
  item. Neither states
  fairness, liveness or anything of a program.
  (`profile_closed`, `lease_enrols_iff` (`src/Effect4/Laws/Library/Pool/Profile.lean`)).
- **The waiting forms are typed once (`waiting-wrapper-typed`, `protected-form-typed`)**:
  Assume the module's part is typed.
  The waiting wrapper at a caller's restore then answers its result type at every typed scope (`waitRetryAt_answers`). The result type is in normal form.
  The wrapper with no loop answers its hint's type at every typed scope, when the module's
  part is typed at that type (`waitAnswer_answers`). It asks no normal form of the hint's
  type: a type with a hint's three rows is its own normal form (`HintTy.canonical`).
  The protected form keeps its body's effect type (`protectedBy_has`). It is one mask over an
  acquisition, a body at the restore site and a release under the exit's binder. The
  acquisition and the release answer a type, with no failure and no requirement. Both laws
  are typing only. They state no run, no law of the mask and no release at an exit. The
  theorems are in `src/Effect4/Laws/Step/Waiting.lean`.
- **Pool's operations are typed at every scope (`pool-use-typed`, `pool-make-typed`,
  `pool-close-typed`)**: `use` keeps its body's effect type. The lease and the return add
  no failure and no requirement. The refusal at a closed pool adds none: an interruption
  has no failure type. `make` answers the pool's handle. Its failure type is the
  acquisition's, so a failed acquisition fails `make`. Its requirement is the acquisition's
  with the scope's key, so a pool is made inside a scope. The close answers the unit, with no
  failure and no requirement: it is a release that cannot fail, and `make` registers it. Each
  statement takes a resource type in normal form whose item record and cell record are
  formed. An acquisition whose answer is another type is outside `make`'s statement. The
  three are typing only: no run, no law of the mask, no wait of the close and no finalizer's
  run. (`use_types`, `make_types`, `close_answers`
  (`src/Effect4/Laws/Library/Pool/Ops.lean`)).

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
  non-local control flow violates naive bind typing. Sequencing therefore needs per-construct compatibility lemmas in `src/Effect4/Laws/Program/Typed/Seq.lean` (seat D2).
  The general form is `guardBind_typed`. Its shapes are `seqGuard_typed` (`onSuccess`), `catchGuard_typed` (`onFailure`), `allGuard_typed` (`all`, `onExit`), `onExit_typed` and `seq_typed`.
- **Closed Root Requirement Rows (Row 117)**: Admitted programs enforce `rootTy.requires = empty` at load time,
  reflecting rc.112's `runPromise` contract (`Effect.ts:17494-17497`).

#### 3. Project Definition and Judgment
Residual programs resulting from elaboration are typed by `Effect4.Program.Typed.TypedProg`:
```lean
inductive TypedProg (root : ProgramSource) : World → EffTy → RProgram → Prop
```
(`src/Effect4/Laws/Program/Typed/Residual.lean`). Operation clauses require certificate validation and enforce that
continuations type for all permitted replies at later worlds. Dedicated typing arms govern `.guard`, `.unguard`, `.finishFinalizer`, and the `scoped` guard.
The last guard's run arm is the scope-exit callback (`.scopedGuard`, decisions row 188 (a)).
Its saved slot is `FrameAccepts.scopedResume`.

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
  `denotesTyped` (`src/Effect4/Laws/Program/Typed/LayerArm.lean`).
  `loadsTyped` proves the load (`load-typed`) in that file.
  It uses the load connector whose race-marker premise the root code's typing discharges
  (`loadsTyped_of_denotesTyped_typed`, `src/Effect4/Laws/Program/Typed/Commands/Finish.lean`).
  The displayed implication abbreviates the premises of `DenotesTyped`. The first is the source's
  formation (`SourceWF`): well-formed layer references, and a definition block's bodies typed. The
  others are a world whose service table equals the source's, and an admitted source point whose
  path selects an effect node. The load discharges the formation from the checker's verdict
  (`sourceWF_of_typeOf`, `src/Effect4/Laws/Program/Typed/Assembly.lean`).
- **The invocation's arm (`invocation-arm`)**: an invocation of a checked block denotes a
  `TypedProg` at the declared row (`call_arm` (`src/Effect4/Laws/Program/Typed/Denotation.lean`)).
  The request's value fits the declared request. The body is typed at its point, one unit of fuel
  lighter, and its type widens to the declared columns. A block has no step of its own: the load
  types its main program's point (`rootCode_typed`, `src/Effect4/Laws/Program/Typed/Assembly.lean`).
  It does not establish progress, liveness or the termination of a recursive definition.
- **Failure handler compatibility (`on-failure-typed`)**: Compatibility lemma for the error recovery bracket `onFailure` (decisions row 148), proved by
  `catchGuard_typed` (`src/Effect4/Laws/Program/Typed/Seq.lean`).
- **M5 on the layer-free fragment (`denote-typed-layer-free`), and the layer family's arm (`provide-layer-arm`)**:
  `childDenotes_upto` assembles every `denoteR` arm by fuel induction (`src/Effect4/Laws/Program/Typed/Denotation.lean`).
  Zero fuel gives the frontier. Positive fuel uses each constructor's arm, with children's hypotheses taken at their nodes.
  The layer family enters as the `ProvideLayerArm` hypothesis in that file.
  Thus `denotesTyped_of_provideLayer` is conditional (`src/Effect4/Laws/Program/Typed/Assembly.lean`).
  `LayerFree` programs have no `provideLayer` node (`src/Effect4/Laws/Program/Typed/Denotation.lean`).
  They cannot reach that arm (`denotesTyped_of_layerFree`, `src/Effect4/Laws/Program/Typed/Assembly.lean`).
  `provideLayerArm` proves the arm at every source (`src/Effect4/Laws/Program/Typed/LayerArm.lean`).
  Decisions rows 176 (b), 185–187 record it; `E4-TYPED-CE-023` and `-031` are repaired.
  `layerBuild_typed` types every `LayerTerm` constructor's build at an admitted layer point.
  The build answers the built context at the layer's checked error type.
  The proof is structural on the term, inside induction on fuel spent by reference hops.
  Expansion fixes checked terms, and checking is path-independent (`ExpandFix`), so each hop's point is typed.
  `memoize_typed` types memo hits through the memo-table clause.
  `mergeContexts_typed` shows awaited merge exits either all read back or fail with fitting reasons.
  `provideLayer_arm` types the protocol around the build.
  These four theorems live in `src/Effect4/Laws/Program/Typed/LayerArm.lean`.
  The store-row arm adapts the textbook reference-read argument: TAPL §13.4's store typing and PLF `References.v`'s `store_weakening`.
  Membership in `refOf A` exposes a declaration (`fits_refOf_inv`, `src/Effect4/Laws/Program/Typed/Denotation.lean`).
  Its type equals `A` under normalized subtyping, not syntactic equality.
  `leHost` keeps the declaration, and the reply's lookup identifies it.
  `fits_subN` transports the reply (`refRead`, `src/Effect4/Laws/Program/Typed/Denotation.lean`).
  The `Ref` and `Deferred` rows are templates (the state plan's T3a).
  `syncRow_typed` reads the node's checked instance off the row's match (`rowTy_fits`).
  `perform_arm` consumes it; both live in `src/Effect4/Laws/Program/Typed/Denotation.lean`.
  `service_arm` keeps source/world service-table agreement as a premise and admits the missing-service defect, which is not a service value.
  `exit` covers its inline branch through `inlineYield_typed`; both live in `src/Effect4/Laws/Program/Typed/Denotation.lean`.
  The load connector needs only the fundamental property: typed root code is never a race registration marker.
  `loadsTyped_of_denotesTyped_typed` discharges that marker premise (`src/Effect4/Laws/Program/Typed/Commands/Finish.lean`).
  A checked layer-free program therefore loads into `J` (`loadsTyped_of_layerFree`, in that file).

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
(`src/Effect4/Machine/Scope.lean`). A scope transitions from `openEmpty` or `openMap` to `closed exit`. Scope presence
in the typed world is governed by `ScopeLive w sc` (World.lean (`src/Effect4/Laws/Program/Typed/World.lean`)), witnessed by `fits_scope_inv`.

#### 4. Required Properties and Obligations
- **Finalizer starts spend registrations (`finalizer-starts-bounded`)**: Every native decision prefix starts each source's finalizer no more often than it pushes that finalizer's frame.
  `Program.FinalizerRun.starts_le_pushes` states the bound in `src/Effect4/Laws/Program/FinalizerRun.lean`.
  The program, row table and compile budget remain arbitrary.
  The proof counts retained finalizer frames through every command and decision edit.
  It establishes no source uniqueness, cleanup-log provenance, progress or host behavior.
- **Source uniqueness for finalizers (`once-placed-finalizer`)**: A once-placed source pushes its finalizer frame at most once across all fibers.
  `Program.FinalizerRun.once_placed_pushes_once` states the obligation in `src/Effect4/Laws/Program/FinalizerRun.lean`.
  Its premise is `OncePlaced` and native reachability.
  It serves the original Atomic cleanup bound and establishes no progress or log-writer provenance.
- **Close idempotence (`close-idempotent`)**: Closing an already closed scope is a no-op.
  (`close_idempotent` (`src/Effect4/Machine/Scope.lean`)).
- **Consecutive close idempotence (`close-twice`)**: Applying close twice produces void.
  (`close_twice` (`src/Effect4/Machine/Scope.lean`)).
- **LIFO execution order (`close-order-eq`)**: Finalizers run in reverse registration order.
  (`closeOrder_eq` (`src/Effect4/Machine/Scope.lean`)).
- **Re-entrant addition semantics (`close-reentrant-add`)**: Adding to closed scope executes immediately.
  (`close_reentrant_add` (`src/Effect4/Machine/Scope.lean`)).
- **Close iterator protocol (`close-seq-protocol`)**: Close walk satisfies iterator protocol for clean finalizers
  (`closeSeq_protocol` (`git:68856e778:Test/Program/ProtocolPosts.lean`)).
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
- **The saved mask's chain through a pop (`saved-mask-pop-discipline`)**: At a fixed base bit, a fiber's restoring frames alternate from the negation of its flag (`MaskChain`). The frame machine's pop keeps the chain, from an empty scratch stack.
  `getCont`, the finished frame's path and the entry of each region keep it too. Two fibers
  with one base and one stack have one flag. It is a local law of the frame machine. It
  states no law of a run, no completed exit and no bracket of a region.
  (`saved_mask_pop_discipline` (`src/Effect4/Laws/Machine/MaskDiscipline.lean`)).
- **The saved mask's chain at every live fiber of a run (`saved-mask-chain-runs`)**: A
  table of start flags is proof data: the machine stores no base. Each live fiber holds the
  chain at its own flag of the table (`MaskRuns`). Each command keeps the invariant under one
  condition, on `Cmd.exitDone` alone. Just before it clears a fiber, that fiber has exited,
  or its stack is empty, or its flag is its base. `Cmd.finish` publishes the fiber before it
  clears it, so it asks for nothing. The command loop discharges the condition, so every
  decision, tape and fuel keeps the invariant. The claim's pointer states it at the compiled
  program's interpreter (`compiled_mask_chain_runs`
  (`src/Effect4/Laws/Program/MaskRuns.lean`)). Its general form is at the frame evaluator
  (`saved_mask_chain_runs` (`src/Effect4/Laws/Machine/MaskRuns.lean`)). Each entry outside
  the machine that returns a machine keeps it, with no premise for the condition. An entry
  that starts a run holds it outright. An entry that steps a machine keeps it from that
  machine. (`src/Effect4/Laws/Program/MaskRuns.lean`, `src/Effect4/Laws/Api/MaskRuns.lean`).
  Along a run, a live fiber's flag is a function of its stack (`MaskRuns.flag_eq`). It states
  no bracket of a region. The bracket is `saved-mask-region-bracket`. It states nothing of
  an exited fiber, of cleanup, of delivery or of progress.
- **A region ends at its entry's stack and at its entry flag (`saved-mask-region-bracket`,
  `stepped-fiber-live`)**: A region is no syntax of the machine. Its entry is a run cut. A later cut is inside it where the fiber's stack is own frames over the entry's stack. The later cut's stack shape `above ++ below` is a premise, and it is the region's
  only mark on the machine. The theorem then gives the entry's stack and the entry flag at
  the region's end. It does not give that a body's run keeps that shape. The end is inside a
  pop: the fiber that the pop of the own frames leaves, where no own frame answers. At a
  compiled command loop a fiber that a pending command steps has not exited
  (`stepped-fiber-live`), so the statement takes no premise on an exit. That fact is false
  at a hand-written interpreter. Both laws give no cleanup, no release count, no delivery,
  no budget and no liveness, and nothing of a region whose fiber exits inside it.
  (`compiled_region_bracket`, `stepped_live`
  (`src/Effect4/Laws/Program/MaskBracket.lean`); the general form is
  `saved_mask_region_bracket` (`src/Effect4/Laws/Machine/MaskBracket.lean`)).
- **Scope validity under nesting (`scope-validity-open`)**: General scope validity under dynamic parent-child nesting
  (D4 hand-back, row 156).
- **Pool's return and close on the model (`pool-return-front`, `pool-return-once`,
  `pool-close-refuses`, `pool-drain-waits`)**: A held lease's return puts its item before the idle items. It keeps every item. The lease then holds nothing
  (`giveBack_front`). A second return of that lease changes nothing (`giveBack_once`). After
  the close's first step every lease is refused (`close_refuses`). The closer's step answers
  true exactly where no lease is outstanding, and it enrols the closer otherwise
  (`drain_waits`). They state no finalizer's run and no wait of the close along a run. The
  four theorems are in `src/Effect4/Laws/Library/Pool/Profile.lean`.

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
  Ordinary program typing excludes administrative markers.
  The raw `scopeExit` remains in the semantic carrier, but `TypedProg` excludes it.
  `TypedProg` admits the callback only at the `scoped` guard's run position and saved slot (`scopedGuard`, `scopedResume`, row 188 (a), `E4-TYPED-CE-034`).
  The host-stack judgment admits registration callbacks under injected yields as correlated arrows carrying race existence and token typing.
  These are `HostStack` and `PositionStack` (row 188 (b), `E4-TYPED-CE-033`).
  Queued observe sources are bounded below `nextId` (`QueueOk.observer`, `HeadOk.observer`, row 189, `E4-TYPED-CE-035`) to prevent vacuous
  antitone $\Gamma$-reads admitting unallocated future fibers.

#### 3. Project Definition and Judgment
The operational configuration and decision types are defined in `src/Effect4/Machine/Fibers.lean`:
```lean
structure RunMachine (ν σ : Type u) (β : Type v) (ε δ ι α χ : Type u) (St : Type (max u v)) ...
inductive RunDecision ...
```
(`src/Effect4/Machine/Fibers.lean`). Machine type safety is maintained by the configuration invariant `MachineTyped root rootTy w m`
(`src/Effect4/Laws/Program/Typed/Assembly.lean`).

#### 4. Required Properties and Obligations
- **Invariant non-halted consequence (`machine-typed-not-halted`)**: A halted machine cannot satisfy `MachineTyped`.
  (`machineTyped_not_halted` (`src/Effect4/Laws/Program/Typed/Assembly.lean`)).
- **Finite queue fairness (`flush-fair`)**: Callback entry within rounds bound.
  `m.armed.Nodup → FlushReady interp fuel m.armed.length m = true → m.armed.length ≤ rounds → ∀ owner ∈ m.armed, FiredWithin interp fuel rounds m owner = true`
  (`flush_fair` (`src/Effect4/Laws/Machine/Scheduling.lean`)).
- **Random descent (`random-descent`)**: Take a step labelled by decisions, and an equivalence `R`
  that is a bisimulation of it. Under the local diamond up to `R`, every tape to a terminal state
  has one length and an `R`-equal end. One such tape bounds every tape.
  `Equivalence R → Bisim step R → Diamond step R → run step s c1 = some t1 → Terminal step t1 → run step s c2 = some t2 → Terminal step t2 → R t1 t2 ∧ c1.length = c2.length`
  (`complete_unique` (`src/Effect4/Laws/Machine/Descent.lean`)). It states nothing of the machine.
  The machine's raw decisions are no instance, since some are always enabled; its use is the
  checked fragment of decisions row 361.
- **Finite fair-tape endpoint (`fair-tape-drains-armed`)**: A fair finite tape that suffices leaves
  no armed owner at its live end.
  `FairTape interp fuel m tape → Suffices interp fuel tape m = true → (replayEval interp fuel tape m).machine.stuck = none → (replayEval interp fuel tape m).machine.armed = []`
  (`fairTape_unarmed` (`src/Effect4/Laws/Machine/Scheduling.lean`)). It is the finite half of R12.
  It says nothing about infinite tapes, termination or host progress. `flush_fair` permits
  rearming, so it is not general scheduler fairness.
- **Frontier names work (`frontier-names-work`)**: At a live, unfinished machine whose tape ran out, the frontier is empty exactly at a deadlock.
  Deadlock means no runnable fiber, armed owner, host request, timer or compile budget.
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
  `queue-first-run-flags`)**: One step of a first operation keeps `FirstRunInv`.
  This invariant includes the profile, the buffer's bound, `tidy`, `quiet`, and the run's two flags.
  So both flags hold after every list of first operations from the empty queue of a positive
  capacity. It is the model's half of `wait-registration-no-gap` and of
  `waiting-request-obligation-preserved`. It states nothing of a program, of a signal's
  delivery or of liveness.
  (`first_step_inv`, `first_run_flags` (`src/Effect4/Laws/Library/Queue/Invariant.lean`)).
- **Pool's wake selection on the model (`pool-select-takes-first`)**: One selection takes the first waiters of its input state, at most its count. It changes only the waiters. It is one selection: it states no run and no liveness.
  (`select_takes_first` (`src/Effect4/Laws/Library/Pool/Profile.lean`)).

#### 5. How the scheduler proofs use the theory

The proof structure is induction on executions: establish the loaded configuration, prove each
command and decision case, then assemble reachability. This follows Lynch and Vaandrager's invariant method, *Forward and Backward Simulations I*, §6 (audit C4).
Isolated command tests do not establish whole-machine typing. `decisionKeeps_of_steps` and
`typedState_reachable_of_steps` expose the remaining premises; their formal consumers are
`decision_preserves` and `typedState_reachable`.

Within a command, two smaller arguments meet. `configTyped_frame` transports clauses across a
store edit under its explicit unchanged-view, typing, key and due-owner hypotheses.
`completionStrong_await` moves a completed Deferred's answer and error evidence to a declared
waiter type. `wake_preserves` uses both arguments at the actual machine step, and supplies
`wake_preserves`'s checked witness. The frame-rule and protocol-subsumption analogy guides this decomposition.
Its source is de Vilhena and Pottier, *A Separation Logic for Effect Handlers*, §3.3 and §4.2.4 (audit P8). Our ordinary Lean predicates do not implement that paper's Iris resource
algebra or separation logic; the displayed theorem premises are the local contract.

Registration completion adds a pending record at one race key. `ObsViewOff` and
`configTyped_rupdate_park` permit that one lookup change while transporting countdown
correlations at other keys. Decisions row 134(d) supplies the stored and queued observer
exclusions. `registrationDone_preserves` combines this transport, race payload typing and
cancellation-frame typing for the accepted, deferred-interrupt and ordinary park branches.
It supplies the unchanged `registrationDone_preserves` goal; the CE-028 battery separately
checks refusal of the historical countdown collision and acceptance after removing only that
countdown. The receipt (`git:98a29895b800556365a2edc9924f3ed12787b820:docs/research/2026-10-02-codex-lead/registration-receipt.md`) records each
helper's concrete consumer. This remains a local invariant proof, with the same limits as above.

The machine generates two internal administrative markers during execution.
They are not user-space programs. The typing invariant places each where the operational semantics expects it (decisions row 188):
1. **Scope-Exit Callbacks (`E4-TYPED-CE-034`)**: When a `.scoped` block executes, it creates a scope-exit callback to close the scope and restore the surrounding context. The raw `scopeExit` marker remains in the semantic program carrier, but ordinary `TypedProg` admission excludes it. The scope callback is admitted at the `scoped` guard's run position and saved slot (`scopedGuard`, `scopedResume`). This repairs the typing contract around the evaluator's explicit `badShapeExit` fallback (`evaluateFiberR`); it does not remove syntax or prove general loop/delivery preservation. The evaluation walk yields the `CallbackSaved` alternative of `WalkTyped`, which `prepareScopedExitR` consumes directly.
2. **Race Registration Callbacks under Injected Yields (`E4-TYPED-CE-033`)**: `beginRace` sets up a race. Budget preemption (`injectYield`) can then save the registration marker inside a success continuation on the stack. The host-stack judgment composes ordinary frames and registration arrows that carry race existence, the matching host and token typing. `HostStack` admits the injected-callback shapes while requiring those correlations. Preservation of typing by `injectYield` and the subsequent walk remains part of the open loop/delivery proofs.

All saved-stack judgments are factored through a unified typed-path relation (`Contracts.FramePath Edge`, decisions row 48):
- `Contracts.FramePath Edge` is a Prop-valued typed-path relation over frame lists, interpreting composition through existential middle types.
- It provides generic identity (`nil`), append (`append`), splitting (`split`), and transport along edge implications (`map`).
- `HostStack` and `PositionStack` instantiate it over `HostEdge` and `PositionEdge` respectively.
- The unchanged `StackAccepts` is connected by the two conversion theorems (`framePath_of_stackAccepts`, `stackAccepts_of_framePath`).
- Conversions (`positionStack_of_host`, `hostStack_of_stackAccepts`) and Kripke-monotonicity transports (`hostStack_mono`, `positionStack_mono`) are derived as single functorial edge maps (`FramePath.map`).


Queued command arguments are bounded below `nextId` wherever an antitone declaration reading would otherwise admit unallocated future fibers (decisions rows 134 (e) and 189). `RCmdOk`'s `observe` arm reads the static fiber environment $\Gamma$ antitonically.

```text
∀ ty, Γ(source) = some ty → ExitOk ty exit
```

If a queued command names an unallocated fiber ID, this premise is satisfied vacuously. When `launch` subsequently allocates that ID below the race's column, the retained exit can violate the child's declared type (`E4-TYPED-CE-035`). Requiring `source.value < m.nextId` in `QueueOk.observer` and `HeadOk.observer` closes this gap, mirroring the enrollment bound for race children (`EnrollRaceOk`).


In particular, token bounds, disjointness from external requests, and race/observer separation
are different properties. They do not state that every internal key occurs at most once, nor
that a reply will eventually arrive. A “sender transfer” is explanatory language for a checked
implication between two typing demands. Unique ownership, at-most-once delivery and liveness
require their own stated invariants or operational theorems. The CE-026 battery checks that the old wrong-column witness is refused and the corrected wake is typed.
Its repeated-wake equation is a finite control, not a general exclusivity theorem.

The generated feature view selects all M6 command goals and the actual frame, transfer and
assembly declarations. Its proof-reference arrows come from Lean expressions; its authored
prerequisite arrows explain the intended assembly. The TYPES 2003 basis—Adams's feature
structure, Ballarin's preservation of context assumptions, and Wiedijk's significant proof
steps—is documented in the proof-view method (`git:98a29895b800556365a2edc9924f3ed12787b820:docs/research/2026-10-02-proof-feature-graph/method.md`).
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
  Schema bridge describes a record type as a struct (`schemaAlg.ty_record`, `src/Effect4/Schema/Bridge.lean`).
  The JSON codec encodes a record value by its own arm (`wireAlgebra.ty_record`,
  `src/Effect4/Schema/Codec.lean`). The claim `record-codec-layout` is proved by `decode_iff`.

#### 3. Project Definition and Judgment
Data plane conversions in Effect4 are exact embeddings between syntactic carriers and serializable formats:
```lean
theorem decode_iff {t : Ty} {j : Json} {v : Val} :
    decode t j = some v ↔ ∃ j', encode t v = some j' ∧ Codec.normJ j' = Codec.normJ j
theorem ofSchema_exact (r : Representation) : ∀ t, ofSchema r = some t → normS r = schema t
```
(`decode_iff`, `src/Effect4/Laws/Schema/Codec.lean`; `ofSchema_exact`, `src/Effect4/Schema/Bridge.lean`).

#### 4. Required Properties and Obligations
- **Program objects (`object-exact`, `object-bytes-exact`, `object-load-exact`, row 439)**: an object holds its signature and program.
  `Object.open_ofBuilt`, `Object.read_exact` and `Object.load_bytes` state the laws in `src/Effect4/Laws/Api/Object.lean`.
  They serve R13 with compatibility role. Byte retraction requires the encoded value's `Val.WF`.
  Program admission, exact node reading and hashing retain their existing owners.
  Equal references imply equal objects or an exhibited collision, without a hash injectivity assumption.
  These laws establish no cross-layout migration, host execution or persistence property.
- **Service-role reading (`service-view-printed`, `service-view`, rows 439 and 440)**: one profiled check separates role formation from target naming.
  `Program.serviceFaultIn_tsProfile_iff` and `Program.entriesOf_isSome` state the properties in `src/Effect4/Laws/Codegen/Services.lean`.
  Their roles are compatibility and adequacy, respectively. They serve R8's service reading and printer compatibility.
  TypeScript success is domain success and TypeScript's naming conditions. Domain success gives readable service entries.
  Neither property names the refusal the printer reports, target compilation or host behavior.
- **The tool wire's JSON profile (`codec-profile-retains-value`, seams S3b)**: a successful guarded JSON write
  reads back as the original canonical value. `Tool.CodecProfile.write_read` states it in
  `src/Effect4/Laws/Tool/CodecProfile.lean`. The profile refuses an option whose item can print null.
  It serves R12 and establishes no total writing, raw JSON text identity or native parser correctness.
- **Stored byte reading (`cas-node-read-exact`)**: every successful `Node.read` returns an exactly encoded node.
  The pointer is `Node.read_exact` (`src/Effect4/Store/Domain/NodeRead.lean`), with compatibility role.
  This law does not establish admission of node values into the store graph.
  It establishes no hashing, capacity or persistence property.
- **Typed stored reading (`cas-get-exact`)**: a successful `Cas.get` names the carrier's exact resident node.
  The pointer is `Cas.get_exact` (`src/Effect4/Store/Domain/Cas.lean`), with compatibility role.
  Version, kind, per-value specification, and canonical payload checks retain the genesis exception.
  The replay parameter stays explicit.
  The law establishes no atomicity or admission of node values into a store for an arbitrary interpreter.
- **Content handles (`cas-admission-handles`)**: every successful node insertion passes the kind's handle rule before edges and residency.
  The pointer is `putNode_ok_handleFree` (`src/Effect4/Store/Domain/Store.lean`), with preservation role.
  `Store.Sound.handles` and accepted words carry this rule; no host persistence or progress claim follows.
- **`cas-advance-head`**: Changed accepted root moves check the complete expected head and increase its generation exactly once.
  The pointer is `advance_head` (`src/Effect4/Store/Domain/Cas.lean`), with compatibility role.
- **`cas-advance-stale`**: A stale complete expected head refuses before every target or policy check.
  The pointer is `advance_stale` (`src/Effect4/Store/Domain/Cas.lean`), with compatibility role.
- **`cas-advance-duplicate`**: An identical complete target retains the exact store and generation.
  The pointer is `advance_duplicate` (`src/Effect4/Store/Domain/Cas.lean`), with compatibility role.
- **`cas-journal-fast-forward`**: A changed accepted journal target reaches the prior head through designated parent fields.
  The pointer is `journal_ff` (`src/Effect4/Store/Domain/Cas.lean`), with preservation role.
- **`cas-commit-grows`**: Accepted transactions retain every earlier resident at its digest.
  The pointer is `commit_grows` (`src/Effect4/Store/Domain/Cas.lean`), with preservation role.
- **`cas-commit-bytes`**: Reading an earlier resident after an accepted transaction returns the same node.
  The pointer is `bytes_never_change` (`src/Effect4/Store/Domain/Cas.lean`), with preservation role.
- **`cas-commit-reads`**: Every submitted node reads back after an accepted transaction; conflicts refuse.
  The pointer is `commit_reads` (`src/Effect4/Store/Domain/Cas.lean`), with compatibility role.
- **`cas-interrupted-closed`**: An accepted cut from a closed store retains node closure after complete transaction validation.
  The pointer is `interrupted_closed` (`src/Effect4/Store/Domain/Cas.lean`), with preservation role.
- **`cas-interrupted-roots`**: An accepted cut retains the exact old root table or returns the exact committed store.
  The pointer is `interrupted_roots` (`src/Effect4/Store/Domain/Cas.lean`), with compatibility role.
  These transaction laws establish no host persistence, crash, or progress property.
- **The result envelope (`cas-result-envelope`, seams ST3)**: a node answers a designated query exactly when it encodes that query's version-0 `Answered` envelope at the common specification.
  The pointer is `Node.resultQuery?_eq_some_iff` (`src/Effect4/Store/Domain/Action.lean`), with compatibility role.
  The designated query is the envelope's query field, never a reference inside the output.
  It establishes no result truth, host determinism, or hash injectivity.
- **One result per query (`cas-result-once`, seams ST3)**: two bindings of a reached store that answer one designated
  query hold the same node. The pointer is `Cas.result_once` (`src/Effect4/Laws/Store/Results.lean`), with preservation role.
  Insertion, word admission and verification apply one result rule, `resultFault`, which scans every binding.
  A wrong first result can satisfy the rule; it establishes no result truth, host determinism, progress, or hash injectivity.
- **Resident node identity (`cas-resident-injective`)**: two nodes resident at their own equal addresses in one store are equal.
  `address_inj_resident` (`src/Effect4/Store/Domain/Store.lean`) keeps both lookup premises.
  It assumes no hash injectivity and establishes no cross-store equality or host persistence property.
- **Exactness modulo key sorting (`decode-iff`)**: JSON decoding is exact modulo `normJ`
  (`decode_iff` (`src/Effect4/Laws/Schema/Codec.lean`)).
- **Retraction on codec-admitted values (`decode-encode`)**: Assume a canonical type (`CTy`).
  Fix a value passing its shape check and codec admission (`Ty.isCodecValue`).
  Decoding its encoding recovers the value (`decode_encode`, `src/Effect4/Laws/Schema/Codec.lean`).
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
- **The typed print erases to the print (`typed-print-erasure`)**: The typed print writes type
  arguments at two places.
  One is a row call whose request the row check joins, and one is an approved eliminator site.
  The named erasure removes exactly those arguments (`eraseJoinArgs`).
  It keeps an operation's own arguments and the stored type annotations.
  At a readable program and a lawful spelling, a successful typed print erases to the print,
  byte for byte (`eraseJoinArgs_printTyped`, `src/Effect4/Laws/Codegen/PrintTyped.lean`).
  A program with no such call and no such site has the typed print that is its print
  (`printTyped_eq_print`, the claim `typed-print-connector`).
  It establishes nothing that tsgo accepts and nothing of a run of the printed program.
  The tsgo checks of the printed sites are finite checks (`make check-ts`).
- **A module with a definition block reads back (`module-defs-round-trip`)**: The module
  printer prints each definition as a constant (`printModule`, `src/Effect4/Codegen/Print.lean`).
  The constants stand before the layers and the main declaration.
  A definition is an arrow from its request, with its declared result type, around a
  suspension of its body.
  Each program parameter follows the request as a function named by its declaration (`paramType`, slice HO-3a).
  Its run prints as a call of that name.
  An invocation prints as the definition's name applied to its request.
  An invocation with programs prints as that name applied to its request and programs.
  Each program prints as an arrow of the binder due at the call (`printInvoke`, slice HO-3b).
  It reads back under the block's laws of invocations (`LawfulInvokes`).
  A name spells its definition. No domain row carries a program-taking definition's name.
  The statement fixes declarations with readable columns, a canonical requirement row and names
  with no layer path (`DefDecl.readable`).
  A header reads its columns under the module's payload classes (`readDefHead`).
  So a column that names a class reads as the class's record.
  The header's requirement row reads back by the requirement reader (`readKeys`).
  A module's file declares its rows' services after its classes (`ModuleEmission.file`).
  The file reader checks each against the table's services, so it reads them back exactly
  (`readRowServices_rowServiceDecls`, `readRowServices_exact`,
  `src/Effect4/Laws/Codegen/RowServices.lean`).
  Then the file reads back to the program (`ModuleEmission.readFile`).
  The block's module layers print after the services, as constants named by their paths
  (`printModuleLayers`), and a reference to one prints as that name.
  Each body reads back at the signature its parameters extend, through the spelling map its
  parameters' names extend (`paramsSpell`). A body's own hoisted layers print as path-named constants at its suspension's top (`printDefs`, `suspension`).
  Each run of the body makes its own layer objects, as rc.112 builds one object per body evaluation. They read
  back at the body's signature (`bodyDeclOf`; row 341, step 3b).
  The main program, each layer and each module layer read back at the block's signature,
  through the block's spelling map (`defsSpell`).
  Both maps are lawful by one law of named rows (`LawfulSpelling.extend`,
  `src/Effect4/Laws/Codegen/Definitions.lean`).
  Each module layer's name decodes to its path.
  Then the module reads back to the program, its module layers rebuilt in order
  (`readModule_printModule_defs`, `src/Effect4/Laws/Codegen/Module.lean`; slice PROC-3, row 341).
  The block's spelling map is lawful under the signature's invocation laws and readable names
  (`LawfulSpelling.withDefs`, `src/Effect4/Laws/Codegen/Definitions.lean`).
  The native signature and the printer's name check give both (`nativeCalls`,
  `defsNamed_of_fault`).
  So the program interface's module round trip holds for a program with a block
  (`Api.printModule_roundTrip`, `src/Effect4/Laws/Api/ModuleReadable.lean`), the claim's pointer.
  The module that ships prints its program pieces by the typed print, and the module reader
  reads them after the named erasure.
  The module laws are stated of any lawful pair of a piece printer and a piece reader
  (`readModuleWith_printModuleWith_defs`, `PiecesLawful`).
  `readModule_printModule_defs` is the plain pair's instance.
  The printer refuses an empty block, and a reference out of its scope by its target
  (`Eff.inScope`).
  The application face refuses an invocation whose programs need a service, at its path
  (`PrintRefusal.callbackRequirement`): the printed header closes a parameter's row as `never`.
  It establishes nothing that tsgo accepts and nothing of a run of the printed module.
  The truth lane runs the block programs on the pin, a finite check (`make check-ts`).
  Three counted programs compare a body's own layer builds with rc.112.
  Two calls build twice. One call providing its layer twice by reference builds once.
  A call nested in another through its passed program builds twice.
- **The reader reads the typed print (`typed-print-read`)**: The statement fixes a readable
  program and a lawful spelling.
  After the named erasure, the reader reads a successful typed print back to its program
  (`readTyped_printTyped`, the same file).
  It transports the existing `read_print`, and `readTyped_exact` transports `read_exact`.
  The raw reader still refuses an inserted argument before the erasure.
  No equality of raw foreign spellings follows.
- **The reader takes any binder names (`binder-names-read`)**: An author names binders as they
  like (decisions row 418, release item 3).
  The reader reads the printer's text as it stands (`readMintedAt`, `src/Effect4/Codegen/Read.lean`).
  It reads any other text after the renaming of its binders to the printer's names.
  The renaming is the reader's named normaliser (`Rename.expr`, `src/Effect4/Codegen/Rename.lean`).
  Each use resolves to its nearest binder, by the authoring scope reader's rule (`Authoring.Names.resolve`).
  The lexical scope is TypeScript's, except that a layer clause closes it and a call's head is a name.
  A use before its block's declaration is refused, as the source binding analysis refuses it.
  A text whose binders rename to the print of a readable program reads (`read_renamed`,
  `src/Effect4/Laws/Codegen/ReadPrint.lean`).
  It reads to that program, or, when the text is itself a print, to the program it prints.
  `read_print` keeps its statement.
  `read_exact` holds under the normaliser: the text is the print, or the renaming writes the print.
  It establishes nothing that tsgo accepts.
  The TypeScript reader's agreement is a finite check (`ts/eff/test/read.test.ts`).
- **A modeled value survives JSON (`modeled-codec`)**: Take a modeled value at the normal form
  of its type. Decoding its encoding and reading it back answers the value
  (`Modeled.codec_roundtrip`, `src/Effect4/Laws/Schema/Modeled.lean`).
  Membership comes from `modeled-membership`, and the step is `decode-encode`.
  Codec admission at the value (`Ty.isCodecValue`) stays a premise: a natural above 2^53
  inhabits `nat` and has no exact JSON image.
  It establishes no TypeScript codec and no target execution (decisions row 330).
- **A field reference is a lens on the record frame (`record-field-laws`)**: A field reference
  is a position in a record's field list (`FieldRef`, `src/Effect4/Schema/FieldRef.lean`).
  On carriers it is a lawful lens, at every identity context, and its writes at two positions
  commute.
  For a record with ascending names, the machine's read at the reference's name reads the
  field's encoding.
  The machine's overwrite at that name writes the record that the reference's write gives
  (`FieldRef.frame_laws`, `src/Effect4/Laws/Schema/FieldRef.lean`).
  It establishes nothing of an optional field (decisions row 330).

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
  Subtyping*, §16.2 *Algorithmic Typing*, §16.3 *Joins and Meets*, audit T10, T50, T51). Soundness and completeness relative to the declarative subtyping judgment, and join-semilattice properties.
- **Set-Theoretic & Semantic Subtyping**: Giuseppe Castagna (2024, *Programming with Union, Intersection,
  and Negation Types*, audit P6, C6). Subtyping in the presence of union and bottom types.

#### 2. Effect4 Adaptation, Assumptions, and Exclusions
- **Adapting Preorder to Canonical Forms**: `Ty.subN` computes subtyping by evaluating raw subtyping `sub`
  on normalized canonical forms `Ty.normalize`. Canonical types `CTy` form a bounded join-semilattice with `Ty.join`.
- **Exclusion & Repair of Raw Subtyping (Row 137, `E4-TYPED-CE-009`)**: Raw `sub` does not distribute products
  over unions; subtyping equivalence and comparisons are defined through `subN`.
- **Exclusion of Function Types (Row 163)**: No function arrow types exist in `Ty`; arrow subtyping is excluded.
- **Row templates and the match (row 42; the state plan's T3a)**: A row's columns may hold parameters.
  The match by bounds (`Bounds.matchB`) binds each parameter at the join of its lower bounds.
  It keeps the bindings exactly when the request is below the template's instance, both sides normalized.
  The guard is the law (`Bounds.matchB_sound`), so the match is sound whatever it binds.
- **Records, maps, tuples and applications (rows 119, 162)**: the constructors are in `Ty`.
  `Ty.sub` compares records with identical canonical names and optionality field by field, covariantly, without a width rule.
  It compares maps exactly in the key and covariantly in the value. It compares equal-length tuples pointwise.
  It compares applications of one name and arity argument by argument, using each argument's declared variance (`argVariance`). The laws below
  quantify over every `Ty`, so they cover these constructors.

#### 3. Project Definition and Judgment
The static type language `Ty` possesses a decidable subtyping preorder `Ty.subN` evaluated on normalized forms:
```lean
def subN (a b : Ty) : Bool := sub a.normalize b.normalize
theorem subN_equiv_iff (a b : Ty) : (subN a b = true ∧ subN b a = true) ↔ a.normalize = b.normalize
```
(`src/Effect4/Laws/Program/TypeAlgebra.lean`). Canonical types `CTy` form a bounded join-semilattice.

#### 4. Required Properties and Obligations
- **Raw formation (`raw-formation`)**: The raw check agrees with distinct record names, the admitted map-key predicate,
  a deferred's admitted error column and the variable rule.
  Rows 192 and 193 require this check before normalization at each checked public boundary.
  Open map keys and open error columns are deferred only in row templates.
  A type variable is formed in a template only (row 288, point 6 a).
  A row's column is a template site, and a program's annotation is not.
  A declared service carrier is a strict formation site, and no template (row 297).
  Formation establishes no inhabitance, codec admission or execution property.
  The generated argument reader retains the exact ordered annotation sequence, including each argument position.
  `Formation.programAnnotations_eq_view` connects it to the existing view in `src/Effect4/Program/Formation.lean`.
  This connector serves raw formation and the closed-type proofs; it establishes no native translation theorem.
- **Closed types of the checker (`checked-types-closed`)**: A formed program that the checker admits has closed
  types (`check_closed`, `src/Effect4/Laws/Program/Typing/Closed.lean`; seat FORM).
  The statement fixes a closed environment and a typing signature with closed atoms and closed service carriers.
  It asks nothing of a row: the row rule checks strict formation of each instantiated column.
  The whole-program checker has the same property with no premise on a layer reference (`typeOfProgram_closed`).
  An admitted program has closed types with no premise (`AdmittedProgram.closed`).
  The checker alone does not have it: it types a stated cursor at a type that is not closed.
  It establishes no closed type of a sketch with a gap, and nothing of a run.
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
- **The complete match of a template by bounds (`template-match-complete`)**: The statement fixes a
  template in the reach of the laws (`Bounds.TemplateOK`).
  Such a template is its own normal form, is admissible, and holds no nominal reference.
  The match by bounds joins the lower bounds that a request offers each parameter.
  It keeps the bindings where the request is below the template's instance at them.
  A normal request below some instance of the template then has a match, from any seed that the
  instance agrees with.
  No premise asks where a parameter first occurs, and none asks where `never` stands.
  It is proved (`Bounds.matchB_complete`, `src/Effect4/Laws/Program/Bounds.lean`; slice MATCH).
  The match is sound by its guard (`Bounds.matchB_sound`), and its bindings are the least
  (`Bounds.matchB_least`).
  An argument list is checked at one, final list of bindings (`Bounds.matchArgsB_sound`), and
  smaller arguments have a match with smaller bindings (`Bounds.matchArgsB_monotone`).
  Every template of the tree is in reach, as a finite check (`Test/Program/BoundsControls.lean`).
  The row check and a binder term read the match by bounds with no guard (slice UNGUARD).
  The TypeScript printer writes a row's type arguments where the row check joins the request
  (`typed-print-connector`).
  It establishes no match under a union head or a nominal reference of a template, and no
  completeness of the checker against `HasTy`.
  It establishes nothing of tsgo's inference.
  The printed type arguments and the prelude's declarations answer to that.
  The truth lane tests them on finite programs.
- **Minimal type slices of a monotone view (`slice-lattice-minimal`)**: The statement fixes a view.
  This is a monotone map from one program's type slices to a preorder of types.
  A type slice is the list of its kept sites, and a smaller type slice keeps less.
  A query is valid for a type slice when the slice's type is at or above it.
  A minimal valid slice exists below each valid slice, and the one-pass descent returns one.
  A refined query has a minimal slice below a minimal slice of the wider query.
  The join of two valid slices is valid for the join of their queries.
  It is proved (`SliceView.lattice_minimal`, `src/Effect4/Laws/Slice/Lattice.lean`; seat LATTICE).
  The statements follow Theorems 4.5, 4.6 and 4.7 of the paper on bidirectional type slicing
  (`vendor/papers/program-graphs/README.md`).
  It establishes no monotone type map of a real program, no least slice and no minimum-size slice.
  A view takes one column of the checker's type, and it owes one fact, its monotonicity.
- **A rule that reads a union member by member (`union-rule-lift`)**: The statement fixes a member
  rule: a function from a type to an optional answer.
  It fixes a carrier of answers with a least answer and a join: a type, or a pair of types.
  The lifted rule asks the member rule at every union member of the target's normal form.
  It joins the answers, and one refusal refuses the target.
  It answers the least answer at `never`.
  At one normal union member it is the member rule, up to the join with the least answer.
  Two types with one normal form have one answer.
  Assume the member rule is monotone on normal union members.
  If a larger target answers, a smaller target answers too, and its answer is smaller.
  A property of a value and an answer that the join keeps on each side passes from the union
  members to the lifted rule.
  It is proved (`UnionRule.lift_laws`, `src/Effect4/Laws/Program/UnionRule.lean`; seat UNION).
  Three more statements stand beside it, each proved in the same file.
  An eliminator of one covariant constructor owes three member facts, and the order laws follow
  (`Eliminator`).
  Its lifted rule answers exactly below the constructor's image, in `Ty.subN`
  (`Eliminator.adjoint`).
  At types, a map with the four properties of the lifted rule is the lifted rule (`lift_unique`).
  The same holds at a pair of types (`lift_unique_pair`).
  The join law is an equation at a type and at a pair of types, since each join is a normal type
  (`lift_union_eq`, `lift_union_eq_pair`).
  It is an equation at every carrier whose order is antisymmetric (`lift_union_eq_of_antisymm`).
  The checker's order on raw types is not antisymmetric, so the two first forms are no case of the
  third (`Test/Program/Order.lean`).
  The order is read in Lean core's classes.
  A carrier with those classes, a least answer and `join = max` is a carrier of answers
  (`AnswerOrder.ofCore`).
  On raw types the checker's order is the order of canonical types, by definition (`subN_iff_le`).
  An eliminator's adjoint form uses `≤` there (`Eliminator.adjoint_le`).
  A join in those classes has its laws once (`src/Effect4/Laws/Program/Order.lean`): the equations
  of `CTy` and of `ErrTy` are one application each.
  The two record rules are its instances, and each equals its earlier definition by `rfl`
  (`Test/Program/UnionRule.lean`).
  It establishes no conversion of an eliminator, no `checker-monotone` and nothing at an
  invariant position.
  The upper form is false in the raw order `Ty.sub`.
  The field read has no upper form: the order has no width rule (decisions row 178).
- **A converted eliminator is the full fallback of its member rule (`union-rule-extend`)**: The statement fixes an eliminator.
  This is a member rule with the three facts of `Eliminator`.
  The full fallback is the member rule's own answer where the member rule answers at the raw
  target.
  Elsewhere it is the lifted rule, which reads every union member of the normal form.
  It agrees with the member rule, so no target that the by-shape function answered moves.
  It is the lifted rule where the member rule refuses.
  It keeps every answer of the earlier guarded rule (`extendAll_of_extend`).
  It answers a least answer at `never`.
  Its answer `a` puts the target below `C a`, in `Ty.subN`.
  An answer `b` is above `a` exactly when the target is below `C b`.
  A retained union member that the member rule refuses refuses the whole target.
  It is proved (`UnionRule.Eliminator.extendAll_laws`, `src/Effect4/Laws/Program/UnionRule.lean`;
  slice P2b).
  It is monotone at every smaller type (`Eliminator.extendAll_mono`).
  Its answer equals the lifted rule's answer up to the order (`Eliminator.extendAll_lift`).
  The fiber, list and exit rules are instances (`fiberTy`, `src/Effect4/Program/Typing/Rules.lean`;
  `Checker.listOf?` and `Checker.exitOf?`, the same file; decisions row 304).
  The cause rule reads two heads, so it is no eliminator of one constructor.
  It is the full fallback of `Member.cause`, with four member facts of an upper type
  (`causeInputError_upper`).
  The option rule of `Decision.arms` reads the normal form alone, so it is the lifted rule of
  `Member.option` (`optionTy`, `src/Effect4/Program/Decision.lean`).
  It is the earlier normalized-head rule where the normal form has one member
  (`optionTy_eq_normal`).
  The guarded rule's laws stay for their earlier consumers (`Eliminator.extend_laws`).
  It establishes no `checker-monotone`, nothing that tsgo accepts, and nothing of another rule.

### 2.7 Concept 7: Initial Algebras & Catamorphic Folds (`initial-algebras-folds`)

#### 1. What the Literature Defines
- **Initial Algebra Semantics**: Meijer, Fokkinga, Paterson (1991), *Functional Programming with Bananas, Lenses, Envelopes and Barbed Wire*.
  FPCA '91, LNCS 523, pp. 124–144 (audit P24, C7, C14).
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
- **Free-Category Path Interpretation (Row 48)**: Saved-stack judgments are factored through `Contracts.FramePath Edge`, a Prop-valued typed-path relation over frame lists interpreting composition through existential middle types. Identity (`nil`), append (`append`), splitting (`split`), and transport along edge implications (`map`) are proved once. Concrete stack judgments (`HostStack`, `PositionStack`) instantiate `FramePath` over `HostEdge` and `PositionEdge`. Two conversion theorems connect the unchanged `StackAccepts`. Conversions and transports use functorial edge maps (`FramePath.map`).

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
  (`cata_eff_congr_on` (`src/Effect4/Program/Typing/SignatureSupport.lean`)).
- **Traversal census maintenance**: 100% fold coverage enforced by `#traversal_census`.
- **Operation data scoped (`operation-data-scoped`)**: the scope fold decides `perform` from the operation data and request (`Eff.perform_scoped_iff`, `src/Effect4/Laws/Program/Authoring.lean`).
  The alphabet's `ScopedOp` reads the operation data. Scope is not typing.
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
- **A sketch is a conservative extension (`sketch-conservative`)**: For programs performing no hole row, every hole table gives the same checker result, refusals included
  (`holes_conservative`, `src/Effect4/Laws/Program/Sketch.lean`). It is the reflection of an
  extension of the typing signature, at a hole table. It says nothing of a program that
  performs a hole.
- **More holes keep a sketch (`sketch-weakening`)**: a sketch that the checker admits stays
  admitted at its type when more holes are declared. The checker reads the rows of the holes
  that the sketch performs and no later row
  (`sketch_weakening` (`src/Effect4/Laws/Program/Sketch.lean`)).
- **The hole's rule (`hole-rule`)**: Consider a row with a unit request and closed, formed columns.
  Its hole has the declared type in every environment (`Sketch.hole_hasTy`, `src/Effect4/Laws/Program/Sketch.lean`). The typing judgment gains no
  rule. The three properties establish no admission of a sketch to a later stage, no law of
  filling a hole and no run.
- **A definition block is a conservative extension (`defs-conservative`)**: a program that
  invokes no definition is checked the same at any block's signature
  (`defs_conservative` (`src/Effect4/Laws/Program/Definitions.lean`)). Refusals are included.
  The block's signature
  changes an invocation's domain bit and row only, so no service key is assumed typed. It says
  nothing of the block's own bodies, and nothing of a run.
- **The invocation's rule (`invocation-rule`)**: at a block's signature, an invocation has the
  type of its definition's declared row, at its request's type
  (`invoke_hasTy` (`src/Effect4/Laws/Program/Definitions.lean`)). The row is read in normal
  form. It is the rule of a `perform`
  read at that signature, and the typing judgment gains no rule. The declarations are closed;
  no generic definition is typed.
- **The module's check (`module-check`)**: the whole module's check agrees with the module
  judgment at the root, both ways (`checkModule_sound` and `checkModule_complete`
  (`src/Effect4/Laws/Program/Definitions.lean`)). A block stands at the root only. The checker
  refuses a block below the root. Neither the rule nor the check says that a declared row is
  inhabited, or that a body terminates.
- **`checker-combine-deps`**: The combined actual dependency answers equal the complete verdict. This includes source layer projection for every module and part key.
  The pointer is `Check.combine_deps` in `src/Effect4/Laws/Program/CheckAgreement.lean`.
- **`checker-placed-verdict`**: A part verdict placed at a base equals checking that part at the base, including the complete annotation table.
  The pointer is `Check.run_placed` in `src/Effect4/Laws/Program/CheckAgreement.lean`.
- **`checker-part-extension`**: A positive part verdict agrees at an extending signature, including the complete annotation table. Negative and module reuse are excluded.
  The pointer is `Check.run_part_extends` in `src/Effect4/Laws/Program/CheckAgreement.lean`.
- **`checker-explanation-replays`**: A selected local explanation names an actual dependency with its exact placed refusal. Aggregate failures need no invented part.
  The pointer is `Check.explain_replays` in `src/Effect4/Laws/Program/CheckAgreement.lean`.
  These compatibility properties serve R14 and establish no program admission, progress, or native execution.
- **Source sessions and accepted document actions (seams S1)**: The following properties serve R14.
  Every conditional property retains its stated premises.
  They establish no program admission, progress, liveness, or native execution.
- **`source-feed-coherent`**: A successful feed preserves the source table under initial coherence and the selected policy.
  The pointer is `SourceSession.feed_coherent` in `src/Effect4/Laws/Program/SourceTable.lean`.
- **`source-feed-edit`**: A successful feed retains the application and exact edit; an invalid edit retains the source, and a valid edit returns its candidate.
  The pointer is `SourceSession.feed_keeps` in `src/Effect4/Laws/Program/SourceTable.lean`.
- **`source-feed-draft`**: Every draft from a coherent source agrees with the existing expanded edit observation and exact source projection.
  The pointer is `SourceSession.feed_draft` in `src/Effect4/Laws/Program/SourceTable.lean`.
- **`source-feed-keep-exact`**: A successful nonroot keepExact feed retains root and local types, using the exact whole-expansion guard for splice or recheck.
  The pointer is `SourceSession.feed_keepExact` in `src/Effect4/Laws/Program/SourceTable.lean`.
- **`source-feed-root`**: Every root edit with a candidate equals the entire checked module recheck, including actual dependency answers.
  The pointer is `SourceSession.feed_root` in `src/Effect4/Laws/Program/SourceTable.lean`.
- **`source-document-coherent`**: Every sealed document has its exact source table, without a separate coherence premise.
  The pointer is `Doc.coherent` in `src/Effect4/Laws/Program/SourceTable.lean`.
- **`source-session-draft-transport`**: Every old application, sketch, and edit list has canonical draft replay with the exact edited sketch, source table, refusals, and root observation.
  The pointer is `SourceSession.replay_drafts_view` in `src/Effect4/Laws/Program/SourceTable.lean`.
- **`source-document-replay`**: Appending an action replays through the same interpreter and exact history ledger.
  The pointer is `Doc.step_replay` in `src/Effect4/Laws/Program/SourceDocument.lean`.
- **`source-document-atomic`**: A refused step offers no replacement document, so the caller retains the original document.
  The pointer is `Doc.step_refuses` in `src/Effect4/Laws/Program/SourceDocument.lean`.
- **`source-document-step`**: A successful step from a coherent document retains its origin and application, appends one action, and remains coherent.
  The pointer is `Doc.step_coherent` in `src/Effect4/Laws/Program/SourceDocument.lean`.
- **`source-document-commit`**: A successful keepExact or recheck commit is positive, with initial positivity required for keepExact.
  The pointer is `Doc.commit_sound` in `src/Effect4/Laws/Program/SourceDocument.lean`.
- **`source-document-local-keep`**: A successful single nonroot kept change retains the exact root and local observations, including an initially refused root.
  The pointer is `Doc.commit_one_keepExact` in `src/Effect4/Laws/Program/SourceDocument.lean`.
- **`source-document-single-transport`**: The old single-edit observation holds under its exact replacement and initial positive-root premise for keepExact.
  The pointer is `Doc.commit_single_sound` in `src/Effect4/Laws/Program/SourceDocument.lean`.
- **`source-document-revert`**: An accepted action and its immediate selected-entry revert restore the prior program and retain appended hole rows.
  The pointer is `Doc.revert_program` in `src/Effect4/Laws/Program/SourceDocument.lean`.
- **`kept-fill-reference`**: For coherent sources at nonroot addresses, keepExact acceptance equals old certification when both base and filling have no references.
  The pointer is `kept_eq_certified` in `src/Effect4/Laws/Program/FillSet.lean`.
- **`pending-fill-construction`**: Every sealed pending set has conflict-free, incomparable entries certified by the anchor's keepExact feed.
  The pointer is `FillSet.add_wf` in `src/Effect4/Laws/Program/FillSet.lean`.
- **`pending-fill-publication`**: A successful publication agrees with old materialization at its exact coherent anchor, under positive-base and reference-free premises.
  The pointer is `FillSet.publish_eq_materialize` in `src/Effect4/Laws/Program/FillSet.lean`.
  These R14 properties establish no program admission, progress, or native execution.
- **The replacement law (`typed-replacement`)**: a typed node splits at an address of a program
  into an environment and a type of the focus. Every program of that type in that environment
  stands in the focus's place, under every extension of the typing signature
  (`NodeHasTy.replace` (`src/Effect4/Laws/Program/Typing/Replace.lean`)). Its six instances are
  the six typing judgments, and the judgment gains no rule. It is the law of the two edits of a
  sketch (`Sketch.check_fill`, `Sketch.check_omit` (`src/Effect4/Laws/Program/Sketch.lean`)).
  A filling has no further premise. An omission keeps the whole type where the focus's columns
  are closed, formed and in normal form. The focus's type is kept exactly: the law says nothing
  at a type that is equal only after normalization, and nothing of behaviour. The environment
  and the type are existential there, and the focus function answers them.
- **The focus function (`focus-function`)**: At a program address in a typed node, `Node.envAt` answers the focus environment.
  `focusAt` answers its type there (`src/Effect4/Program/Typing/Focus.lean`). The replacement law
  holds at that pair with no existential (`NodeHasTy.replace_envAt`
  (`src/Effect4/Laws/Program/Typing/Replace.lean`); `check_replace_focusAt`
  (`src/Effect4/Laws/Program/Typing/Focus.lean`)). The step has one case for each arm of
  `Node.child`. It answers nothing after a sibling that the checker refuses. It stores
  nothing, and one answer costs up to one check of the program. One pass answers every
  address (`annotate-table`, below).
- **The address table (`address-table`)**: the table has one entry for each address of a node,
  and no other (`mem_addresses_iff` (`src/Effect4/Laws/Program/Typing/Table.lean`), from
  `Node.mem_foldList_iff` (`src/Effect4/Laws/Program/PathFold.lean`)). An entry of a program
  holds the typing environment that the step function answers, and the checker's answer there
  (`table` (`src/Effect4/Program/Typing/Table.lean`)). The distinct refusals start with the located refusal of `explain` (`refusals_head`).
  Their list is empty exactly when the checker admits the program (`refusals_nil_iff`). An entry after a refused sibling is
  not reached. The table is a specification, and each of its entries costs up to one check
  of the program. No law orders the refusals after the head, and no theorem states the frame
  of an edit.
- **The table in one traversal (`annotate-table`)**: `annotate` is the checker's seven
  functions with a record at each node (`src/Effect4/Program/Typing/Annotate.lean`). It
  answers the address table at every program, entry for entry and in its order
  (`annotate_eq_table` (`src/Effect4/Laws/Program/Typing/Annotate.lean`)). Each node's checker
  arm runs once, and a child's environment comes from the answers before it. Past a refused
  read the subtree is not reached, as in the table. No theorem counts the cost. The left
  child's entries are copied at each node.
- **The slot table (`term-slot-environment`)**: a term has no address. Five term slots read an
  extension of their node's typing environment, and the slot table answers it
  (`Node.extSlotEnv` (`src/Effect4/Program/Typing/Table.lean`)). On a typed node the term in
  each slot has a type there (`hasTy_extSlotEnv`
  (`src/Effect4/Laws/Program/Typing/Table.lean`)). The property does not say that the
  environment is the only one, and it says nothing at a node that the checker refuses.
- **Local agreement of a type-fold cache (`fold-cache-local-agreement`)**: a cache holds
  entries, each a source type and an answer, the newest first
  (`src/Effect4/Program/TyCache.lean`). `check` accepts entries whose children stand in earlier
  entries and whose answers meet the layer's local equation at their own sources. Every
  answer of accepted entries is `cata_ty` of the same layer at its source (`check_agreement`
  (`src/Effect4/Laws/Program/Folds/TyCache.lean`)). The equation reads the generated view, so
  a payload, a field name, a flag and the order of two children are part of it. `check`
  accepts the entries that `prepare` builds, so `answer` returns the fold at every type
  (`answer_eq`). The property establishes no speed and no reuse after an edit. It reads no
  typing judgment and no input that the layer inherits: the type is the whole key. Its consumer
  is slice D6 of `git:98a29895b800556365a2edc9924f3ed12787b820:docs/research/2026-10-09-program-graph-design.md`, serving R14.
- **A checked summary of cyclic dependencies (`dependency-summary-exact`)**: a finite graph
  gives each node its seeded labels and its ordered children (`Tools.Graph.Summary.Graph`,
  `tools/Tools/Graph/Summary.lean`). Cycles are allowed. A summary is a table with a distance
  for each node and label. `check` accepts a table when each seed and each child's label has an
  entry. Each entry must also be a seed, or have a child at a smaller distance. An
  accepted table holds an entry if and only if a directed path reaches a seed of the label
  (`check_summary_exact`). One distance per node would refuse valid summaries on a cycle, so a
  distance belongs to a node and a label. `#axiom_audit checked` runs this check over the axiom
  walk's answers and the graph they read (`checkDependencies`,
  `tools/ProofGraph/Summary.lean`). The property says nothing of the capture's fidelity to the
  Lean environment, and nothing of a theorem that a node names.
- **A checked reachability of a flow (`view-reachability-summary-exact`)**: the reach graph of a
  flow has a node for each item position below a bound (`Tools.View.Flow.reachGraph`,
  `tools/Tools/View/FlowReach.lean`). Each node seeds its own position. When `checkReach` accepts
  a table, the table reports a target at a source if and only if `Flow.Reach` leads there
  (`checkReach_exact`). An edge with an end at or above the bound is refused, since dropping
  it could lose a path. `ReachTable` answers directed queries under this law. The property
  establishes no schedule, no layout and no weak connectedness.

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
(`src/Effect4/Machine/Context.lean`). Layer composition and capability discharge are governed by `LayerTy`
(`src/Effect4/Program/Provision.lean`).

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
- **Build totality (`build-total`)**: Assume typed leaf semantics and a layer the checker types.
  It builds under every context satisfying its requirement row. The built context satisfies its output row.
  `build_total` states this in `src/Effect4/Laws/Program/BuildTotal.lean` (restored under decisions row 147). The machine's build refining `build` is the row's other half, still owed.
- **Layer sharing invariants (`layer-sharing-contract`)**: Dynamic layer memoization and sharing invariants
  (`LayerSharingContract.lean`). A build's key holds the layer's path and, inside a definition body, the running call (`Point.layerKey`, `src/Effect4/Program/Compile.lean`).
  A body's layer builds once per call, as rc.112 builds one layer object per body evaluation (decisions row 341, step 3). The memo table types a cell by its key's path alone (`LayerCellTyped`, `src/Effect4/Laws/Program/Typed/Adequacy.lean`).
  Every call of one body checks the layer at the body's one signature.

### 2.9 Concept 9: Host Session Protocol & Boundary (`host-session-protocol`)

#### 1. What the Literature Defines
- **Session Types & Propositions as Sessions**: Philip Wadler (2012 ICFP / 2014 JFP), *Propositions as Sessions*, JFP 24(2-3): 384–418 (audit P35, P41, C46).
  Honda, Vasconcelos, Kubo (1998), *Language Primitives and Type Discipline for Structured Communication-Based Programming*, ESOP '98 (audit P16, C9).
  Duality, session sequencing, and protocol safety.
- **I/O Automata & Labeled Transitions**: Lynch & Vaandrager (1995, *Forward and Backward Simulations I:
  Untimed Systems*, Information and Computation 121, pp. 214–233, audit C4, C47).
- **Comodels and runners**: four texts, each locator read in
  `git:98a29895b800556365a2edc9924f3ed12787b820:docs/research/2026-10-09-comodel-papers/README.md` (decisions row 338).
  Plotkin and Power (2008, *Tensors of Comodels and Models for Operational Semantics*, MFPS XXIV,
  ENTCS 218).
  Their Definition 3.1 defines a comodel of a countable Lawvere theory.
  Their section 4 defines the tensor of a comodel with a model.
  Uustalu (2015, *Stateful Runners of Effectful Computations*, MFPS XXXI, ENTCS 319) reads
  runners as comodels.
  His Proposition 3.1 puts monad morphisms from a theory's monad to the state monad of `C` in
  bijection with comodels on `C`.
  His section 5 separates running from handling.
  Ahman and Bauer (2020, *Runners in Action*, ESOP 2020) define runners in their section 2.2.
  Their Definition 2 defines a `T`-runner, whose co-operations land in a monad `T`.
  Their Proposition 3 puts monad morphisms from the free monad to `T` in one-to-one
  correspondence with `T`-runners.
  Setzer and Hancock (2005, *Interactive Programs and Weakly Final Coalgebras in Dependent Type Theory*,
  Dagstuhl Seminar Proceedings 04381).
  Their section 3 defines a dependent interface.
  It has states, the commands of each state, the responses to each command and the next state
  after each response.
  The note maps these definitions to the tree's declarations and proves nothing.

#### 2. Effect4 Adaptation, Assumptions, and Exclusions
- **Adapting 4-State Session Automaton**: A four-state protocol automaton governs interaction between the Effect4 runtime machine and external host.
  Its states are `.idle`, `.awaitingAsync`, `.parked` and `.terminated`.
- **A host is a comodel**: In the laws, a host of a row table is an
  `Effects.Comodel (RowSig table) σ` (`RowSig`, `src/Effect4/Laws/Program/DenoteRows.lean`).
  From a state of its own, it answers each operation with its next state, or gives `none`.
  The structure is `Effects.Comodel`, in the `effects` package's
  `Effects/Coalgebra/Comodel.lean` (decisions row 338).
  The reply tape is one host, `tapeHost` (`src/Effect4/Laws/Program/HostRuns.lean`).
  The comodel of the tape handler is `tapeHost` (`tapeHandler_eq_replies`, same file).
  So the meaning under a reply tape is a run of the call tree against that host.
  The stores are routed beside it (`rowsHost`, `meaningRows_eq_run`, same file).
  Under any host, the host's run of the call tree is the meaning under that host read as a
  handler (`hostRun_eq_meaningUnder`, same file).
  These laws model a host in Lean. They do not discharge host progress, which stays the
  external assumption below.
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
(`src/Effect4/Api/HostProtocol.lean`). External answers are submitted through `HostSession.submit` and applied via `HostSession.applyReply`.

#### 4. Required Properties and Obligations
- **Exact checker asks (`checker-ask-value`)**: Every certified oracle ask returns the exact uncached verdict.
  `Check.Checked.ask_value` states this property in `src/Effect4/Laws/Program/CheckAgreement.lean`.
  It serves R6 and R14; native execution and invocation counts remain outside its observation.
- **Checker substitution (`checker-oracle-agrees`)**: Every certified checker oracle equals the uncached checker.
  `Check.Oracle.eq_uncached` states this equality in `src/Effect4/Program/Check.lean`.
  Its agreement premise fixes the entire verdict, including the annotation table.
  Checked traces and learned memos contain only those answers; a hit rule carries its agreement law.
  This property serves R6 and R14 and excludes arbitrary native callbacks or forged checked packages.
  Generated interface tests check that host callers cannot construct those packages.
  Those finite tests establish no general native translation theorem.
- **Recorded runs have admitted histories (`run-admitted-history`)**: Every reached run holds its built program's call table and an admitted native history.
  `Run.reached_history` states the connection in `src/Effect4/Laws/Run/Frame.lean`.
  The history keeps the run's compile budget and records each accepted decision with its command budget.
  It covers arbitrary recorded commands and establishes no progress or outside-host behavior.
- **Each key once (`keys-once`)**: A reached run binds, submits and applies each key at most once,
  and applies no retired key.
  `Run.Reached s → (boundKeys s).Nodup ∧ (submittedKeys s).Nodup ∧ (appliedKeys s).Nodup ∧ ∀ k ∈ retiredKeys s, k ∉ appliedKeys s`
  (`session_keys_once` (`src/Effect4/Laws/Run/Journal.lean`)). It does not establish reply
  admission at the application, the retirement edge, the order of two applications, or which reply
  a host sends.
- **Allowed answer step (`allows-answer`)**: Async answering is an allowed transition from `.awaitingAsync`.
  (`allows_answer` (`src/Effect4/Laws/Run.lean`)).
- **Host reply commutativity (`reply-commute`)**: Independent host answers commute in session queues.
  (`reply_commute` (`src/Effect4/Laws/Api/HostSession.lean`)).
- **A reply that the session accepts fits (`session-success-prepared-membership`,
  `session-failure-shape-free`)**: A successful reply that the session accepts prepares a member
  of its selected shape-decided row.
  Where the row's own columns refuse it, the session admits the reply at its call's checked
  instance (`InstanceSuccess`, decisions row 323).
  A failing reply that the session accepts carries no reserved defect: the failure half of the
  statement `admit_sound` (decisions row 191, register line `E4-HOST-CE-008`).
  (`preflight_success_prepared_fits`, `preflight_failure_noShapeDefect`
  (`src/Effect4/Laws/Api/HostSession.lean`)).
- **A reply at its call's instance (`reply-at-call-instance`, `block-call-instance`)**: A reply
  admitted at its call's checked instance is a handle-free member of the instance's answer
  column.
  The machine prepares it unchanged, at a row whose answer column allocates nothing.
  A failing reply admitted there holds no reserved defect.
  The registration keeps its call's address, and the session reads the instance there from a
  table made once at open (`Run.reached_callInstance`).
  In a recorded, funded run that address holds a call of the operation
  (`Run.origin_addresses_call`, `src/Effect4/Laws/Api/SessionRef.lean`).
  On a program that the module check admits, the call instance answers at every call, with the
  call's operation (`programCallAt`).
  `HostSession.instanceAt_complete` supplies an instance at each call of an admitted program.
  `Run.reached_callInstance` reads that table in a reached run.
  Neither law says that the expansion of layer references keeps a call at its address.
  The second says nothing of a run (decisions rows 183, 323, 328 and 333).
  (`instance_prepared_success` (`src/Effect4/Laws/Program/Admit.lean`);
  `checkModule_programCallAt` (`src/Effect4/Laws/Program/Typing/Parts.lean`)).
- **A waiting run names its wait (`rows-loop-frontier`, `rows-loop-frontier-host`)**: Each law
  takes a recorded run of a `LoopedRows` program in `LoopedDataRows`.
  That fragment is the row fragment with loops, and the run is funded, at rest and driven by a
  host.
  Every call that the machine waits on is a host row.
  Past a budget bound, the detailed observation of the budgeted meaning under the run's reply
  tape waits at that row and request.
  It holds the machine's stores and reads the tape to its end.
  Take any host whose answers are the run's and which leaves the waited call unanswered.
  Past a budget bound, the meaning under that host waits at that call too, with the machine's
  stores.
  The host stays where the answers left it.
  The host's silence is a premise.
  A wait is a frontier, never a failure, and no progress claim follows.
  Neither law says anything of a fork, a scope or an interruption (slice L4,
  `git:98a29895b800556365a2edc9924f3ed12787b820:docs/research/2026-10-10-l4-frontiers.md`).
  (`Run.rows_loop_frontier`, `Run.rows_loop_frontier_host`
  (`src/Effect4/Laws/Api/SessionMeaningLoop.lean`)).
- **Frontier awaitHost inversion (`frontier-awaithost`)**: Machine awaitingAsync state matches frontier reason.
  characterization of frontier state matching `.awaitingAsync` (`observe_awaitingAsync_iff` (`src/Effect4/Laws/Api/Frontier.lean`)).
- **External host progress (`host-progress`)**: External driver progress assumed under `docs/core/host-boundary.md`.
- **Tool transitions (seams S3a)**: `Tool.serve` answers one request from a state kept as its accepted actions.
  An accepted action appends itself (`tool-serve-appends`); a refused request and every query leave the state unchanged
  (`tool-serve-refuses`, `tool-serve-query`). Any certified oracle serves the same answers and trace (`tool-serve-transparent`).
  A state's transcript replays to it (`tool-transcript-replays`). The theorems live in `src/Effect4/Laws/Tool/Serve.lean`.
  They serve R6 and R13 and establish no native execution, external-effect rollback or host progress.
- **Tool replies pair with requests (seams S3b)**: Every `Tool.serve` reply pairs with its request.
  `Tool.serve_answers` proves `tool-serve-answers` in `src/Effect4/Laws/Tool/Wire.lean`, by cases on each action and query branch.
  It serves R6 and establishes no JSON decoding exactness, native driver behaviour or host progress.
- **Workspaces over the store (seams ST4)**: a workspace persists as a chain of `WorkspaceEntry` nodes under a journal root
  `workspace/<name>`, never as derived state. Loading replays the chain through `serve` and compares each stored program.
  - `workspace-load-own` (`Exchange.load_own`): after an exchange commits an accepted action, loading the head it reports
    gives the state `serve` reached from the resolved base.
  - `workspace-commits-once` (`Exchange.apply_commits_once`): an accepted action commits one transaction; its last node is the
    entry, and its one move publishes it.
  - `workspace-refuses` (`Exchange.apply_refuses`): a query or a refused request returns the store it was given.
  - `workspace-entry-exact` (`WorkspaceEntry.ofVal_exact`): an entry's reader answers only its own tree.
  The laws are in `src/Effect4/Laws/Tool/Exchange.lean`. They serve R6 and R13, repeat no host effect, and claim no host progress.
- **Typed replay under session (`typed-replay-session`)**: Opening requires full admission at the application extended by the sketch's hole rows.
  `Api.Built.ofSketch_error_iff` states the exact refusal in `src/Effect4/Laws/Api/Built.lean` (`built-admission-exact`, R6 and R13).
  Each hole is a host row that the driver answers; a restore admits at the recorded application exactly (`Api.Built.ofProgram`).
  Restore replays ordered commands and retains recorded names, including an empty session name.
  `LiveRecord.restore_save` returns the exact saved run in `src/Effect4/Laws/Api/LiveRecord.lean` (`live-session-persists`, R6 and R13).
  Neither property establishes native package integrity, host reconnection, repeated effects, or progress.

- **Checked service sessions (`service-session-checked`, `service-session-retains`)**: `Object.session` writes a service's lifetime as the object's main program, data to data; `Api.Built.session` admits it.
  Success requires the session object, full program admission, and a requirement row closed modulo the signature: every key left is one the signature types.
  It retains declarations, bodies, module layers, named types, and service declarations.
  It appends rows and replaces the main program.
  `Built.session_ok_iff` and `Built.session_retains` state these properties in `src/Effect4/Laws/Api/Session.lean`.
  They serve R6 and R13. Neither establishes transport support, termination, or equality with the replaced main program's behaviour.

- **Queue and tensor equations (`queue-reactor`)**: `Reactor.queue_spec` has compatibility role and serves R6 and R13.
  It states the queue's two equations in `src/Effect4/Laws/Run/Runner.lean`.
  `Reactor.tensor_left` and `Reactor.tensor_right` are helpers of this claim in the same file.
  Their definitions are `Reactor.queue` and `Reactor.tensor` in `src/Effect4/Run/Runner.lean`.
  `ServiceSession.nextName`, `replyPrefix` and `isReplyRow` own the row spellings in `src/Effect4/Api/Session.lean`.
  The queue reads its current list from reactor state; its `requests` argument initializes nothing.

  ```text
  queue requests next v q    = some (success (head? q), tail q)
  queue requests reply_m v q = some (success unit, q)
  tensor r s row v (a,b)     = some (answer,(a',b))     if r row v a = some (answer,a')
  tensor r s row v (a,b)     = map (answer,b') ↦ (answer,(a,b')) (s row v b)  if r row v a = none
  ```

  The tensor equations act on separate state components.
  They realize the comodel tensor for disjoint supported rows; overlapping supports give the left answer priority.
  `Reactor` is partial over erased values, so its exit-answer interpretation uses `StateT σ Option`.
  The checked `Run` separately admits each answer.
  These equations establish no host progress, session/client agreement theorem, or state-monad interpretation of every `Eff` constructor.
  The to-do agreement on replies and final repository is finite evidence in `Test/Api/SessionContract.lean`.
- **Open part: a general client as a reactor**: No definition, proof pointer or planned goal exists for this property.
  A client is a program over service methods; the definition block handles those calls through its bodies.
  The required property serves R6 and R13: compare replies and application store under the generated session protocol.
  Running the session against the client as a reactor must agree with running the handled client against the application reactor.
  For the free-monad interpretation of those method calls, one-step unfolding gives these equations:

  ```text
  C : T_Σsvc 1
  next    (unit, return unit) = (none, return unit)
  next    (unit, m(a,k))      = (some (m,a), m(a,k))
  reply_m (e, m(a,k))         = (unit, k e)
  ```

  The equations cover legal alternating requests and matching replies; they define no response to a mismatched reply.
  The general client advances on reply, while the queue advances on next.
  Repeating next therefore distinguishes them: the general client repeats its request, while the queue consumes another item.
  A future simulation must relate these states under the generated protocol, not assert unrestricted reactor equality.
  Its definition needs the machine to step a client one method call at a time.
  `docs/research/2026-10-21-runner-slice/README.md` §2.5 records the design; no hosted stage lands here.

### 2.10 Concept 10: Translation & Simulation Metatheory (`translation-simulation`)

#### 1. What the Literature Defines
- **Compiler Correctness & Semantic Preservation**: Xavier Leroy (2009, *Formal Verification of a
  Realistic Compiler*, CACM 52(7), audit C10). Semantic preservation relative to the compiler correctness theorem relates source and target observations.
- **Forward & Backward Simulations**: Lynch & Vaandrager (1995, *Forward and Backward Simulations I:
  Untimed Systems*, Information and Computation 121, pp. 214–233, audit C4). Trace inclusion and simulation relations.
- **Coalgebraic Moore Behaviors**: Bart Jacobs (2012 draft, *Introduction to Coalgebra: Mathematics
  of State and Observation*, ch. 2, audit P17, C23). Deterministic behavior functors on decision words.
- **Syntactic Soundness**: Wright & Felleisen (1994, audit P36). Safety on closed programs.
- **Comodels and runners**: the four texts of §2.9's literature, with the same locators.
  A comodel of `Effects` is a `T`-runner of Ahman and Bauer at `T = StateT σ Option`.
  `Comodel.run` is the induced monad morphism of their Proposition 3.

#### 2. Effect4 Adaptation, Assumptions, and Exclusions
- **Adapting Simulation Relations**: Behavioral agreement between operational execution (`Api.run`) and
  denotational meaning (`meaning`) is established as equal-observation theorems over restricted fragments
  (`Straight`, `Looped`, and `M7Fragment`).
- **Separation of Route vs. Goals**: `m7_of_ledger` proves a **conditional implication** ($M5 \land M6 \implies M7$),
  not the milestones' premises or conclusions themselves. In the registry, the claim `m7-route` is
  `.fundamentalProperty` (a witness for the route theorem). The M7 results are separate claims, listed under the
  required properties below.
- **Boundary & Fragment Exclusions (Rows 138, 95, 117)**: M7 is stated strictly on `M7Fragment`.
  Its row table is **fixed empty** (`root.table = []`), decision tapes are answer-free, and requirement rows are closed (`rootTy.requires = empty`). The agreement at a non-empty row table is R6's (DI-57).
- **The host meaning on a run**: The call tree `denoteRows` reads a program over the stores and
  the host rows (`src/Effect4/Laws/Program/DenoteRows.lean`).
  Its fragment is `StraightRows`, which admits `catchIf` (`src/Effect4/Laws/Program/FragmentRows.lean`).
  Slice H8 of the host-meaning packet reads the meaning under a run's reply tape (decisions row 310).
  Slice H9 reads the meaning under any host whose answers are the run's.
  A host there is a comodel of the row signature, and the reply tape is one host (§2.9).
  On loops both hold past a budget bound, through the budgeted meaning `denoteRowsB` on
  `LoopedDataRows` (`src/Effect4/Laws/Program/DenoteRowsB.lean`).
  A budget cut is no failure and no divergence.
  Each statement of H8 and H9 takes one fiber and a recorded run that is funded, at rest and
  driven by a host. None claims progress.
  The packet is `git:98a29895b800556365a2edc9924f3ed12787b820:docs/research/2026-10-07-packet-host-meaning.md`, and the loops are
  `git:98a29895b800556365a2edc9924f3ed12787b820:docs/research/2026-10-10-host-meaning-widening/README.md` (DI-57, DI-69).

#### 3. Project Definition and Judgment
Agreement theorems and fragment definitions are modeled in `src/Effect4/Laws/Program/Agreement/Segment.lean`
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
(`run_eq_meaning` in `src/Effect4/Laws/Program/Agreement/Segment.lean`, `M7Fragment` in `src/Effect4/Laws/Program/Typed/Assembly.lean`).

#### 4. Required Properties and Obligations

- **Checked disk-image recovery (seams ST2, R13)**: Recovery starts at the empty store and uses shared node value admission.
  `restore_roots` states checked empty-store restoration retains the exact root table, including legacy generations.
  `restore_closed` states checked empty-store restoration establishes node closure through shared admission.
  `restore_targets` states every restored root resolves to a durable resident of its fixed kind.
  Their owner is `src/Effect4/Laws/Store/Recovery.lean`.
  The claims are `cas-restore-roots`, `cas-restore-closed`, and `cas-restore-targets`.
  They establish no historical ancestry, generation provenance, hash injectivity, filesystem correctness, or host progress.

- **Recorded calls occur in the admitted call tree (`recorded-call-tree-prefix`)**: Each recorded call binding names a wait in that program's admitted call tree.
  `Run.CallTree.bound_in_tree` states the obligation in `src/Effect4/Laws/Run/CallTree.lean`.
  Its premises are `StraightRows`, no cause handlers and a reached run.
  The tree uses exits from replies submitted in that run.
  It covers arbitrary command budgets and establishes no progress, fork behavior or scope behavior.
- **Straight program agreement (`run-eq-meaning`)**: Frame machine execution matches denotational meaning on `Straight`.
  (`run_eq_meaning` (`src/Effect4/Laws/Program/Agreement/Segment.lean`)).
- **Loop agreement (`loop-agreement`)**: Replay agreement holds across straight loop steps
  (`loopAgreement_of_straight` (`src/Effect4/Laws/Program/LoopAgreement.lean`)).
- **Reference machine simulation (`run-eq-ref`)**: Frame machine replay matches term reference replay at empty row table
  (`run_eq_ref` (`src/Effect4/Laws/Program/RuntimeR.lean`)).
- **Straight composition agrees (`straight-composition-agreement`)**: Programs related by
  `StraightEq` run to equal exits and stores at their own sufficient budgets.
  (`StraightEq.run_agrees` (`src/Effect4/Laws/Program/MeaningEq.lean`)).
- **The call tree extends the meaning (`rows-denotation-straight`, `rows-denotation-append`,
  `rows-denotation-reference`)**: On `Straight`, the call tree is `denote`'s tree, injected on the
  left of the coproduct.
  (`Denote.denoteRows_straight` (`src/Effect4/Laws/Program/DenoteRows.lean`)).
  On `StraightRows`, a program's meaning under a host of an appended row table is its meaning
  under that host restricted to its rows.
  This is C2 of DB-01 for host rows, and outside the fragment C2 stays operational
  (`Denote.meaningUnder_append` (`src/Effect4/Laws/Program/DenoteRowsAppend.lean`)).
  The reference machine's term of a `StraightRows` program, its control markers erased, is the
  call tree read into the reference machine's signature.
  That law needs a compile budget that covers the program's depth
  (`Sched.denoteR_straightRows` (`src/Effect4/Laws/Program/DenoteRowsR.lean`); decisions row 310).
- **The raw agreement at every row table (`run-eq-ref-table`, `session-eq-ref`)**: The frame
  machine and the reference machine agree at every row table.
  On every program, decision tape and pair of budgets, they reach the same class and the same
  observation `obs`.
  The law takes no premise on the tape: a host answer reaches either machine only as a
  decision (DI-23).
  (`Sched.run_eq_ref_table` (`src/Effect4/Laws/Program/Table/Agreement.lean`)).
  For a recorded, funded run, a session's reading is the reference machine's replay of the
  run's own tape, with the same class and observation.
  (`Run.session_eq_ref` (`src/Effect4/Laws/Api/SessionRef.lean`)).
  Neither law says anything of reply admission, reply typing, a host's conformance or the
  session's ledger.
  The second says nothing of a run with a stopped row (DI-57, decisions rows 310 and 314).
- **H8 and H9 on straight programs (`rows-denotation-session`, `rows-denotation-host`,
  `rows-denotation-driver`)**: Take a recorded run of a `StraightRows` program.
  The run is funded, at rest and driven by a host.
  H8: the meaning of the program under the run's reply tape is the root's exit with the stores,
  or the frontier (`Run.denoteRows_eq_session`).
  H9: if the run is also finished, take any host whose answers are the run's.
  The host's run of the call tree is then the root's exit with the stores, and the host ends
  where the answers left it (`Run.denoteRows_eq_session_host`).
  Both laws are in `src/Effect4/Laws/Api/SessionMeaning.lean`.
  At the driver, `Run.runWith` opens a `StraightRows` program, evaluates its root and drives it
  with a reactor.
  The reactor stays inside the envelope and answers with exits.
  The law's premises are that the run is funded, at rest and its root exited.
  Then the reactor read as a host runs the call tree to that exit with the stores.
  It ends at the drive's state (`Run.runWith_denotes` (`src/Effect4/Laws/Api/HostDrive.lean`),
  slice CO-6).
  Nothing shows that the drive finishes, that its rounds suffice or that the run is funded.
  Each law takes one fiber and claims no progress.
  None says anything of an interruption, a clock step, a delayed cell read or a handle row.
  H9 says nothing of a run stopped at a call.
- **H8 and H9 on loops (`rows-loop-session`, `rows-loop-host`, `rows-loop-driver`,
  `rows-loop-straight`, `rows-loop-looped`)**: The budgeted row meaning `denoteRowsB` extends
  both meanings.
  On `StraightRows` it is `denoteRows` finished, at every budget
  (`Denote.denoteRowsB_straight`).
  On `Looped` it is `denoteB` injected on the left of the coproduct, at the same budget
  (`Denote.denoteRowsB_looped`).
  Both laws are in `src/Effect4/Laws/Program/DenoteRowsB.lean`.
  Take a recorded run of a `LoopedRows` program in `LoopedDataRows`, funded, at rest and driven
  by a host.
  Past a budget bound, the coarse observation of the budgeted meaning under the run's reply tape
  is the root's exit with the stores, or none.
  (`Run.h8_loopedRows`).
  For a finished run, take any host whose answers are the run's.
  Past a budget bound, the budgeted meaning under that host is the root's exit with the stores.
  The host ends where the answers left it (`Run.denoteRowsB_eq_session_host`).
  At the driver, the reactor read as a host runs the budgeted call tree to the root's exit with
  the stores.
  That holds past a budget bound (`Run.runWith_denotesB`).
  Its premises are the straight driver's: a funded run at rest whose root exited.
  The three laws are in `src/Effect4/Laws/Api/SessionMeaningLoop.lean`.
  No law takes a global compile-depth premise, and a budget cut is no failure and no divergence.
  Each claims no progress.
  None says anything of a waiting position's stores or request, a scope, a handle allocation, a
  fork or an interruption (slice L1).
- **M7 conditional route (`m7-route`)**: Derivation of M7 conditionally from M5 and M6 ledger components
  (`m7_of_ledger` (`src/Effect4/Laws/Program/Typed/Assembly.lean`)).
- **M7's results (`m7-exits-typed`, `m7-stores-typed`, `m7-never-halts`, `m7-admitted`)**: On
  `M7Fragment`, every exit that the observation records fits its fiber's declared type (M7a).
  The observed stores fit at a world that describes them (M7b).
  The frame machine never halts (M7c, row 139).
  (`m7_proved` (`src/Effect4/Laws/Program/Typed/Commands/Clauses/All.lean`)).
  M7a–c hold for a program that the API admits at the empty row table, with a closed
  requirement row and an answer-free tape.
  (`m7_admitted` (`src/Effect4/Laws/Program/Typed/AdmittedSource.lean`)).
- **Typed exits and observations (`m7-exit-handles-valid`, `obs-typed-admitted`,
  `m7-results-exit-hasty`)**: Recorded exits name only live scope handles on every reachable
  machine (row 139, `exitHandles_valid`).
  On every ghost-admitted tape of a checked program, the frame machine's observation is typed and
  the run has not halted (`obs_typed`).
  Both laws are in `src/Effect4/Laws/Program/Typed/Commands/Clauses/All.lean`.
  Every recorded exit of a checked program's frame-machine run satisfies the meaning layer's exit
  judgment at its declared type (T1).
  (`exits_hasTy` (`src/Effect4/Laws/Program/Typed/Results.lean`)).
- **A face is exact inside its profile (`profile-plus-exact`, `profile-mul-exact`)**: Take two
  arguments inside the profile.
  The checked integer addition answers exactly when the reference addition answers inside the
  profile.
  For this one operation that grows, a face equals the reference inside its profile and refuses
  outside it (DI-56).
  The checked natural multiplication answers exactly for the represented product inside the
  supplied bound.
  The OCaml row and the TypeScript helper stay trusted rows, each run by a finite control
  (decisions rows 108 and 321).
  (`intAddIn_eq_some_iff`, `mulIn_eq_some_iff` (`src/Effect4/Laws/Machine/IntegerProfile.lean`)).
- **Profile support refuses at ingress, located (`profile-support-located`)**: Profile support is
  one judgment over the value tree and over a program's literals. Its bound is
  `ProfileData.natBound`, and `admitsNat` is its leaf.
  A value's refusal is absent exactly when every number of its tree is inside the bound.
  A program's refusal is absent exactly when every literal of the literal fold is.
  The refusal names the path of the first number outside, or the address of its node.
  The engine and the kit run it at ingress, lowered by the LCNF route, before a reply is applied
  or a program runs.
  It establishes nothing of which face reads a supported value, nor of arithmetic inside a run.
  (`ProfileData.valueRefusal_eq_none_iff`, `ProfileData.literalRefusal_eq_none_iff`
  (`src/Effect4/Laws/Program/ProfileSupport.lean`)).
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
- **A step reads its value (`step-language-sound`)**: A step is data over typed inputs
  (`src/Effect4/Step.lean`).
  The caller's terms read the input encodings, and the step passes its reading check.
  A fold requires aligned caller value and source scope lengths.
  Deferred comparison requires `DeferredIdentity` at the carrier interpretation.
  Captured caller sources resolve at their original scope.
  Then the translated term reads the carrier value (`Step.sound`, `src/Effect4/Laws/Step.lean`).
  Each module separately proves its value equation against an independent behavior model.
  The shared law establishes no optional field, allocation, wrapper, run or host behavior (decisions row 330).
- **The Latch's steps agree with its model (`latch-steps-agree`)**: The Latch is written in the
  step language from the start (`src/Effect4/Library/Latch/Steps.lean`).
  Its model is rc.112's `class Latch`: `isOpen`, `open` and `release` with `scheduleUnsafe`,
  `flushScheduled` and `closeUnsafe` (`src/Effect4/Library/Latch/Model.lean`).
  A wake posts one flush per batch, and a later wake joins the scheduled batch.
  The cell's value is the image of the model state's carrier, by definition.
  So each step's agreement is the reading law and one equation of Lean values
  (`latch_steps_agree`, `src/Effect4/Laws/Library/Latch/Steps.lean`).
  It establishes nothing of `await`, interruption, the posted flush's fiber or liveness
  (decisions row 330).
- **Latch registration agrees with its model (`latch-registration-agrees`)**: Initial construction and registration read their independent model transitions.
  Registration uses the identity and hint supplied by the encoding table.
  Withdrawal requires an injective table and aligned caller value and source scope lengths.
  It removes the first matching registration, including duplicates, and searches live waiters before the attached scheduled batch.
  It retains the scheduled flag when the batch becomes empty.
  The connector is `latch_registration_agrees` (`src/Effect4/Laws/Library/Latch/Registration.lean`).
  It establishes no interruption delivery, posted-flush execution, liveness or host behavior.
- **Channel transforms its selected payload (`channel-batch-transform`, `channel-completion-transform`)**: An exact input observation selects the batch or completion transformation.
  Input failures propagate with their full cause and resulting stores.
  A selected handler's exit and resulting stores become the result.
  The laws require aligned scopes and successful elaboration of the input and handlers.
  They are `Internal.mapEffectOf_protocol` and `Internal.mapDoneEffectOf_protocol` (`src/Effect4/Laws/Library/Channel/Protocol.lean`).
  These denotation laws do not execute stored definition calls or establish nonempty outputs, whole-stream behavior or host simulation.
- **Pull selects its protocol handler (`pull-protocol-selection`)**: The input answers an exact batch or End value, or fails with its full cause.
  Authoring elaboration accepts all handlers, and source and value scopes have equal lengths.
  The selected handler receives the input's resulting stores.
  Its full exit and final stores are the result.
  The law is `Pull.matchEffect_protocol` (`src/Effect4/Laws/Library/Pull/Protocol.lean`).
  It uses the existing denotation and establishes no scheduler, host Done, nonempty-batch admission or whole-stream agreement.
- **Pull propagates completion recovery (`pull-completion-recovery`)**: An input failure retains its cause and resulting stores.
  An input success runs the answer handler with those stores.
  A failure from that handler escapes unchanged.
  The law requires successful input and handler authoring elaboration.
  The law is `Pull.catchDone_meaning` (`src/Effect4/Laws/Library/Pull/Protocol.lean`).
  Exact answer selection uses `Pull.matchAnswer_meaning` in the same file.
  Neither law establishes host completion correspondence.
- **A step keeps the fields it does not name (`step-frame`)**: Take an update spine of an
  input. A field that no overwrite of the step names keeps its value.
  On carriers the law has no premise on the record's names (`Step.frame`).
  On the machine's record frame it holds for ascending names (`Step.frame_read`).
  It says nothing of a step that is no spine (decisions row 330).
- **A journal's position replays (`journal-position-replay`)**: The machine after a position
  of a journal's tape is the raw replay of the decisions up to that position. The replay
  starts at the machine of the run that the tape was read from. A journal splits into a
  completed prefix and an unread rest, and the prefix's machine is the replay of its
  positions (`tapeFrom_cut_replays`). The laws say nothing about the machine after a stopped
  row: that row may change the machine before it reports its frontier.
  (`tapeFrom_position_replays` (`src/Effect4/Laws/Run/Tape.lean`)).
- **A funded run replays (`funded-run-replay`)**: A run is funded when the tape of its own
  journal leaves no row unread. The machine of a funded run is the raw replay of its tape's
  decisions, from the program's own load. A statement over a session's runs takes this
  budget premise by its one name, `funded`. A journal's verdicts do not decide it: a reply's
  application answers `applied` whatever fuel its step had left. The law says nothing about
  a run with a stopped row, a session ledger or a generated engine.
  (`funded_replays` (`src/Effect4/Laws/Run/Tape.lean`)).
- **A journal's tape replays (`replay-externals`, `run-controls-replay`, `run-tape-replay`)**:
  No replay at the empty row table allocates an external handle.
  (`replay_externals` (`src/Effect4/Laws/Program/RuntimeR.lean`)).
  Journaled control rows leave the raw replay's machine whenever every added phase progressed.
  (`Run.play_controls_eq_replay` (`src/Effect4/Laws/Run.lean`)).
  A journal's machine is the raw replay of its tape: the controls that progressed and the reply
  applications.
  Each enters as the decision that the session hands the machine.
  The law holds for any run and any journal whose tape reads to its end.
  It says nothing of a session ledger, a journal that stops at a frontier or a generated engine
  (decisions row 254).
  (`Run.tape_replays` (`src/Effect4/Laws/Run/Tape.lean`)).
- **Pool's steps agree with the model (`pool-steps-agree`)**: Each of Pool's six step terms
  agrees with the model's step, on every state of the model. The lease, the withdrawal and
  the closer's step take an injective table. The agreement covers the reply, the stored
  value through the table, and the selected waiters' records. It is a part of the proposed claim
  `pool-expansion-agrees`. It states no order of the wake across helpers, no cancellation
  law, no wait of the close along a run and no wrapper.
  (`pool_steps_agree` (`src/Effect4/Laws/Library/Pool/Steps.lean`)).
- **More modules agree with their models (`queue-steps-agree`, `semaphore-steps-agree`,
  `partitioned-semaphore-bookkeeping`, `pubsub-single-steps-agree`,
  `stream-array-step-agreement`, `ref-steps-agree`)**: Each law reads a module's steps against an
  independent model.
  Each of the Queue's six step terms agrees with the model's step on the first profile.
  It covers the reply, the stored value through the encoding table and the ordered signals
  (decisions row 255).
  (`queue_steps_agree` (`src/Effect4/Laws/Library/Queue/Steps.lean`)).
  Each of Semaphore's five step terms agrees with the model's step on every model state.
  It covers the reply, the stored value through the encoding table and the selected waiter's
  record (decisions rows 259 to 261 and 265).
  (`semaphore_steps_agree` (`src/Effect4/Laws/Library/Semaphore/Steps.lean`)).
  Neither states delivery, an order of the wake across visits or a cancellation law.
  PartitionedSemaphore's four scalar step terms read its natural-count model: initialization,
  availability, attempted acquisition and reservation of the unmet need.
  Reservation assumes insufficient availability and a request within capacity.
  (`bookkeeping_agrees` (`src/Effect4/Laws/Library/PartitionedSemaphore/Steps.lean`)).
  It states no waiter registration, identity allocation, wake delivery or codec admission.
  Six pure PubSub bookkeeping sources read its capacity-one, replay-zero, natural-message model.
  They are the initial source, subscription with a fresh logical name, `tryPublish`, `poll`,
  `unsubscribe` and `slide`.
  (`single_steps_agree` (`src/Effect4/Laws/Library/PubSub/Steps.lean`)).
  It states no handle allocation, delivery, lifetime, backpressure or arbitrary capacity.
  The Stream array source's batch extraction returns the pending list and clears its allocated
  backing cell.
  It needs a receiver that reads the cell handle and a cell that holds the input image.
  (`arrayStep_agrees` (`src/Effect4/Laws/Library/Stream/Array.lean`)).
  It states no whole pull, scope finalization, codec admission or handle allocation.
  The PubSub and Stream laws need aligned value and source scope lengths.
  Each of Ref's thirteen effectful operations agrees with the model of `Ref` in latest (Effect
  4.0.1), under allocation and callback-evaluation premises.
  The laws compare replies and final stores, not write events.
  So they say nothing of whether an operation writes an unchanged value, a callback exception or
  a reentrant mutation.
  (`ref_steps_agree` (`src/Effect4/Laws/Library/Ref/Operations.lean`)).
  None of these laws states a wrapper, a schedule, a whole run, liveness or a host's behaviour
  (decisions rows 330, 331 and 335).

### 2.11 Concept 11: Typed Editing (`typed-editing`)

Decisions row 414 (5) ruled this concept: it owns sketches, places, edit policies, documents,
fills, suggestions, expected context and marking. Row 418 adds the workspace and the verdict, the
two objects the tool holds. This section is prose only. Semantics generation is paused (row 418
(6)). So the semantics registry (`tools/ProofGraph/Registry.lean`) has no entry for this concept yet. The claims of part 4 keep their present
concepts until generation resumes.

#### 1. What the Literature Defines
- **Typed holes.** An expression with holes is the object an editor holds. The source is Omar,
  Voysey, Hilton and others, *Hazelnut: A Bidirectionally Typed Structure Editor Calculus*, POPL
  2017 (read in `git:98a29895b800556365a2edc9924f3ed12787b820:docs/research/2026-10-06-seat-GAP-study.md` §3). Each hole has an entry with its
  type, and filling a hole is an operation of its own. The source is Omar, Voysey, Chugh and
  Hammer, *Live Functional Programming with Typed Holes*, ICFP 2019 (vendored as
  `vendor/papers/gradual-holes/omar-live-typed-holes-1805.00155v4.pdf`).
- **Total marking.** A checker marks each ill-typed position and goes on. So it types every
  position of a program, not only the ones before the first error. The source is Zhao, Maroof,
  Dukkipati, Blinn, Pan and Omar, *Total Type Error Localization and Recovery with Holes*, POPL
  2024 (vendored as `vendor/papers/gradual-holes/zhao-marking-popl24.pdf`).
- **The focus of a typed decomposition.** A typed program splits at an address into a context and
  a focus. Any program of the focus's type stands in the focus's place. The source is Carroll,
  Madhavapeddy and Omar 2026, Theorem 5.2 (read in the head of
  `src/Effect4/Laws/Program/Typing/Replace.lean`).
- **Incremental attribute evaluation.** An edit re-evaluates only the attributes it reaches
  (Reps, Teitelbaum and Demers 1983; recalled, `git:98a29895b800556365a2edc9924f3ed12787b820:docs/research/2026-10-08-live-authoring.md` §2).

#### 2. Effect4 Adaptation, Assumptions, and Exclusions
- **A hole is a host row.** A sketch is a program over its application's row table, extended by
  one hole row per hole (`Row.hole`, `src/Effect4/Program/Sketch.lean`). So every fold, the
  checker and the printer read a sketch as a program, and editing adds no program syntax.
- **An edit is data.** A place is a hole's index or an address with the sub-program it must still
  hold (`Place`, `src/Effect4/Program/Typing/SourceDocument.lean`). An action fills or omits at a
  place (`DocAction`, same file). A policy says how a feed decides an edit (`FeedPolicy`,
  `src/Effect4/Program/Typing/SourceSession.lean`).
- **Each object is a state reached by its journal.** A document is reached by its actions
  (`Doc.replayedState`), a fill set by its submissions (`FillSet.constructed`), and the workspace
  by its accepted actions (`Tool.State.replayed`). This is the monoid action of concept 7, the
  same construction as a run's journal (`docs/research/2026-10-20-coherence-audit/coherence.md`
  §3).
- **A suggestion is a fill that was not taken.** `Suggest.suggestOne` evaluates a candidate by the
  same `keepExact` feed that certifies a fill (`src/Effect4/Program/Typing/Suggest.lean`), so a
  suggestion and a fill never disagree.
- **The verdict is the checker's.** The checker is one `Except` fold whose refusal is located
  (`Checker.check`, `Checker.explain`, `src/Effect4/Program/Checker.lean`). The checker's memo
  changes cost, never an answer (`Check.Oracle.eq_uncached`, `src/Effect4/Program/Check.lean`).
- **Expected context.** The focus gives each address the environment and the type that the rest of
  the program gives it (`Focus`, `envAt`, `src/Effect4/Program/Typing/Focus.lean`). The type an
  address is expected to have, with its substitution law, is not defined yet (the slices plan's
  L2, `expectAt`).
- **Marking.** The annotation marks a subtree past a refused read as not reached
  (`Annotate.unreached`, `src/Effect4/Program/Typing/Annotate.lean`). Total marking is not defined
  yet (L3). Row 414 (6) starts it with explicit unknown contexts.
- **Text in, data judged.** An agent writes Effect TypeScript, and the reader turns it into `Eff`
  (row 418 (4)). This concept judges the data, not the text.
- **Exclusions.** No cursor calculus: an edit is an addressed replacement, not a structure
  editor's movement. No live evaluation of a hole's closure. No merge of two writers' edits until
  L4 states how a stale edit moves to a new snapshot.

#### 3. Project Definition and Judgment
A place and a policy are the data an edit carries (`src/Effect4/Program/Typing/SourceDocument.lean`,
`src/Effect4/Program/Typing/SourceSession.lean`):
```lean
inductive Place where
  | hole (index : Nat)
  | at_ (path : List Nat) (expected : NativeEff)

inductive FeedPolicy where
  | draft
  | keepExact
  | recheck
```
The judgment of a document is coherence: its table is its sketch's source table
(`SourceSession.Coherent`, `src/Effect4/Program/Typing/SourceSession.lean`). The tool serves one
transition over a workspace (`Tool.serve`; `Tool.Native.Workspace`, `src/Effect4/Tool/Native.lean`),
and a workspace persists as a chain of `WorkspaceEntry` nodes (`Tool.Exchange`,
`src/Effect4/Tool/Exchange.lean`).

#### 4. Required Properties and Obligations
The claims below state this concept's properties today. They move here when generation resumes.
Their statuses are generated, never written here.
- **A sketch is a conservative extension** (concept 7 today): `sketch-conservative`,
  `sketch-weakening`, `hole-rule`, `module-holes-conservative`.
- **A typed program splits at an address** (concept 7): `addressed-replacement`,
  `typed-replacement`, `focus-function`.
- **The address table is the checker's answer at every address** (concept 7): `address-table`,
  `annotate-table`, `module-address-table`, `module-annotate-table`, `source-annotation-agrees`.
- **An edit splices the table** (concept 7): `edit-splices-table`, `module-table-splices`,
  `omit-splices-table`.
- **A feed keeps the document coherent, under each policy** (concept 7): `edit-session-coherent`,
  `edit-session-undo`, `edit-repaint-set`, `source-feed-coherent`, `source-feed-edit`,
  `source-feed-draft`, `source-feed-keep-exact`, `source-feed-root`, `source-session-coherent`,
  `source-session-undo`, `source-session-draft-transport`.
- **A document's actions replay to its state** (concept 7): `source-document-coherent`,
  `source-document-replay`, `source-document-atomic`, `source-document-step`,
  `source-document-commit`, `source-document-local-keep`, `source-document-single-transport`,
  `source-document-revert`.
- **A fill set publishes what it constructed** (concept 7): `kept-fill-reference`,
  `pending-fill-construction`, `pending-fill-publication`.
- **The checker's verdict is placed, and its memo changes no answer** (concepts 7 and 9):
  `checker-placed-verdict`, `checker-ask-value`, `checker-oracle-agrees`.
- **The workspace is one transition, and its stored history loads back** (concept 9):
  `tool-serve-appends`, `tool-serve-refuses`, `tool-serve-query`, `tool-serve-transparent`,
  `tool-transcript-replays`, `tool-serve-answers`, `workspace-load-own`,
  `workspace-commits-once`, `workspace-refuses`.

The codecs of a sketch and of a workspace entry (`sketch-wire`, `workspace-entry-exact`) stay with
concept 5, which owns every exact codec.

Owed, with no definition yet (the slices plan's lane L and row 414 (3)):
- **A feed checks only the new subtree** (`feed-checks-subtree`, L1).
- **An address has an expected type, with its substitution law** (`expectAt`, L2).
- **Total marking agrees with the checker** (`marking-agrees`, L3).
- **A stale edit rebases onto a new snapshot** (`kept-edit-rebases`, L4).
- **One query answers full admission** (`checkProgram`, row 414 (3)).

This concept serves R14 (a sketch checks and explains its types) and R6 (the tool's transitions),
and the first release (row 418 (1)). It establishes no live evaluation of holes, no merge of
concurrent edits, and nothing about the text an agent writes before the reader.

## 3. The object-language glossary (moved 2026-10-03)

The glossary that set our words against Lean's moved to the dictionary,
`docs/core/controlled-english.md` §3.2 and §3.3. It covers syntax, the three senses of
elaboration, print, read, render, lift, sugar, census and gate, each with its Lean counterpart.
Each site is now cited by name and path, not by line.

---

## 4. Metatheoretical Bounds & Evidence Summary

1. **Axiom Ceiling**: The producer checks every theorem cited by the semantics registry at `[propext, Quot.sound]`.
   The whole-library gate (`Test/Audit/AxiomGate.lean`) holds every declaration there too, except the rendering and instrumentation declarations it admits by name.
2. **First-Order Data Discipline**: Stored `Eff` syntax is first-order data: its bind continuation
   is another program tree with positional inputs (`src/Effect4/Program/Eff.lean`). `RProgram` is the proof-side
   semantic carrier `Effects.Program RSig ExitV`, whose visible operation nodes carry Lean function
   continuations (`vis : Answer op → Program sig A`). Those functions belong to the semantic model
   and are not stored function values in `Eff` or `Val`.
3. **Simulations vs. Equivalence**: Behavioral relationships are stated strictly as equal-observation
   theorems over specified fragments (`Straight`, `Looped`, empty row table `M7Fragment`), never
   as unqualified "equivalence".
4. **Literature Tracking**: Every textbook chapter and academic paper citation is audited against
   vendored copies in `git:98a29895b800556365a2edc9924f3ed12787b820:docs/research/2026-10-01-semantics/citations-audit.md`.
