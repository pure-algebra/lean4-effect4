# Effect4 Implementation Inventory: Semantic Contracts and Next Bounded Slices

This document establishes the implementation inventory derived from Effect4's semantic contracts.
For each of the ten core foundational concepts, it records what the semantic contract demands,
distinguishes required implementation work from deliberate exclusions, refuted statements, and
external assumptions, and connects outstanding items to their owners, decision rows, and next
bounded build slices.

Status ownership belongs strictly to the existing evidence and decision registers
(`tools/ProofGraph/Ledger.lean`, `Test/Counterexamples/REGISTER.md`, `docs/core/decisions.md`).
The selected registry claims are an authored sample; this inventory makes the broader obligation
chain visible.

---

## 1. Overview and Planning Focus

### 1.1 The Two Primary Implementation Paths

Implementation work in Effect4 is organized along two mutually supportive paths:

```
THE DATA PATH:
  W2 Generator Hand-back
      │ (make gen-data, order work)
      ▼
  W4 Value & Type Appends
      │ (signed int, binary64 float, new Ty constructors)
      ▼
  W5 Exact Codecs
      │ (JSON & Schema exact embeddings, rows 128 & 179)
      ▼
  W6 Term & Surface Faces
      │ (AST representation, render, read/print roundtrip)
      ▼
  p2 Handler Acceptance
        (end-to-end host-side decoding and execution)

THE ASSURANCE PATH:
  D4 Scope & D2 Constructor Group Hand-backs + Owner Bookkeeping Repair
      │ (src/Effect4/Laws/Program/Typed/Commands/Bookkeeping.lean)
      ▼
  M5 Residual Constructor Groups
      │ (seq_typed companions: onFailure, all, onExit; rows 148, 176, 183)
      ▼
  D5 Command & Field Invariants
      │ (M6 preservation goals: step_loop, step_deliver; rows 134 & 181)
      ▼
  M7 Capstone Safety
        (M7Exits, M7Stores, M7NoHalt, ExitHandlesValid on M7Fragment)
```

1. **The Data Path (Product Finish Line)**:
   Advances the concrete data representation towards the v0 acceptance milestone: `p2`'s handler with
   host-side decoding (`docs/research/2026-10-01-data-wave/README.md`). W2's generator hand-back feeds W4's
   value and type appends (starting with signed integer and binary64 float images), which in turn enable
   W5's exact codecs (decisions rows 128, 179), W6's term constructors, and finally the printed/read
   surfaces.
2. **The Assurance Path (Semantic Soundness Finish Line)**:
   Advances the metatheoretical proof graph to support the M7 capstone safety results. Following D4's
   scope lifetime hand-back, D2's residual constructor groups, and the owner's Bookkeeping repair
   (`src/Effect4/Laws/Program/Typed/Commands/Bookkeeping.lean`), the path discharges M5's residual typing
   goals across all syntax forms (`seq_typed`, `onFailure_typed`, etc.), D5's scheduler preservation
   goals across command cases (`step_loop`, `step_deliver`), and ultimately discharges M7's four capstone
   goals (`M7Exits`, `M7Stores`, `M7NoHalt`, `ExitHandlesValid`) over `M7Fragment`.

---

## 2. The Ten-Concept Semantic Alignment and Implementation Inventory

### 2.1 Concept 1: Store Typing & Value Membership (`store-typing`)

#### Semantic Contract
Value membership `Fits w v ty` asserts that a stored runtime value `v : Val` satisfies the semantic type
`ty : Ty` under Kripke world typing `w : World`. Handle leaves verify capability declarations against
allocated tables in `w` (`w.Ρ`, `w.«Π»`, `w.Γ`) and check scope persistence (`ScopeLive w sc`). By
decisions row 163, values are strictly first-order; `Fits` contains no arrow clause.

#### Implementation Inventory
| Item | Category | Judgment / Law | Evidence / Decision | Owner / Dep | Next Bounded Action |
|---|---|---|---|---|---|
| `fits-mono` | Proved Witness | `w.leHost w' → Fits w v ty → Fits w' v ty` | `Membership.lean:885` | Core | Maintain under world extensions |
| `fits-subn` | Proved Witness | `Ty.subN a b = true → Fits w v a → Fits w v b` | `Membership.lean:1261` | Core | Maintain across data-wave appends |
| `fits-normalize` | Proved Witness | `Fits w v t.normalize ↔ Fits w v t` | `Membership.lean:1155` | Core | Re-check when new type forms normalize |
| `fits-scope-inv` | Proved Witness | `Fits w v Ty.scope → ∃ sc, v = .scopeHandle sc ∧ ScopeLive w sc` | `Membership.lean:895` | Core | Maintain under scope close walks |
| `raw-subtyping-union` | Refuted (Repaired) | Raw `sub` does not distribute products over unions | `E4-TYPED-CE-009`, Row 137 | Core | Keep checker order under `subN` |
| `store-safety` | Required Work | Inductive configuration typing preserves store validity | Row 139, D5 / Row 181 | D5 / Laws | State and prove store validity preservation under store write commands |
| `data-wave-values` | Required Work | `Fits` clauses for signed integer and binary64 float values | Decisions Rows 109, 121, Data-Wave W4 | Seat W4 | Implement `Val.int64`, `Val.float64` images and their `Fits` clauses |
| `arrow-membership` | Intentional Exclusion | Arrow typing clause `Fits w v (Ty.arrow a b)` | Decisions Row 163, `language-cut.md` §1 | Architecture | Excluded by language cut: no function values in `Val` |
| `step-indexing` | Intentional Exclusion | Step-indexed semantic tie over circular higher-order stores | Decisions Row 163 | Architecture | Excluded: first-order stores prevent semantic circularity |

---

### 2.2 Concept 2: Residual Program Typing (`residual-program-typing`)

#### Semantic Contract
Residual programs resulting from elaboration are typed by `TypedProg root w ty a`, where `a : RProgram`
is an inductive free-monad AST (`Effects.Program (SyncOp ⊕ FiberOp) ExitV`). Operation clauses require
certificate validation and enforce that continuations type for all permitted replies at later worlds.
Closing markers (`unguard`, `finishFinalizer`) carry exit values directly.

#### Implementation Inventory
| Item | Category | Judgment / Law | Evidence / Decision | Owner / Dep | Next Bounded Action |
|---|---|---|---|---|---|
| `seq-typed` | Proved Witness | `TypedProg w mid a → (∀ w' v, Fits w' v mid.answer → TypedProg w' ty (k v)) → TypedProg w ty ((guardR .onSuccess a).bind (seqR k))` | `Seq.lean:59`, Row 148 | Core | Reused by M5 elaboration |
| `close-typed` | Proved Witness | Invariance of `TypedProg` under closing `unguard` markers | `Seq.lean:40` | Core | Reused by M5 bracket lowering |
| `denote-typed` | Open Goal | `typeOfProgram root.sig root.prog = some ty → TypedProg root w ty (denoteR root)` | `Assembly.lean:1637` (`denoteR_typed`) | M5 / Seat D2 | Prove M5 capstone from constructor groups |
| `bind-closed` | Refuted | `TypedProg` is closed under unrestricted monadic bind | `E4-TYPED-CE-030`, Row 148 | Core / M5 | Refuted: sequencing must use per-construct compatibility lemmas |
| `on-failure-typed` | Required Work | `TypedProg` compatibility for `onFailure` control bracket | Decisions Row 148, M5 | Seat D2 | Prove `onFailure_typed` beside `seq_typed` with positive & rejecting controls |
| `all-typed` | Required Work | `TypedProg` compatibility for tuple/record zip composition (`all`) | Decisions Row 148, M5 | Seat D2 | Prove `all_typed` for parallel sync branches |
| `on-exit-typed` | Required Work | `TypedProg` compatibility for finalization bracket (`onExit`) | Decisions Row 148, M5 | Seat D2 | Prove `onExit_typed` ensuring finalizer typing |
| `layer-context-rep` | Required Work | Requirement row representation in residual program certificates | Decisions Row 176 | Seat D2 | Reconcile layer context representation in certificate ledger |
| `lawful-template-row` | Required Work | Kernel control for `List<A>` to `Option<A>` template conversion | Decisions Row 183 | Seat D2 | Prove kernel preservation control for template row instance |
| `open-root-rows` | Intentional Exclusion | Programs admitted with non-empty requirement rows | Decisions Row 117 | Architecture | Excluded at load time: `rootTy.requires = empty` enforced by `LoadsTyped` |

---

### 2.3 Concept 3: Scope Lifetime & Finalization (`scope-lifetime-finalization`)

#### Semantic Contract
Scopes govern resource lifetimes via an insertion-ordered finalizer table. Closing a scope transitions
its state to `Closed` *before* iterating finalizers, guaranteeing LIFO execution and ensuring re-entrant
finalizer additions observe closed state immediately.

#### Implementation Inventory
| Item | Category | Judgment / Law | Evidence / Decision | Owner / Dep | Next Bounded Action |
|---|---|---|---|---|---|
| `close-idempotent` | Proved Witness | `self.isClosed = true → close run self ex = (self, Exit.void)` | `Effect4.Scope.close_idempotent` (`Scope.lean:950`) | Core | Base case for scope close termination |
| `close-twice` | Proved Witness | `close run (close run self first).1 second = ((close run self first).1, Exit.void)` | `Effect4.Scope.close_twice` (`Scope.lean:960`) | Core | Idempotence of consecutive closes |
| `close-order-eq` | Proved Witness | `self.closeOrder = (self.finalizers.map Prod.snd).reverse` | `Effect4.Scope.closeOrder_eq` (`Scope.lean:978`) | Core | LIFO finalization contract |
| `close-reentrant-add` | Proved Witness | `self.isClosed = false → addExit run (closeState self ex) k φ = (closeState self ex, run φ ex)` | `Effect4.Scope.close_reentrant_add` (`Scope.lean:969`) | Core | State-first finalization rule |
| `close-seq-protocol` | Proved Witness | The close walk satisfies the iterator protocol for clean finalizers | `CloseIter.closeSeq_protocol` (`ProtocolPosts.lean:970`) | Core | Connects close walk to residual typing |
| `scope-validity-open` | Required Work | General scope validity under dynamic parent-child nesting | Decisions Row 156, D4 hand-back | Seat D4 | Prove scope handle validity across nested forks and joins |
| `absent-scope-exit` | Intentional Exclusion | Closing or exiting an absent scope handle | Decisions Row 156, `E4-SCHED-CE-020` | Architecture | Excluded: machine halts on absent scope in `prepareScopedExitR` |
| `defect-transmission` | Intentional Exclusion | `badName` and `notImplemented` transmission through finalizers | Decisions Row 152 | Architecture | Excluded: `ShapeFree` filter on closing exits |

---

### 2.4 Concept 4: Reactive Scheduling & Machine Invariants (`reactive-scheduling`)

#### Semantic Contract
The Effect4 runtime machine is an operational small-step state machine (`RunMachine`) executing
commands from decision queues. The configuration typing invariant `MachineTyped root rootTy w m`
guarantees that running configurations have no stuck errors (`stuck = none`). Fairness is finite:
`flush_fair` guarantees callback entry for initially armed owners within a round bound.

#### Implementation Inventory
| Item | Category | Judgment / Law | Evidence / Decision | Owner / Dep | Next Bounded Action |
|---|---|---|---|---|---|
| `machine-typed-not-halted` | Proved Witness | `MachineTyped root rootTy w (m.halt why) → False` | `Assembly.lean:310` | Core | Invariant consequence projecting `stuck = none` |
| `flush-fair` | Proved Witness | `m.armed.Nodup → FlushReady m → length ≤ rounds → owner ∈ m.armed → FiredWithin rounds owner` | `Scheduling.lean:413` | Core | Finite queue service theorem |
| `drivestate-lift` | Proved Witness | Step invariant lifting for sequential command loops | `Lift.lean:56` | Core | Inductive step lifting apparatus |
| `step-loop-preserves` | Open Goal | `stepDecision` on `.loop` preserves `MachineTyped` | `M6Ledger.step_loop` (`Assembly.lean:1683`) | Seat D5 | Prove preservation across loop decision |
| `step-deliver-preserves` | Open Goal | `stepDecision` on `.deliver` preserves `MachineTyped` | `M6Ledger.step_deliver` (`Assembly.lean:1694`) | Seat D5 | Prove preservation across deliver decision |
| `clock-preservation` | Open Goal | `stepDecision` preserves timer/clock state | `Assembly.lean:1867`, Row 134 | Seat D5 | Prove timer column preservation under step |
| `field-census-coverage` | Required Work | Field-by-field inductive invariant census for `MachineTyped` | Decisions Row 181 | Seat D5 | Complete field preservation census across all 18 commands |
| `scheduler-progress` | Required Work | Every typed state is either terminal, takes a step, or is at a live frontier | Decisions Row 139 | Laws / R12 | State operational progress theorem with live frontiers |
| `weak-fairness-liveness` | Required Work | Infinite-trace liveness under weak scheduler fairness | Decisions Row 86, Requirement R12 | Laws / R12 | Open theoretical goal: define fair infinite behaviors |
| `unbounded-tokens` | Intentional Exclusion | Allocation of unbounded or negative token indices | Decisions Row 106 | Architecture | Excluded: `QueueOk` enforces `GuardState.keysBelow` |

---

### 2.5 Concept 5: Exact Codecs & Data Plane Embeddings (`exact-codecs`)

#### Semantic Contract
Codecs provide exact embeddings between first-order AST representations and external formats (JSON,
Schema AST). An exact embedding `(write, read)` satisfies three laws: totality, retraction `read (write a) = some a`,
and exactness `read v = some a → v ≡ write a` modulo an explicit normaliser (`normJ` for JSON key ordering,
`normS` for Schema annotation erasure).

#### Implementation Inventory
| Item | Category | Judgment / Law | Evidence / Decision | Owner / Dep | Next Bounded Action |
|---|---|---|---|---|---|
| `decode-iff` | Proved Witness | `decode j = some v ↔ normJ j = normJ (encode v)` | `Effect4.Schema.decode_iff` (`Codec.lean:1052`) | Core | Exactness modulo key sorting |
| `decode-encode` | Proved Witness | `Canonical v → decode (encode v) = some v` | `Effect4.Schema.decode_encode` (`Codec.lean:1065`) | Core | Retraction on canonical types |
| `of-schema-exact` | Proved Witness | `ofSchema s = some t → normS s = normS (schema t)` | `ofSchema_exact` (`Bridge.lean:492`) | Core | Exactness modulo nine approved keys |
| `of-schema-schema` | Proved Witness | `ReservedFree t → ofSchema (schema t) = some t` | `ofSchema_schema` (`Bridge.lean:412`) | Core | Retraction on closed unreserved types |
| `left-biased-union` | Refuted (Pinned) | Codec exactness on overlapping union variants | `E4-SCHEMA-CE-059` | Schema | Pinned limitation: left-biased variant decode |
| `record-codec-layout` | Required Work (Planned Feature) | Exact codec encoding and decoding for positional record layouts | Decisions Row 165, Data-Wave W5 | Seat W5 | Implement named record field codecs in `ctor 0 [names, values]` |
| `arbitrary-metadata-erasure` | Intentional Exclusion | Unconditional erasure of `effect4/*` metadata keys in `normS` | Decisions Row 179 | Architecture | Excluded: `normS` erases only nine approved annotation keys |

---

### 2.6 Concept 6: Subtyping Algebra & Normalization (`subtyping-algebra`)

#### Semantic Contract
Subtyping on `Ty` forms a preorder with reflexivity and transitivity under `subN`. Normalization
`normalize : Ty → Ty` computes a canonical representative in `CTy`; on canonical types, `subN` forms
a partial order with antisymmetry (`sub_antisymm_canonical`) and a join-semilattice structure.

#### Implementation Inventory
| Item | Category | Judgment / Law | Evidence / Decision | Owner / Dep | Next Bounded Action |
|---|---|---|---|---|---|
| `subn-refl` | Proved Witness | `Ty.subN a a = true` | `TypeAlgebra.lean:1069` | Core | Reflexivity of normalized order |
| `subn-trans` | Proved Witness | `Ty.subN a b = true → Ty.subN b c = true → Ty.subN a c = true` | `TypeAlgebra.lean:1071` | Core | Transitivity of normalized order |
| `subn-equiv-iff` | Proved Witness | `Ty.subN a b = true ∧ Ty.subN b a = true ↔ a.normalize = b.normalize` | `TypeAlgebra.lean:1088` | Core | Kernel of subtyping equivalence |
| `normalize-idem` | Proved Witness | `(a.normalize).normalize = a.normalize` | `TypeAlgebra.lean:1081` | Core | Idempotence of normal form reduction |
| `sub-antisymm-canonical` | Proved Witness | `Canonical a → Canonical b → subN a b = true → subN b a = true → a = b` | `TypeAlgebra.lean:1092` | Core | Antisymmetry on `CTy` |
| `record-app-subtyping` | Required Work (Planned Feature) | Subtyping, join, and normalization laws for record and app constructors | Decisions Row 119, Data-Wave W2/W4 | Seat W2/W4 | Add `Ty.record` and `Ty.app`, extend generator and normalization |
| `optional-field-subtyping` | Required Work (Planned Feature) | Subtyping rules for optional fields and width/depth subtyping | Decisions Rows 177, 178 | Seat W2 | Implement width and depth subtyping order on records |
| `arrow-subtyping` | Intentional Exclusion | Function contravariant/covariant subtyping `Ty.arrow a b ≤ Ty.arrow c d` | Decisions Row 163 | Architecture | Excluded: `Ty` contains no arrow constructor |

---

### 2.7 Concept 7: Initial Algebras & Catamorphic Folds (`initial-algebras-folds`)

#### Semantic Contract
Syntax sorts (`Eff`, `Ty`, `Term`, `Val`, `Representation`) are free objects generated by algebraic signatures.
Every traversal is generated from the sort's signature as a unique catamorphic fold (`cata_eff`, `cata_ty`).
Two folds agree when their algebras agree (`hom_eq_cata_eff`), eliminating ad-hoc induction proofs.

#### Implementation Inventory
| Item | Category | Judgment / Law | Evidence / Decision | Owner / Dep | Next Bounded Action |
|---|---|---|---|---|---|
| `hom-eq-cata-eff` | Proved Witness | Pointwise equality of signature algebra homomorphisms with `cata_eff` | `Fold.lean:1270` | Core | Uniqueness of catamorphism |
| `inhabited-iff-fits` | Proved Witness | Syntactic `inhabited` fold characterizes semantic non-emptiness in `Fits` | `Membership.lean:2613` | Core | Finite syntax inhabitation check |
| `cata-eff-congr` | Proved Witness | Fold congruence over agreeing algebra implementations | `Signature.lean:518` | Core | Equivalence of generated traversals |
| `data-wave-algebra-extension` | Required Work | Extend `EffAlgebra`, `TyAlgebra`, and catamorphisms for new data forms | Decisions Row 182, Data-Wave W2/W4 | Seat W2/W4 | Regenerate fold signatures when adding new `Ty`/`Val` constructors |
| `equi-recursive-unfolding` | Intentional Exclusion | Infinite equi-recursive unfolding in syntactic traversals | Decisions Row 127 | Architecture | Excluded: `Ty` is finite inductive syntax; no cyclic graphs in program ASTs |

---

### 2.8 Concept 8: Context Requirements & Provision (`context-requirements`)

#### Semantic Contract
Ambient capabilities required by an effectful program are tracked by flat requirement rows
`r : Row ServiceKey`. Context satisfaction is simple subset inclusion (`r.Subset ctx.keysRow`).
Layer provision `s.provide t` statically discharges output capabilities, yielding closed programs
when all requirements are met (`provide_closed`).

#### Implementation Inventory
| Item | Category | Judgment / Law | Evidence / Decision | Owner / Dep | Next Bounded Action |
|---|---|---|---|---|---|
| `satisfies-empty` | Proved Witness | `Satisfies ctx Row.empty = true` | `Context.lean:149` | Core | Base case of context satisfaction |
| `satisfies-single` | Proved Witness | `Satisfies ctx (Row.single k) = true ↔ k ∈ ctx.keys` | `Context.lean:153` | Core | Singleton requirement lookup |
| `satisfies-union` | Proved Witness | `Satisfies ctx (r₁ ∪ r₂) = (Satisfies ctx r₁ && Satisfies ctx r₂)` | `Context.lean:164` | Core | Split requirement satisfaction |
| `satisfies-weaken` | Proved Witness | `r.Subset r' → Satisfies ctx r' = true → Satisfies ctx r = true` | `Context.lean:176` | Core | Monotonicity under context extension |
| `provide-discharges` | Proved Witness | `k ∈ t.out → k ∉ t.requires → k ∉ (s.provide t).requires` | `Provision.lean:87` | Core | Capability discharge theorem |
| `provide-closed` | Proved Witness | `t.Closed → s.requires.Subset t.out → (s.provide t).Closed` | `Provision.lean:99` | Core | Closed layer composition |
| `missing-service-exclusion` | Refuted (Repaired) | Frame carrying `missingService` defect crossing closed boundary | `E4-TYPED-CE-008`, Row 117 pt 2 | Core | Closed root rows prevent runtime `missingService` |
| `layer-sharing-contract` | Required Work | Dynamic layer memoization and sharing invariants | `LayerSharingContract.lean`, D2 | Seat D2 / Owner | Reconcile dirty worktree changes on `LayerSharingContract.lean` |
| `comonadic-adjunctions` | Intentional Exclusion | Categorical comonadic indexed adjunctions for context dependence | Decisions Row 117 | Architecture | Excluded: Effect4 uses flat nominal requirement sets |

---

### 2.9 Concept 9: Host Session Protocol & Boundary (`host-session-protocol`)

#### Semantic Contract
Interaction with the host environment is governed by an explicit 4-state protocol automaton
(`idle`, `awaitingAsync`, `parked`, `terminated`). Transitions are validated by `allows`. External
replies commute in session queues and cannot corrupt internal execution.

#### Implementation Inventory
| Item | Category | Judgment / Law | Evidence / Decision | Owner / Dep | Next Bounded Action |
|---|---|---|---|---|---|
| `allows-answer` | Proved Witness | `allows .awaitingAsync (.answerAsync id tok ans) target = true` | `Laws/Run.lean:289` | Core | Valid async reply transition |
| `reply-commute` | Proved Witness | `submit r₁ (submit r₂ s) = submit r₂ (submit r₁ s)` | `HostSession.lean:112` | Core | Commutativity of independent replies |
| `frontier-awaithost` | Proved Witness | Characterization of frontier state matching `.awaitingAsync` | `Frontier.lean:8` | Core | Frontier reason bijection |
| `typed-replay-session` | Required Work | Public typed replay route under keyed host session | Decisions Row 98 | API / Laws | Connect `HostSession` driver to `Typed.replay` |
| `boundary-handle-leak` | Refuted (Repaired) | Internal handle leakage across host answer boundaries | `E4-HOST-CE-007`, Row 97 | Core | Repaired: internal handles rejected at table admission |
| `host-progress` | External Assumption | External driver supplies answers to pending async requests | `docs/core/host-boundary.md` | Host Environment | External assumption: host driver liveness outside closed runtime |

---

### 2.10 Concept 10: Translation & Simulation Metatheory (`translation-simulation`)

#### Semantic Contract
Behavioral agreement between operational and denotational semantics is established as simulation
relations over restricted program fragments: `run_eq_meaning` over `Straight` programs,
`loopAgreement` over `Looped` programs, and `run_eq_ref` on `M7Fragment` with the host table fixed
empty (`root.table = []`) and decision tapes answer-free.

#### Implementation Inventory
| Item | Category | Judgment / Law | Evidence / Decision | Owner / Dep | Next Bounded Action |
|---|---|---|---|---|---|
| `run-eq-meaning` | Proved Witness | `Straight e → Api.run e fuel = finished ∧ exit = meaning e` | `Agreement/Machine.lean:1922` | Core | Operational / denotational agreement on Straight |
| `loop-agreement` | Proved Witness | Replay agreement holds across straight loop steps | `LoopAgreement.lean:42` | Core | Loop execution invariance |
| `run-eq-ref` | Proved Witness | Frame machine replay matches term reference replay at empty table | `Sched.run_eq_ref` (`RuntimeR.lean:211`) | Core | Step simulation on answer-free fragment |
| `m7-route` | Proved Witness (Route) | M7 capstone derived conditionally from M5 and M6 ledger components | `Assembly.lean:1580` (`m7_of_ledger`) | Core | Proves conditional implication, NOT premises |
| `m7-exits` | Open Goal | Replay exit value matches denotational prediction | `Assembly.lean:1774, 1854` (`M7.exits_typed`) | M7 / Capstone | Prove capstone exit agreement goal |
| `m7-stores` | Open Goal | Replay final store matches denotational store state | `Assembly.lean:1778, 1855` (`M7.stores_typed`) | M7 / Capstone | Prove capstone store agreement goal |
| `m7-no-halt` | Open Goal | Replay on answer-free tape never enters halted state | `Assembly.lean:1782, 1856` (`M7.never_halts`) | M7 / Capstone | Prove non-halting capstone goal |
| `m7-exit-handles` | Open Goal | Reified exit handles satisfy validity in final world | `Assembly.lean:1787, 1857` (`M7.exitHandles_valid`) | M7 / Capstone | Prove exit handle validity goal |
| `host-table-simulation` | Intentional Exclusion | Replay agreement under non-empty host tables and external answers | Decisions Rows 138, 95 (DI-57, R6) | Architecture | Deferred to milestone R6: M7 scope is strictly host-free |

---

## 3. The Next Two Useful Implementation Slices

### Slice 1: Data Path — W4 Signed Integer and Binary64 Float Value/Type Append

- **Adapted Semantic Contract**:
  Concept 1 (`store-typing`) and Concept 6 (`subtyping-algebra`). Primitive numeric types are extended
  with machine-width integers and IEEE-754 floating point numbers: `Ty.int64`, `Ty.float64` and their
  corresponding values `Val.int64 (n : Int64)`, `Val.float64 (f : Float)`.
- **Required Judgment or Law**:
  1. Value membership:
     ```lean
     Fits w (Val.int64 n) Ty.int64
     Fits w (Val.float64 f) Ty.float64
     ```
  2. Monotonicity and subtyping invariance:
     `fits_mono` and `fits_subN` extended to cover `Ty.int64` and `Ty.float64`.
  3. Disjointness: `Ty.int64` and `Ty.float64` are distinct leaves in the `CTy` normal form semilattice.
- **Concrete Outcome**:
  Enables first-order storage of 64-bit numeric data, unblocking W5's exact codec implementations
  for signed integers and floating point values.
- **Prerequisites and Owner**:
  - Owner: Seat W4 (`docs/research/2026-10-01-data-wave/README.md`).
  - Prerequisite: W2 generator hand-back (`make gen-data`) integrated.
- **Positive Example and Rejecting Control**:
  - Positive example: `Fits w (Val.int64 42) Ty.int64 = True`.
  - Rejecting control: `Fits w (Val.int64 42) Ty.float64 = False`; `Ty.subN Ty.int64 Ty.float64 = false`.
- **Completion Evidence**:
  Narrow compilation of `Effect4.Machine.Value`, `Effect4.Program.Ty`, `Effect4.Laws.Program.Typed.Membership`,
  and passing unit tests in `Test/Program/DataWaveNumeric.lean`.

---

### Slice 2: Assurance Path — D2 Constructor Group Compatibility for `onFailure`

- **Adapted Semantic Contract**:
  Concept 2 (`residual-program-typing`). Per-construct sequencing compatibility for error recovery
  control brackets (decisions row 148). The error handler branch must be typed at the enclosing
  error and answer types under all permitted error exits.
- **Required Judgment or Law**:
  `onFailure_typed`:
  ```lean
  theorem onFailure_typed (root : ProgramSource) {w : World} {ty : EffTy} {a : RProgram}
      {h : Val → RProgram} (ha : TypedProg root w ty a)
      (hh : ∀ w', w.leHost w' → ∀ err, Fits w' err ty.error → TypedProg root w' ty (h err)) :
      TypedProg root w ty ((guardR .onError a).bind (handleR h))
  ```
- **Concrete Outcome**:
  Discharges the `onFailure` constructor obligation in M5's denotational typing ledger, directly
  advancing the proof of `denoteR_typed` (`Assembly.lean:1650`).
- **Prerequisites and Owner**:
  - Owner: Seat D2 (`docs/research/2026-10-01-semantics/seat-B/brief-gemini-implementation.md`).
  - Prerequisite: Owner Bookkeeping repair (`src/Effect4/Laws/Program/Typed/Commands/Bookkeeping.lean`) integrated.
- **Positive Example and Rejecting Control**:
  - Positive example: Program with valid `catchAll` handler types under `onFailure_typed`.
  - Rejecting control: Catch-all handler attempting to return a value whose type does not match `ty.answer`
    is rejected; `TypedProg` derivation fails.
- **Completion Evidence**:
  `lake build Effect4.Laws.Program.Typed.Seq`, zero new axioms outside `[propext, Quot.sound]`, and
  successful registration of `on-failure-typed` as a proved witness in `SemanticsRegistry.lean`.
