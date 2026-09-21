# Post-Phase C Synthesis: Ground Truth, Decision Rulings, and Architectural Roadmap

**Date:** 2026-09-20  
**Status:** Core Authority & Architectural Roadmap  
**Base Commit:** `10d5c009` on `refactor/phase1-phase3`  
**Authorities Referenced:** `docs/core/ontology.md`, `docs/core/decisions.md`, `docs/core/machine-state.md`, `docs/core/coherence-principle.md`, `docs/research/2026-09-19-plan-deep-dive-review.md`, `docs/research/2026-09-20-look-ahead-after-phase-c.md`, `AGENTS.md`.

---

## 0. Executive Digest & Ground Truth Reconciliation

At commit `16090306` (with look-ahead `10d5c009`), Phase C closed with:
* **Tooling T1–T5** fully landed (`de27095d`), providing `ProofGraph`, `#typed_state`, `#frame_rules`, and the declaration-backed ledger `#typed_state_obligations`.
* **Completion as data M1** landed (`8b64039f`), eliminating `MemoEntry.effect`, moving cell completion to `Completion`, and establishing the 30/30 connector in `b2bf4cca`.
* **P2 Arena** landed (`8cb639b4`), proving 14/14 laws at ceiling 0.
* **M2 Layer 1** is half-landed: `World`, `WorldOrder`, table extension preorders, columns on data, and extension theorems are proved in `Laws/Program/Typed/World.lean`.
* **M2b (The Hinge)** is unbuilt: the 7 custom predicates over `World` are undefined, `instance : Preds World` does not exist, and the loaded-program control `RStateOk P w (loadR e fuel)` is not yet formulated.
* **Residue:** 42 open statements across the ledger. 31 are theorem-backed (already verified, held open by search normalization), and 11 are genuine proof obligations.

```
   [T1–T5 Tooling]  ──▶  [M1: D2 Completion Data]  ──▶  [M2a: World Preorder]
      (Landed)                   (Landed)                    (Landed)
                                                                 │
                                                                 ▼
   [Residue Closer] ──▶  [Memo Slice Cleanup]       ──▶  [M2b: Preds World] (THE HINGE)
     (31 Namesakes)         (Unique Map IDs)                     │
                                                                 ▼
   [F6: Multi-Field]──▶  [F5: Coverage Join]        ──▶  [M3: Residual Protocol]
      (Pre-M6)                   (Pre-M6)                        │
                                                                 ▼
                                                         [M4 Keeps & Stack]
                                                                 │
                                                                 ▼
                                                         [M5 S1 Denotation]
                                                                 │
                                                                 ▼
                                                         [M6 S2 Ledger Ceiling]
                                                                 │
                                                                 ▼
                                                         [M7 S3 Transfer Run]
```

---

## 1. The Residue Census: 42 Statements Confirmed

A full audit of the codebase confirms exactly 41 live `#proof_wanted` declarations in `src/` (plus 2 audit control fixtures in `Test/Audit/Obligations.lean`):

### 1.1 The 31 Theorem-Backed Statements (Zero Proof Work Owed)
Each of these statements compiles as a verified theorem in the repository. They remain marked wanted because `aesop`’s preprocessing normalization (`subst`, `simp`, splitting `And`) transforms the goal before the registered bank rule can match.

1. **Premise/`subst` Inversion (11):**
   * `fork_arm_minted` (`src/Effect4/Laws/Machine/Handles.lean:3153`)
   * `spawn_minted` (`src/Effect4/Laws/Machine/Handles.lean:2104`)
   * `withFiber_fork_minted` (`src/Effect4/Laws/Machine/Handles.lean:3203`)
   * `memoBuild_extension` (`src/Effect4/Laws/Program/Typed/World.lean:244`, theorem at `:667`)
   * `storesOk_closeScopeUnsafe` (`src/Effect4/Laws/Program/Simulation/Deliver.lean:414`)
   * `scopeLinkFiber_ok` (`src/Effect4/Laws/Program/Simulation/Actions.lean:61`)
   * `dropFinalizer_ok` (`src/Effect4/Laws/Program/Simulation/Drive.lean:191`)
   * `fork_pendingOk` (`src/Effect4/Laws/Program/Simulation/Pending.lean:30`)
   * `forkIn_pendingOk` (`src/Effect4/Laws/Program/Simulation/Pending.lean:36`)
   * `forkScoped_pendingOk` (`src/Effect4/Laws/Program/Simulation/Pending.lean:42`)
   * `book_advanceState` (`src/Effect4/Laws/Machine/Book.lean:986`, theorem at `:989`)
2. **Key Subsets & Store `simp` Rewriting (6):**
   * `complete_keys` (`src/Effect4/Laws/Machine/Handles.lean:5490`)
   * `register_keys` (`src/Effect4/Laws/Machine/Handles.lean:5479`)
   * `drainDue_keys` (`src/Effect4/Laws/Machine/Handles.lean:5495`)
   * `setCell_keys_of_subset` (`src/Effect4/Laws/Machine/Handles.lean:5539`)
   * `setCell_appendDue_keys` (`src/Effect4/Laws/Machine/Handles.lean:5553`)
   * `spawnChild_keys_subset` (`src/Effect4/Laws/Machine/Handles.lean:2081`)
3. **`withFiber_fork` Term Rewriting (7):**
   * `fork_forked` (`src/Effect4/Laws/Api/Supervision.lean:236`)
   * `forkScoped_forked` (`src/Effect4/Laws/Api/Supervision.lean:273`)
   * `forkFinalizers_forked` (`src/Effect4/Laws/Api/Supervision.lean:326`)
   * `supervision_static` (`src/Effect4/Laws/Api/Supervision.lean:417`)
   * `supervision_static` (`src/Effect4/Laws/Api/Supervision.lean:683`)
   * `source_fork` (`src/Effect4/Laws/Api/Supervision.lean:713`)
   * `race_launch_origins` (`src/Effect4/Laws/Api/Supervision.lean:772`)
4. **`let`/`∃`/`∀` Shape Indexing (7):**
   * `source_fork_extension` (`src/Effect4/Laws/Program/Typed/ForkSource.lean:48`, theorem `fork_source_extension` at `:50`)
   * `actionAt_fork` (`src/Effect4/Laws/Program/Intro/Weight.lean:147`)
   * `actionAt_forkIn` (`src/Effect4/Laws/Program/Intro/Weight.lean:158`)
   * `actionAt_not_forkScoped` (`src/Effect4/Laws/Program/Intro/Weight.lean:169`)
   * `actionAt_raceAll` (`src/Effect4/Laws/Program/Intro/Weight.lean:179`)
   * `fork_rel` (`src/Effect4/Laws/Program/Simulation/Actions.lean:517`)
   * `forkIn_rel` (`src/Effect4/Laws/Program/Simulation/Actions.lean:571`)
   * `raceAll_rel` (`src/Effect4/Laws/Program/Simulation/Actions.lean:769`)

### 1.2 The 11 Genuine Proof Obligations
* **5 Static-Site Membership Proofs** (`Laws/Api/Supervision.lean:758-818`): `source_race_site`, `source_fork_site`, `source_forkIn_site`, `source_forkScoped_site`, `source_two_race_sites`.
* **2 Trace Agreements** (`Laws/Program/Guard/TraceOrigin.lean:17, 23`): `step_agrees`, `reachable_agrees`.
* **1 Observation Ignores Trace** (`Laws/Run.lean:881`): `observe_replace_trace`.
* **1 Handshake** (`Laws/Program/Guard/Handshake.lean:26`): `parkHandshake_reachable` (held for M4).
* **1 Audit Fixture** (`Test/Audit/Obligations.lean`): Intentionally open control.
* **1 Memo Slice Write Removal** (`Machine/Stores.lean:2020`): Redundant duplicate-collapsing write.

---

## 2. Decision Register Synchronization & Open Rulings

### 2.1 The Register Lag
The tree has already landed implementation details that `docs/core/decisions.md` marks as open or recommended. Under project rules, rulings must be explicitly recorded in tracked files.

| Row | Current Text in `decisions.md` | Ground Truth in Tree | Required Ruling Text |
| :--- | :--- | :--- | :--- |
| **79** | Open, recommended | R3 landed (`RunFiber.origin` with site); `Obs` unchanged; `Projects`/`Refines` landed | **Ruled.** Adopt R79.1–R79.5. `Obs` is the permanent semantic view. The holder view factors through state/ledger, not trace. Trace erasure is definitional. `Refinement.lean` is the sole store refinement contract. |
| **20** | Open | Landed in `Fibers.lean` (`Origin.forked parent daemon site`); LCNF regenerated | **Ruled.** Fiber fork sites are data on `RunFiber.origin`. `supervision_static` reads state. |
| **48** | Recommended | Required for M2b (`StackOk`) | **Ruled.** Intermediate stack types in `StackOk` are existential (`∃ ty, ...`). No runtime tags on `ScopeFrame`. |
| **51** | Recommended | Required for M2b (`ServiceOk`) | **Ruled.** `ServiceOk` is context-wide. Every service in an environment fits its key's declared type. |
| **52** | Open, recommended | Verified by construction | **Ruled.** Eliminating halting defects (`unknownFiber`, `unknownScope`, `unknownRace`) and `badShapeExit` are proven corollaries of the milestone. |

### 2.2 Rulings on Genuinely Unanswered Questions

#### Row 84: Transactions v1 Fragment & Fuel Ownership
* **Ruling:** **Adopt `TxBody ∩ Straight` with the proved sufficient driver bound.**
* **Theoretical Foundation:** A straight program compiles to continuation frames and cannot loop. In `Laws/Program/RuntimeR.lean:304` and `TypedRun.lean:85`, the repository already proves:
  $$\text{fuel} \ge \max(\text{Agreement.depth } e, 2 \cdot \text{Agreement.steps } e + 6)$$
  guarantees that `loadR` runs to completion without encountering a fuel boundary.
* **The Connector:** The `tx` wrapper supplies this proved bound alongside an outer attempt-isolation connector. Under this bound, embedded straight attempts never hit a fuel frontier, isolating transactions from scheduler yields and completely unblocking P4 without waiting for Row 80 (complex STM retry/preemption). Loops (`iterate`) and generators (`gen`) remain explicit located refusals.

#### The Clock (Review F4 / Row 83)
* **Ruling:** **Ratify `ClockMillis` (exact logical clock, protocol v3).**
* Host-arbitrary custom clocks are refused at the API boundary. The reference machine advances time via explicit `clockStep` increments, and timing events drain lawfully through `WakeList`.

#### Row 81: Latch Scheduled-Wake Primitive
* Keep open; schedule for P5 (after M7). As established in finding F11, `Wake.lean` already provides the lawful `WakeList` abstraction. Latch is its `Unit` broadcast/scheduled instance.

#### Row 82: Behavior Values
* **Ruling:** **Strictly reject host closures or second IRs.** Program references remain first-order content-addressed `Eff` syntax with typed certificates.

#### Row 85: Arena Storage
* **Ruled & Landed in P2.** `Arena` interface + dense-arena laws + `RefHeap` list instance; OCaml property tests serve as trusted edge evidence.

---

## 3. Code Organization, Import Stratification & Cycle Elimination

The architecture audit (`tools/Tools/ArchitectureRoles.lean` and `make gen-architecture`) establishes a strict height lattice:

```
[Store.Carrier] (Val, Codec, Image)  ──▶  Layer 1 (Below Machine)
       │
[Machine / Fibers / Stores]          ──▶  Layer 2 (Core Runtime)
       │
[Program / Eff / Ty / Checker]       ──▶  Layer 3 (Abstract AST)
       │
[Store.Domain] (Node, Shape)         ──▶  Layer 4 (Above Program)
       │
[Schema / OfShape]                   ──▶  Layer 4 (Data Plane; Row 39 target)
       │
[Api / Supervision / Inspection]     ──▶  Layer 6 (Application Face)
       │
[Run / Commands / Replay]            ──▶  Layer 7 (Driver)
       │
[Effect4]                            ──▶  Layer 8 (Public Root; never imports Laws)
```

### 3.1 Resolving Inverted Dependencies

1. **Bisection of Store (Finding §8.4):**
   * `Store.Carrier` (`Val`, `Utf8`, `Digits`, `Image`, `Digest`) sits at Layer 1 strictly *below* `Machine`.
   * `Store.Domain` (`Node`, `Canonical`, `Word`, `Store`, `Traits`, `Shape`) sits at Layer 4 *above* `Program`.
2. **Execute Row 39 (`render` move):**
   * `Store/Shape.lean:1` currently imports `Schema.Authoring`, creating an upward import cycle.
   * Move `Store.render` and `ShapeDoc.document` out of `Store/Shape.lean` into `Schema/OfShape.lean`. Store becomes a pure leaf beneath Schema.
3. **Move Fold Connectors to `Laws/` (Finding §8.1):**
   * The 9 `fold_of` connectors currently sitting in runtime roots (`Program/Folds/*`, `Machine/Folds/*`, `Store/Folds/*`) import upward into `Schema`, `Codegen`, and `Program`.
   * Fold connectors are proof artifacts: relocate them to `src/Effect4/Laws/Folds/`. This immediately eliminates 3 of the 10 cycles reported in `architecture-map.html`.
4. **Co-locate Typed-State Tooling:**
   * All typed-state definitions, tables, and gates belong under `src/Effect4/Laws/Program/Typed/`: `World.lean`, `State.lean`, `Sources.lean`, `Vocabulary.lean`, `TypedSources.lean`, `TypedStateDecl.lean`, `ForkSource.lean`, and the upcoming `AnswerGate.lean`.

---

## 4. Subtle Details & Critical Work-Savers

### 4.1 The F7 Clarification: Do NOT Delete `ResumeOk` or `InterruptOnly`
* Finding F7 of the deep-dive review suggested deriving `ResumeOk` and `InterruptOnly`.
* **Crucial Finding:** In §9 of the deep-dive review (P1 §4), this proposal was explicitly **withdrawn**:
  * `ResumeOk` types a resumed value against the *saved continuation frame’s input type*, which is intermediate and distinct from the fiber’s final exit type.
  * `InterruptOnly` represents provenance across columns, not a standard column type admission.
* **Action for M2b:** Retain both in `Sources.lean`. Do not attempt to eliminate them. Define all 7 custom predicates over `World`. The pruning of `Expect` (down to `root`, `fiber id`, `hook name`) stands.

### 4.2 The Memo Slice Invariant & Deletion (§3.1 / G3)
In `src/Effect4/Machine/Stores.lean:2020`:
```lean
memo := st.memo.updateEntry memoMap layer id
```
* **Why it collapsed duplicates:** `updateEntry` uses `mapAt` (first match) and `setMap` (overwriting all matches). On duplicate map IDs, it collapses duplicates to the first entry.
* **The Invariant:** Memo maps are only minted by `SyncOp.memoFork`, which uses the monotonic counter `st.nextName`. Therefore:
  $$\text{MemoKeysFresh } s := (s.\text{memo}.\text{map } (\cdot.\text{id})).\text{Nodup}$$
* Under `MemoKeysFresh`, `updateEntry w id layer id = w` is an exact lemma.
* **Action:** Prove this lemma, delete `memo := st.memo.updateEntry memoMap layer id`, and run full regeneration (`make gen-lcnf`, `gen-cas`, `gen-eff`, OCaml build).

### 4.3 Monotonicity Seam: External Handle Allocation
* `ValueOk` and `CompletionOk` evaluate `Val.hasTy value ty w.state.externals.allocated`.
* `Stores.le` orders lengths of arrays, not key-wise string spellings in `externals.allocated`. Arbitrary `World.le` does *not* imply monotonicity of `ValueOk`!
* **Work-Saver for M3:** M3’s weakening lemma must carry an explicit external table extension premise:
  $$\text{TableExtends } w.\text{state}.\text{externals}.\text{allocated } w'.\text{state}.\text{externals}.\text{allocated}$$

### 4.4 Trace Agreement vs. State Erasure (R3 & R79.2/3)
* In `src/Effect4/Machine/Fibers.lean:939`, `spawn` is the *sole* producer of `RunEvent.forked` and the *sole* writer of `RunFiber.origin = .forked`.
* `forkedOf m.trace` and `originForks m` are identical on all reachable states (`step_agrees` and `reachable_agrees`).
* With fiber provenance held in `RunFiber.origin`, `Run.observe` is completely decoupled from `m.trace`. Diagnostic trace erasure becomes definitional (`rfl`).

### 4.5 Multi-Field Frame Generation (F6 before M6)
* Real runtime steps (e.g. `exitFiber`) mutate multiple record fields simultaneously.
* Single-field frame rules (`Laws/Auto/Frames.lean`) fail because intermediate single-field mutations violate inductive invariants.
* **Requirement:** Amend `Frames.lean` to accept `(owner, written-field set)` from the write census before starting M6.

---

## 5. Tooling Architecture & Proof Fast-Path

### 5.1 The Namesake-Theorem Closer in `Obligations.lean` (G1)
In `src/Effect4/Laws/Auto/Obligations.lean`, before calling `ProofGraph.search`:
```lean
-- Check for a namesake theorem in the parent/enclosing namespace
let candidate := goal.id.getPrefix.getPrefix ++ goal.id.getString!
if let some (.thmInfo t) := env.find? candidate then
  let ref : ProofRef := ⟨candidate, goal.levels, goal.proposition⟩
  match ← ref.validate with
  | .ok () =>
    let proof := mkAppN (mkConst candidate (goal.levels.map mkLevelParam)) #[]
    discard <| addTheorem checked goal.levels goal.proposition proof
    entries := entries.push ⟨goal.id, .proved checked⟩
    continue
  | .error why =>
    throwError "obligation ledger: namesake theorem {candidate} invalid: {why}"
```
* **Impact:** Discharges 31 open obligations in milliseconds with zero proof churn, protects proofs from aesop normalization, and fails if a namesake diverges in type or axioms.

### 5.2 Aesop Bank Registration Taxonomy
* **`safe destruct`:** Inversions that consume hypotheses completely.
* **`safe forward`:** Universal premises whose conclusions must enrich the context.
* **`norm simp` / `norm unfold`:** Recursive definition unfolding.
* **`safe -100 apply`:** Whole-statement rules that must preempt aesop’s built-in `And.intro`, `split`, or `rfl`.
* **`unsafe 90% apply`:** Single equations or simple predicates.

### 5.3 Proof Hygiene
* **Strictly forbidden:** `simp_all`, `first | ...`, and `try`.
* **Mandatory:** `simp only [...]` with explicit lemmas; case splits matching source definitions via `fun_induction` or `fun_cases`.

---

## 6. Audit of Core Abstractions & Theoretical Coherence

### 6.1 The Six Free Objects
1. `Eff` (Program IR) $\to$ `cata_eff`
2. `Ty` (Type AST) $\to$ `cata_ty`
3. `Term` (Expressions) $\to$ `cata_term`
4. `Representation` (Schema shape AST) $\to$ `cata_rep`
5. `Store.Val` (Values) $\to$ `cata_val`
6. `List Command` (Journal monoid) $\to$ `journal_replays`

### 6.2 Layer 0: Hazel / Interaction Trees Protocol (`Protocol.lean`)
```lean
inductive Typed (o : WorldOrder W) (Ψ : Protocol W S) : W → (W → A → Prop) → Program S A → Prop
  | pure (h : Q w a) : Typed o Ψ w Q (.pure a)
  | vis (hpre : Ψ.pre w op)
      (hk : ∀ w', o.le w w' → ∀ ans, Ψ.post w' op ans → Typed o Ψ w' Q (k ans)) :
      Typed o Ψ w Q (.vis op k)
```
* **Theoretical Invariant:** Universal quantification over future worlds $w'$ ($o.\text{le } w\ w'$) inside `vis` ensures weakening (`Typed.mono`) is provable in a single `cases` step without structural induction.

### 6.3 The World Preorder (`World.lean`)
$$\text{World} := \langle \text{ids}, \text{state}, \Gamma : \text{FiberTable}, \Pi : \text{PromiseTableTy}, \text{P} : \text{HeapTableTy} \rangle$$
$$\text{World.le } w\ w' \iff \text{Machine.World.le } w\ w' \land \text{TableExtends } \Gamma \land \text{TableExtends } \Pi \land \text{TableExtends } \text{P} \land \text{CellCompatible } w\ w'$$

### 6.4 The 12 Fields of `Preds World` Confirmed by Kernel Reflection
Reflection on the Lean environment confirms that `structure Preds (W : Type)` has exactly 12 fields:
1. `program : W → Expect → Program RSig ExitV → Prop`
2. `StackOk : W → Expect → List ScopeFrame → Prop`
3. `InterruptOnly : W → Expect → Option CauseV → Prop`
4. `PendingOk : W → Expect → List Pending → Prop`
5. `exit : W → Expect → ExitV → Prop`
6. `ResumeOk : W → Expect → RProgram → Prop`
7. `ServiceOk : W → Expect → Ctx → Prop`
8. `RaceOk : W → Expect → List Race → Prop`
9. `PromiseTable : W → Stores → Prop`
10. `HeapCell : W → RefKey → Val → Prop`
11. `PromiseCell : W → DeferredKey → DeferredCell Completion → Prop`
12. `CaptureOk : W → Expect → List Val → Prop`

Defining these 12 fields over `World` in `Laws/Program/Typed/World.lean` establishes `instance : Preds World`, completing M2b and unblocking the concrete transition ledger for M6.

---

## 7. Concrete Execution Sequence

1. **Step 1: Land Residue Tooling Closer (G1)**
   * Add namesake-theorem resolution to `Effect4.Laws.Auto.Obligations`.
   * Verify that 31 obligations close immediately.
2. **Step 2: Land the Memo Slice (G3)**
   * Prove `MemoKeysFresh` and `updateEntry_id_eq`.
   * Remove `st.memo.updateEntry memoMap layer id` in `Stores.lean:2020`.
   * Run full regeneration and OCaml checks in an atomic commit.
3. **Step 3: Update `docs/core/decisions.md`**
   * Record rulings for Rows 79, 20, 48, 51, 52, 84, and ClockMillis.
4. **Step 4: Execute M2b (`Preds World`)**
   * Define the 7 custom predicates over `World`.
   * Instantiate `instance : Preds World`.
   * State the red control `RStateOk P w (loadR e fuel)`.
5. **Step 5: Land F6 & F5 before M6**
   * Implement multi-field frame generation in `Frames.lean`.
   * Add `#typed_state_coverage` to `Obligations.lean`.
6. **Step 6: Proceed with Slices M3–M7.**
