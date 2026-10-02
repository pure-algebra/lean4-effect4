# The Effect4 Chapter Table: Mapping the Language to TAPL & ATTAPL

This document is the exhaustive formal catalog of the Effect4 language against Benjamin Pierce's *Types and Programming Languages* (TAPL, 2002), *Advanced Topics in Types and Programming Languages* (ATTAPL, 2005), and foundational literature.

Every judgment and theorem names its exact Lean declaration at HEAD (`69c78069`, re-pinned at `6b3f2c92`), its file:line citation, its evidence status (**proved** at `[propext, Quot.sound]`, **tested**, **reading**, or **open** as a declared ledger obligation), its ledger scope, and its governing decisions rows.

---

## 1. Summary Matrix of the 17 Chapters

| Chapter ID | Book Reference | Title | Primary Judgments | Core Theorems (Proved / Open) | Ledger Scopes | Decisions Rows |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| `tapl-03-evaluation` | TAPL ch. 3, pp. 31–43 | Operational Semantics & Abstract Machines | `driveStep`, `stepDecisionState`, `replayEval`, `denoteR` | `run_eq_ref` (proved), `run_eq_meaning` (proved), `replay_unique` (proved) | `M1Actions`, `M1Origin`, `M1Evaluate`, `M1Clock`, `M1Drive` | 91–94, 110, 146, 150; DB-03, DB-04 |
| `tapl-08-typed-arith` | TAPL ch. 8, pp. 91–98 | Type Safety, Progress, & Invariant Preservation | `MachineTyped` ($J$), `ConfigTyped` ($I$), `StepPreserves`, `MachineLive` | `machineTyped_not_halted` (proved), `stepKeeps_of_stepPreserves` (proved), `m7_of_ledger` (proved); 11 `M6Ledger` proved / 9 open | `M6Ledger`, `M6Edits`, `M7` | 106, 107, 133, 134, 138, 139, 180, 181 |
| `tapl-09-stlc-cut` | TAPL ch. 9, pp. 99–112 | Pure Program Typing, Inversion, & Decision | `HasTy`, `check`, `wellTyped` | `check_sound` (proved), `check_complete` (proved), `hasTy_unique` (proved), `hasTy_weaken` (proved) | (AxiomGate Core) | 104, 105, 163; DB-08 |
| `tapl-11-extensions` | TAPL ch. 11, pp. 117–152 | Structural Extensions: Records, Variants, Iteration | `Ty.prod`, `Ty.record`, `Ty.union`, `Ty.list`, `Term.record`, `Eff.iterate` | `sub_prod_mono` (proved), `inv_iterate` (proved), `conv_fixpoint` (proved), `inhabited_iff_fits` (proved) | `M3aAdmissionObligations` | 119, 121, 125, 126, 127, 130, 157, 159, 160, 165, 166 |
| `tapl-13-references` | TAPL ch. 13, pp. 153–178 | First-Order Mutable References & Store Typings | `World`, `World.le`, `WorldValid`, `RefDeclared`, `ScopeLive`, `StoreTyped` | `fits_mono` (proved), `scopeLive_mono` (proved), `storeStep_typed` (proved), 66 `M3bAdequacy` proved / 8 open | `M2Validity`, `M3bWorld`, `M3bAdequacy` | 44, 45, 96, 136, 156; DB-07, DB-16 |
| `tapl-14-exceptions` | TAPL ch. 14, pp. 179–186 | Typed Failures, Cause Algebras, & Defect Soundness | `ExitOk`, `FitsExit`, `NoShapeDefect`, `ShapeFree` | `fitsExit_mono` (proved), `noShapeDefect_failure_iff` (proved), `exitHasTy_of_fitsExit` (proved); `M7.exits_typed` (open) | `M7`, `M3bAssembly` | 107, 117, 120, 151, 152; DB-07 |
| `tapl-15-subtyping` | TAPL ch. 15, pp. 187–208 | Algorithmic Subtyping, Join-Semilattices, Variance | `Ty.sub`, `Ty.subN`, `Ty.isMember` | `sub_never` (proved), `sub_unknown` (proved), `sub_sound` (proved), `sub_not_complete` (proved), `fits_sub` (proved) | (AxiomGate Core) | 137, 177, 178; DB-15 |
| `tapl-16-metatheory-subtyping` | TAPL ch. 16, pp. 209–224 | Subtyping Metatheory & Normal-Form Algebra | `CTy`, `CTy.join`, `Ty.normalize` | `sub_trans` (proved), `sub_antisymm_normal` (proved), `subN_equiv_iff` (proved), `instLawfulOrderSup` (proved) | (AxiomGate Core) | 137, 177 |
| `tapl-19-nominal` | TAPL ch. 19, pp. 245–259 | Nominal Handle Types & Class Identity | `Ty.handle`, `Ty.app`, `HandleFits`, `ExitHandlesValid` | `sub_handle` (proved), `handles_minted` (proved), `exitHandles_valid_of_registered` (proved); `M7.exitHandles_valid` (open) | `M7` | 97, 158, 180 |
| `tapl-20-recursive` | TAPL ch. 20, pp. 261–280 | Recursive Types & Inhabitance Metatheory | `Ty.inhabited`, `AdmittedProgram.columnsTable` | `inhabited_of_fits` (proved), `inhabited_of_hasTy` (proved), `inhabited_iff_fits` (proved) | `M3aAdmissionObligations` | 124, 127, 149 |
| `tapl-22-reconstruction` | TAPL ch. 22, pp. 317–338 | Type Inference & Template Matching | `Ty.infer`, `matchTemplate`, `matchTemplateArgs`, `Widens` | `matchTemplate_sound` (proved), `infer_widens` (proved), `infer_closed` (proved) | (AxiomGate Core) | 42, 43, 155, 183 |
| `tapl-23-prenex` | TAPL ch. 23, pp. 339–358 | Prenex Polymorphic Templates & Instantiation | `Ty.var`, `instantiate`, `Row.instantiate` | `NativeOp.row_closed` (proved), `templateAdmissible_of_closed` (proved), `rowTy_closed` (proved) | (AxiomGate Core) | 42, 43, 163 |
| `attapl-03-effects` | ATTAPL ch. 3, pp. 87–130 | Effect Signatures, Requirement Rows, & Coeffects | `Row`, `RowTable`, `keysRow`, `satisfies`, `EffTy.requires` | `merge_rows_comm` (proved), `provide_closed` (proved), `provide_provide_rows` (proved), `satisfies_iff_subset_keysRow` (proved) | `D12` | 111, 115, 116, 117; DB-17 |
| `attapl-08-logical-relations` | ATTAPL ch. 8, pp. 343–388 | Kripke Logical Relations & Protocol Weakest Preconditions | `Fits`, `TypedProg`, `FrameAccepts`, `SavedOk`, `DenotesTyped` | `fits_mono` (proved), `typedProg_mono` (proved), `popR_typed` (proved), `seq_typed` (proved); `denoteR_typed` (open) | `M3bWorld`, `M4Stack`, `M5Hooks`, `M3bAssembly` | 96, 135, 148, 170, 175; DB-16 |
| `boundary-embeddings` | Foster 2007; Rendel 2010 | Invertible Syntax Descriptions & Exact Embeddings | `Canonical`, `Bridge.schema`, `Bridge.ofSchema`, `decodeRaw`, `printT`, `read` | `ofVal_toVal` (proved), `decode_exact` (proved), `decode_iff` (proved), `ofSchema_exact` (proved), `read_print` (proved) | `Test.Contracts` | 128, 169, 179; DB-15 |
| `initial-algebra` | GTWW 1977; Meijer 1991 | Initial Algebras, Catamorphisms, & Coherence | `cataFam`, `cata_eff`, `cata_ty`, `cata_term`, `build`, `view` | `hom_eq_cata_eff` (proved), `hom_eq_cata_ty` (proved), `cata_build` (proved), `build_view` (proved) | (AxiomGate Core) | 143, 171, 173, 182; DB-01 |
| `machine-concurrency` | Harper PFPL ch. 28; Wright 1994 | Reactive Fiber Runtime, Defunctionalization, & Session | `RunMachine`, `Session`, `Guarded`, `DecisionLift`, `FoldLift`, `Projects`, `Refines` | `driveState_lift` (proved), `advance_step` (proved), `projects_compose` (proved), `bookMeans_obs` (proved), `step_agrees` (proved) | `M1Actions`..`M1Drive`, `M4Handshake`, `M6Ledger`, `M7` | 91–94, 95–101, 110, 134, 139, 156; DB-05, DB-13, DB-14 |

---

## 2. Exhaustive Chapter Specifications

### Chapter 1: `tapl-03-evaluation`
- **Book Citation:** TAPL Chapter 3: Untyped Arithmetic Expressions (§3.1 Syntax, §3.2 Induction, §3.5 Evaluation, pp. 31–43); PLF *Smallstep*.
- **Title:** Operational Semantics, Reduction Relations, and Abstract Machines
- **Judgments of Ours:**
  - `driveStep` ([`Machine/Fibers.lean:1846`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Machine/Fibers.lean#L1846)): Deterministic step function on the synchronous fiber machine $\mathcal{M} \to \mathcal{M}' \times \text{List } \text{RCmd}$.
  - `stepDecisionState` ([`Machine/Fibers.lean:2111`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Machine/Fibers.lean#L2111)): Multi-fiber decision stepping parameterized by external decision tape $\text{List Decision} \to \mathcal{M} \times \text{List Decision}$.
  - `denoteR` ([`Laws/Program/DenoteR.lean:799`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/DenoteR.lean#L799)): First-order elaboration of scoped syntax into free-monad interaction trees with bracket markers.
  - `replayEval` ([`Laws/Machine/Approximation.lean:19`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Machine/Approximation.lean#L19)): Deterministic fold of the decision tape over the abstract machine.
  - `BMeans root m₁ m₂` ([`Laws/Program/RuntimeR.lean:239`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/RuntimeR.lean#L239)): Lock-step forward simulation relation between compiled frame machine $m_1$ and term reference machine $m_2$.
- **Theorems:**
  - `run_eq_meaning`: **proved** ([`Laws/Program/Agreement/Machine.lean:1922`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Agreement/Machine.lean#L1922)): On `Straight` programs, machine run observation equals denotational meaning.
  - `loopAgreement`: **proved** ([`Laws/Program/Agreement/Loop.lean:839`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Agreement/Loop.lean#L839)): On `Looped` programs, iterative machine evaluation agrees with Kleene limit semantics.
  - `run_eq_ref`: **proved** ([`Laws/Program/RuntimeR.lean:211`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/RuntimeR.lean#L211)): At the empty host table, the compiled machine replay equals the reference machine replay.
  - `replay_unique`: **proved** ([`Laws/Api/Runner.lean:157`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Api/Runner.lean#L157)): Uniqueness of the action of journal words on runner states.
  - `journal_replays`: **proved** ([`Laws/Run.lean:184`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Run.lean#L184)): Reconstruction of machine execution traces from event-sourced journals.
  - `Beh_fuel_irrelevant`: **proved** ([`Laws/Program/RuntimeR.lean:121`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/RuntimeR.lean#L121)): Behavior observations are independent of surplus fuel.
- **Ledger Scopes:** `M1Actions`, `M1Origin`, `M1Evaluate`, `M1Clock`, `M1Drive` ([`Laws/Program/Simulation/Actions.lean:830-831`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Simulation/Actions.lean#L830-L831), [`Evaluate.lean:1037`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Simulation/Evaluate.lean#L1037), [`Drive.lean:1146-1147`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Simulation/Drive.lean#L1146-L1147)).
- **Decisions Rows:** Rows 91–94 (fork ledger & trace agreement), Row 110 (generic step lifts), Row 146 (observation finality not claimed), Row 150 (`FoldLift` over 8 premises replacing 6 fold-level inductions), DB-03 (tape determinism), DB-04 (Elgot iteration).
- **Modules Covered:** `Machine/Fibers.lean`, `Machine/Stores.lean`, `Laws/Machine/Lift.lean`, `Laws/Machine/Book.lean`, `Laws/Machine/Approximation.lean`, `Laws/Program/RuntimeR.lean`, `Laws/Program/InterpR.lean`, `Laws/Program/DenoteR.lean`, `Laws/Program/Agreement/*.lean`.
- **The Language Cut:**
  TAPL Chapter 3 formalizes evaluation via small-step inductive rewriting relations on syntax terms ($t \to t'$). Effect4 rejects small-step term reduction for effectful code: programs are immutable tree data (`Eff`), evaluated through an explicit defunctionalized machine (`RunMachine`) carrying stack continuations (`RSaved`), while all scheduling, timing, and host non-determinism are factored out into an external decision tape (`List Decision`).

---

### Chapter 2: `tapl-08-typed-arith`
- **Book Citation:** TAPL Chapter 8: Typed Arithmetic Expressions (§8.1–§8.3, pp. 91–98); PLF *Types*.
- **Title:** Type Safety, Progress, and Preservation Foundations
- **Judgments of Ours:**
  - `MachineTyped root rootTy w m` ($J$) ([`Laws/Program/Typed/Assembly.lean:251`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Typed/Assembly.lean#L251)): Machine-only cut-tolerant invariant: world validity, typed stores, inert fiber code, and live scheduler.
  - `ConfigTyped root rootTy w m (cmd :: rest)` ($I$) ([`Laws/Program/Typed/Assembly.lean:263`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Typed/Assembly.lean#L263)): Configuration invariant extending $J$ with running fiber code and queued command validity (`QueueOk`).
  - `StepPreserves root rootTy cmd` ([`Laws/Program/Typed/Assembly.lean:444`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Typed/Assembly.lean#L444)): One-step preservation predicate for command execution under $I$.
  - `MachineLive m` ([`Laws/Program/Typed/Assembly.lean:239`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Typed/Assembly.lean#L239)): Halting-freedom predicate: $m.\text{stuck} = \text{none}$, ambient scopes live, scheduled owed resumes owned.
- **Theorems:**
  - `machineTyped_not_halted`: **proved** ([`Laws/Program/Typed/Assembly.lean:310`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Typed/Assembly.lean#L310)): Every typed machine state is non-halting ($m.\text{stuck} = \text{none}$).
  - `machineTyped_of_configTyped`: **proved** ([`Laws/Program/Typed/Assembly.lean:271`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Typed/Assembly.lean#L271)): Configuration invariant $I$ projects directly to machine invariant $J$.
  - `evaluate_entry`: **proved** ([`Laws/Program/Typed/Assembly.lean:413`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Typed/Assembly.lean#L413)): Initial entry premise for evaluation loops.
  - `stepKeeps_of_stepPreserves`: **proved** ([`Laws/Program/Typed/Assembly.lean:452`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Typed/Assembly.lean#L452)): Connecting command preservation to the generic lift `StepKeeps`.
  - `m7_of_ledger`: **proved** ([`Laws/Program/Typed/Assembly.lean:1580`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Typed/Assembly.lean#L1580)): Capstone route theorem: `LoadsTyped` (M5) and `DecisionKeeps` (M6) imply M7a–c.
  - Proved command preservations in `M6Ledger`: `step_trackChild`, `step_drainDue`, `step_link`, `step_evaluate`, `step_resume`, `step_observe`, `step_interruptTarget`, `step_raceCancel`, `step_enrollRace`, `step_afterInterrupt`, `step_closeParAwait` (11 proved, [`Laws/Program/Typed/Commands/*.lean`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Typed/Commands/Observe.lean#L1353)).
  - Open command preservations in `M6Ledger`: `step_loop`, `step_deliver`, `step_finish`, `step_launch`, `step_registrationDone`, `step_exitDone`, `step_wake`, `decision_preserves`, `typedState_reachable` (9 open, [`Assembly.lean:1843-1851`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Typed/Assembly.lean#L1843-L1851)).
- **Ledger Scopes:** `M6Ledger` ([`Commands/Observe.lean:1356`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Typed/Commands/Observe.lean#L1356), 9 open, 11 proved), `M6Edits` ([`Edits.lean:487`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Typed/Edits.lean#L487), 1 open, 12 proved), `M7` ([`Assembly.lean:1858`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Typed/Assembly.lean#L1858), 4 open).
- **Decisions Rows:** Rows 106, 107 (fresh tokens, exit clause), Rows 133, 134 (the $J$/$I$ split keyed on `running`; five clauses (a)–(e)), Row 138 (M7 declared), Row 139 (halting freedom in typed state), Row 180 (registered handle bytes), Row 181 (field census).
- **Modules Covered:** `Laws/Program/Typed/Assembly.lean`, `Laws/Program/Typed/Commands/*.lean`, `Laws/Program/Typed/Edits.lean`.
- **The Language Cut:**
  In TAPL Chapter 8, Type Safety is stated on closed terms as Progress ($t \text{ val} \lor \exists t', t \to t'$) and Preservation ($t : T \land t \to t' \implies t' : T$). In Effect4, progress is formulated as non-halting ($m.\text{stuck} = \text{none}$) and frontier preservation under explicit scheduler decisions (`machineTyped_not_halted`), while preservation is factored through the $J$/$I$ split and generic transition lifts (`FoldLift` / `DecisionLift`).

---

### Chapter 3: `tapl-09-stlc-cut`
- **Book Citation:** TAPL Chapter 9: Simply Typed Lambda-Calculus (§9.1–§9.4, pp. 99–112); PLF *Stlc*.
- **Title:** Pure Program Typing, Inversion, and Decision Procedures
- **Judgments of Ours:**
  - `HasTy (sig : Signature Op) (env : TyEnv) (e : Eff Op) (t : EffTy) : Prop` ([`Laws/Program/Typing/HasTy.lean:64`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Typing/HasTy.lean#L64)): Declarative inductive typing judgment.
  - `check (sig : Signature Op) (env : TyEnv) (path : List Nat) (e : Eff Op) : Except Refusal EffTy` ([`Program/Checker.lean:24`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Program/Checker.lean#L24)): Algorithmic typechecker fold with located refusal reporting.
  - `wellTyped (sig : Signature Op) (p : Eff Op) : Prop` ([`Program/Checker.lean:114`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Program/Checker.lean#L114)): Existence of typing certificate.
- **Theorems:**
  - `check_sound`: **proved** ([`Laws/Program/Typing/CheckSound.lean:37`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Typing/CheckSound.lean#L37)): Algorithmic checker soundness ($\text{check } e = \text{ok } t \implies \text{HasTy } e \, t$).
  - `check_complete`: **proved** ([`Laws/Program/Typing/CheckSound.lean:361`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Typing/CheckSound.lean#L361)): Algorithmic checker completeness ($\text{HasTy } e \, t \implies \text{check } e = \text{ok } t$).
  - `hasTy_unique`: **proved** ([`Laws/Program/Typing/Sound.lean:130`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Typing/Sound.lean#L130)): Declarative typing uniqueness ($\text{HasTy } e \, t_1 \land \text{HasTy } e \, t_2 \implies t_1 = t_2$).
  - `hasTy_weaken`: **proved** ([`Laws/Program/Typing/Sound.lean:156`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Typing/Sound.lean#L156)): Weakening under context extension.
  - Inversion lemmas: `inv_succeed`, `inv_fail`, `inv_bind`, `inv_perform`, `inv_sync`, `inv_suspend`: **proved** ([`Laws/Program/Typing/Inversion.lean:21-52`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Typing/Inversion.lean#L21-L52)).
  - `effTy_eq_hasTy`: **proved** ([`Laws/Program/Typing/Sound.lean:114`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Typing/Sound.lean#L114)).
  - `wellTyped_iff`: **proved** ([`Laws/Program/Typing/Sound.lean:120`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Typing/Sound.lean#L120)): $\text{explain } p = \text{none} \iff \text{wellTyped } p$.
- **Ledger Scopes:** Core proof graph in `Laws/Program/Typing/` (audited by `AxiomGate.lean` at `[propext, Quot.sound]`).
- **Decisions Rows:** Row 104 (`E4-PROV-CE-005` repaired: layer body environment scoping), Row 105 (`E4-PROV-CE-006` repaired: layer value fits static key type), Row 163 (the function-value cut), DB-08 (`Expr` is metaprogramming only).
- **Modules Covered:** `Program/Typing/Rules.lean`, `Program/Checker.lean`, `Laws/Program/Typing/{HasTy,CheckSound,CheckInversion,Inversion,Sound}.lean`.
- **The Language Cut:**
  TAPL Chapter 9 centers on arrow types ($T_1 \to T_2$), functional abstraction ($\lambda x : T_1. t$), application ($t_1 \, t_2$), and the substitution lemma ($[x \mapsto s]t$). Effect4 performs a complete, deliberate cut of function values (row 163, `language-cut.md` §1): no $\lambda$, no higher-order closures stored in values or syntax. Variables are de Bruijn positions indexing an immutable input environment `TyEnv`. Composition is monadic `bind` appending answers to the environment, not higher-order function application. Substitution is replaced by positional indexing and environment weakening (`hasTy_weaken`).

---

### Chapter 4: `tapl-11-extensions`
- **Book Citation:** TAPL Chapter 11: Simple Extensions (§11.1 Base types, §11.2 Sequencing, §11.5 Pairs/Tuples, §11.6 Records, §11.7 Sums/Variants, §11.11 General Recursion, §11.12 Lists, pp. 117–152); PLF *MoreStlc*.
- **Title:** Structural Extensions: Products, Records, Variants, Lists, and Iteration
- **Judgments of Ours:**
  - `Ty.prod`, `Ty.record`, `Ty.union`, `Ty.list`, `Ty.option`, `Ty.unit`, `Ty.boolean`, `Ty.string`, `Ty.nat`, `Ty.int` ([`Program/Ty.lean:37-65`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Program/Ty.lean#L37-L65)): Inductive type constructors.
  - `Term.record`, `Term.field` ([`Machine/Term.lean`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Machine/Term.lean), row 166): First-order record term constructors.
  - `Eff.iterate` ([`Program/Eff.lean:559`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Program/Eff.lean#L559)): Bounded tail-recursive loop construct.
- **Theorems:**
  - `sub_prod_mono`: **proved** ([`Laws/Program/TypeAlgebra.lean:845`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/TypeAlgebra.lean#L845)): Product subtyping covariance.
  - `inv_iterate`: **proved** ([`Laws/Program/Typing/Inversion.lean:111`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Typing/Inversion.lean#L111)): Typing inversion for iteration.
  - `conv_fixpoint`, `conv_least`, `conv_unique`: **proved** ([`Laws/Program/IterLimit.lean`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/IterLimit.lean)): Kleene limit fixed-point laws for iteration.
  - `denoteB_mono`: **proved** ([`Laws/Program/DenoteB.lean:208`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/DenoteB.lean#L208)): Monotonicity of budget approximants.
  - `namedHasTy`, `record_width_refused`, `fits_project`: **proved on copy** ([`type-language-probe/P/probes/P2Ty.lean`](file:///Users/pooks/Dev/lean4-effect4/docs/research/2026-10-01-type-language-probe/P/probes/P2Ty.lean)): Canonical record membership and width projection.
  - `inhabited_iff_fits`: **proved** ([`Laws/Program/Typed/Membership.lean:2240`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Typed/Membership.lean#L2240)): Semantic inhabitance agreement.
- **Ledger Scopes:** `M3aAdmissionObligations`, `Test.IndexedColumnActual`.
- **Decisions Rows:** Row 119 (records with canonical field names), Row 121 (`int` inhabited and binary64 `number` nesting), Row 125 (keyed collections/maps), Row 126 (equality at records refused), Row 127 (`E4-TYPED-CE-015`: inhabitance check at admission for `prod never nat`), Row 130 (`catchTag` residual, discriminant `_tag`), Row 157 (optional keys `a?: A`), Row 159 (tuples of arbitrary arity), Row 160 (`null` and `undefined` leaves), Row 165 (record values carry canonical names in existing frames), Row 166 (record term constructors `Term.record`, `Term.field`).
- **Modules Covered:** `Program/Ty.lean`, `Program/Eff.lean`, `Machine/Term.lean`, `Store/Val.lean`, `Laws/Program/TypeAlgebra.lean`, `Laws/Program/Iter.lean`, `Laws/Program/IterLimit.lean`.
- **The Language Cut:**
  TAPL Chapter 11 uses general non-terminating recursion via $\text{fix}$ or letrec. Effect4 isolates non-termination strictly in the monadic `Eff.iterate` construct, whose denotation is the Kleene limit of budget approximants (`denoteB`), verified via Elgot iteration algebras. Records are strictly first-order with field names canonically sorted; projection is untyped and field-name directed (row 165).

---

### Chapter 5: `tapl-13-references`
- **Book Citation:** TAPL Chapter 13: References (§13.1–§13.5, pp. 153–178); PLF *References*.
- **Title:** First-Order Mutable References and Kripke Store Typings
- **Judgments of Ours:**
  - `World` ([`Laws/Program/Typed/World.lean:52`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Typed/World.lean#L52)): Kripke store typing holding ghost tables $\Gamma, \Pi, \mathrm{P}, \Theta$.
  - `World.le` ([`Laws/Program/Typed/World.lean:137`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Typed/World.lean#L137)): Preorder of store typing extension.
  - `WorldValid` ([`Laws/Program/Typed/Validity.lean:19`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Typed/Validity.lean#L19)): Invariant that physical machine stores conform to store typing.
  - `RefDeclared w cell ty` ([`Laws/Program/Typed/World.lean:71`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Typed/World.lean#L71)): Location typing in world.
  - `ScopeLive w sc` ([`Laws/Program/Typed/World.lean:149`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Typed/World.lean#L149)): Persistent scope presence predicate.
  - `StoreTyped root w m` ([`Laws/Program/Typed/Adequacy.lean:39`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Typed/Adequacy.lean#L39)): Machine store typing conformance.
- **Theorems:**
  - `order_refl`, `order_trans`: **proved** ([`Laws/Program/Typed/World.lean:411-415`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Typed/World.lean#L411-L415)): Reflexivity and transitivity of store typing extension.
  - `fits_mono`: **proved** ([`Laws/Program/Typed/Membership.lean:856`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Typed/Membership.lean#L856)): Monotonicity of value interpretation along store extension ($w \le w' \implies \text{Fits } w \, v \, \tau \implies \text{Fits } w' \, v \, \tau$).
  - `scopeLive_mono`: **proved** ([`Laws/Program/Typed/World.lean:432`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Typed/World.lean#L432)): Persistence of allocated scopes under store growth.
  - `valid_refMake_fresh`: **proved** ([`Laws/Program/Typed/Validity.lean:224`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Typed/Validity.lean#L224)): Store validity preserved under fresh cell allocation.
  - `initial_world_valid`: **proved** ([`Laws/Program/Typed/Validity.lean:218`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Typed/Validity.lean#L218)): Initial loaded world is valid.
  - `storeStep_typed`: **proved** ([`Laws/Program/Typed/Adequacy.lean:59`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Typed/Adequacy.lean#L59)): General store handler adequacy theorem.
  - Specific store adequacy theorems: `refUpdate_implements`, `refGetAndUpdate_implements`, `refUpdateAndGet_implements`, `refUpdateSome_implements`, `refGetAndUpdateSome_implements`, `refUpdateSomeAndGet_implements`: **proved** ([`Laws/Program/Typed/Adequacy.lean:1705-1716`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Typed/Adequacy.lean#L1705-L1716)).
  - `M7.stores_typed`: **open** ([`Laws/Program/Typed/Assembly.lean:1778`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Typed/Assembly.lean#L1778)): Replay stores fit declared store typing.
- **Ledger Scopes:** `M2Validity` ([`Validity.lean:240`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Typed/Validity.lean#L240), ceiling 0), `M3bWorld` ([`Assembly.lean:1872`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Typed/Assembly.lean#L1872), ceiling 0), `M3bAdequacy` ([`Adequacy.lean:1724`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Typed/Adequacy.lean#L1724), ceiling 2).
- **Decisions Rows:** Rows 44, 45 (world types cells at any type, ghost store typings), Row 96 (`Fits` replaces `StrongValue`), Row 136 (protocol fulfillment by store handlers; 66 of 74 proved), Row 156 (`ScopeLive` presence predicate), DB-07 (observable state on failure), DB-16 (typing as protocol per operation over world).
- **Modules Covered:** `Laws/Program/Typed/World.lean`, `Laws/Program/Typed/Validity.lean`, `Laws/Program/Typed/Adequacy.lean`, `Machine/Stores.lean`.
- **The Language Cut:**
  TAPL Chapter 13 defines locations $l \in \mathrm{Loc}$ as first-class terms and store typings $\Sigma$ mapping locations to arbitrary types, including closures (which requires cyclic/step-indexed store typings). Effect4 references (`Ref`, `Deferred`, `Scope`, `Fiber`) are first-order handles (indices $\mathbb{N}$). Worlds $W = \langle \text{ids}, \text{state}, \Gamma, \Pi, \mathrm{P}, \Theta \rangle$ store purely first-order syntactic types (`Ty`). Hence no step-indexing is required: the store typing extension $\le$ is well-founded and exact.

---

### Chapter 6: `tapl-14-exceptions`
- **Book Citation:** TAPL Chapter 14: Exceptions (§14.1–§14.3, pp. 179–186).
- **Title:** Typed Failures, Cause Algebras, and Defect Soundness
- **Judgments of Ours:**
  - `ExitOk w ty ex` ([`Laws/Program/Typed/Admission.lean:31`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Typed/Admission.lean#L31)): $\text{FitsExit } w \, ty \, ex \land \text{NoShapeDefect } ty \, ex$.
  - `NoShapeDefect ty ex` ([`Laws/Program/Typed/Admission.lean:24`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Typed/Admission.lean#L24)): Excludes bad dispatch defects (`badName`, `notImplemented`) from typed exits.
  - `ShapeFree c` ([`Laws/Program/Typed/Membership.lean:135`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Typed/Membership.lean#L135)): Excludes shape defects from cause trees.
  - Inversion judgments: `inv_fail`, `inv_failCause`, `inv_catchCause`, `inv_matchCause`, `inv_onExit` ([`Laws/Program/Typing/Inversion.lean:26-91`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Typing/Inversion.lean#L26-L91)).
  - `exitHasTy_of_fitsExit` ([`Laws/Program/Typed/ExitConnector.lean:65`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Typed/ExitConnector.lean#L65)): Soundness bridge from machine exits to denotational exits.
- **Theorems:**
  - `fitsExit_mono`: **proved** ([`Laws/Program/Typed/Validity.lean:237`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Typed/Validity.lean#L237)): Monotonicity of exit membership along world order.
  - `noShapeDefect_failure_iff`: **proved** ([`Laws/Program/Typed/Membership.lean:150`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Typed/Membership.lean#L150)): Characterization of shape defect freedom on failures.
  - `M7.exits_typed`: **open** ([`Laws/Program/Typed/Assembly.lean:1774`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Typed/Assembly.lean#L1774)): Recorded exits fit fiber types.
- **Ledger Scopes:** `M7`, `M3bAssembly`.
- **Decisions Rows:** Row 107 (exit clause "never goes wrong": `ExitOk`), Row 117 (H2 part two: presence coeffects for `missingService`), Row 120 (error payloads without handles), Row 151 (lone finalizer voiding at public close), Row 152 (`Fits` at `exitOf a e` reads `ShapeFree`, repairing `E4-TYPED-CE-017`), DB-07 (runtime state observable on failure).
- **Modules Covered:** `Laws/Program/Typed/Admission.lean`, `Laws/Program/Typed/Membership.lean`, `Laws/Program/Typed/ExitConnector.lean`, `Machine/Exit.lean`, `Machine/Cause.lean`.
- **The Language Cut:**
  TAPL Chapter 14 models simple exceptions (`error` or `raise t`) that abort evaluation. Effect4 reifies Effect rc.112's algebraic cause structure: structured exits (`Exit.Success`, `Exit.Failure`), composite cause trees (`Cause.Fail`, `Cause.Die`, `Cause.Interrupt`, `Cause.Parallel`, `Cause.Sequential`), cleanly separating typed domain failures (`Fail e`) from untyped machine defects (`Die d`). The exit judgment `ExitOk` guarantees typed failures conform to the error type while verifying that defects never arise from ill-typed runtime dispatch (`NoShapeDefect`).

---

### Chapter 7: `tapl-15-subtyping`
- **Book Citation:** TAPL Chapter 15: Subtyping (§15.1 Subsumption, §15.2 Subtyping rules, §15.3 Top and Bottom, §15.4 Structural Subtyping, pp. 187–208).
- **Title:** Algorithmic Subtyping, Bounded Join-Semilattices, and Variance
- **Judgments of Ours:**
  - `Ty.sub : Ty -> Ty -> Bool` ([`Program/Ty.lean:352`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Program/Ty.lean#L352)): Computable boolean subtyping decision procedure.
  - `Ty.subN : Ty -> Ty -> Bool` ([`Program/Ty.lean:835`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Program/Ty.lean#L835)): Subtyping on normalized types (`Ty.sub a.normalize b.normalize`).
  - `Ty.isMember : Ty -> Bool` ([`Program/Ty.lean:242`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Program/Ty.lean#L242)): Normal form member classifier.
- **Theorems:**
  - `sub_never`: **proved** ([`Laws/Program/TypeAlgebra.lean:496`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/TypeAlgebra.lean#L496)): $\bot = \text{never}$ is minimal: $\forall t, \text{sub } \text{never } t = \text{true}$.
  - `sub_unknown`: **proved** ([`Laws/Program/TypeAlgebra.lean:502`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/TypeAlgebra.lean#L502)): $\top = \text{unknown}$ is maximal: $\forall t, \text{sub } t \, \text{unknown} = \text{true}$.
  - `sub_join_left`, `sub_join_right`: **proved** ([`Laws/Program/TypeAlgebra.lean:734-742`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/TypeAlgebra.lean#L734-L742)): $\text{join}$ is an upper bound.
  - `sub_sound`: **proved** ([`Laws/Program/Template.lean:312`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Template.lean#L312)): Soundness against value membership ($\text{sub } a \, b \implies \text{hasTy } v \, a \implies \text{hasTy } v \, b$).
  - `sub_not_complete`: **proved** ([`Laws/Program/Template.lean:322`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Template.lean#L322)): Semantic value inclusion does not imply syntactic subtyping (counterexample: `Option<nat | string>` vs `Option<nat> | Option<string>`).
  - `fits_sub`: **proved** ([`Laws/Program/Typed/Membership.lean:894`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Typed/Membership.lean#L894)): Semantic membership closed under `sub`.
  - `fits_subN`: **proved** ([`Laws/Program/Typed/Membership.lean:1232`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Typed/Membership.lean#L1232)): Semantic membership closed under `subN`.
- **Ledger Scopes:** Core Laws in `TypeAlgebra.lean`.
- **Decisions Rows:** Row 137 (`Fits` compares declarations in `subN`, repairing `E4-TYPED-CE-009`), Row 177 (leaf-order table: acyclicity, declared edges), Row 178 (required below optional at records), DB-15 (structural subtyping on records).
- **Modules Covered:** `Program/Ty.lean`, `Laws/Program/TypeAlgebra.lean`, `Laws/Program/Typed/Membership.lean`.
- **The Language Cut:**
  TAPL Chapter 15 includes the standard subsumption rule in the declarative judgment ($\Gamma \vdash t : S \land S <: T \implies \Gamma \vdash t : T$). Effect4's declarative judgment `HasTy` has no subsumption rule; subsumption is pushed into specific syntax nodes (`bind`, `perform`, `provideLayer`), while `check` uses algorithmic `subN` on normalized types. Records use exact subtyping (width subtyping is refused at program level and projected only at the foreign boundary, row 119).

---

### Chapter 8: `tapl-16-metatheory-subtyping`
- **Book Citation:** TAPL Chapter 16: Metatheory of Subtyping (§16.1 Algorithmic Subtyping, §16.2 Completeness and Decidability, §16.3 Joins and Meets, pp. 209–224).
- **Title:** Metatheory of Algorithmic Subtyping and Normal-Form Algebras
- **Judgments of Ours:**
  - `CTy` ([`Program/Ty.lean:842`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Program/Ty.lean#L842)): Canonical normalized types ($CTy = \{ t : Ty \mid t.\text{normalize} = t \}$).
  - `CTy.join` ([`Program/Ty.lean:848`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Program/Ty.lean#L848)): Computable least upper bound operator.
  - `Ty.normalize` ([`Program/Ty.lean:820`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Program/Ty.lean#L820)): Normalization function into canonical form.
- **Theorems:**
  - `sub_trans`: **proved** ([`Laws/Program/TypeAlgebra.lean:117`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/TypeAlgebra.lean#L117)): Transitivity of algorithmic subtyping ($\text{sub } a \, b \land \text{sub } b \, c \implies \text{sub } a \, c$).
  - `sub_antisymm_normal`: **proved** ([`Laws/Program/TypeAlgebra.lean:618`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/TypeAlgebra.lean#L618)): Antisymmetry on normalized types ($\text{sub } a \, b \land \text{sub } b \, a \implies a = b$).
  - `sub_antisymm_canonical`: **proved** ([`Laws/Program/TypeAlgebra.lean:705`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/TypeAlgebra.lean#L705)): Antisymmetry on `CTy`.
  - `subN_equiv_iff`: **proved** ([`Laws/Program/TypeAlgebra.lean:1088`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/TypeAlgebra.lean#L1088)): Kernel of checker's order is syntactic equality of normal forms ($Ty/\equiv_N \cong CTy$).
  - `instIsPartialOrder` on `CTy`: **proved** ([`Laws/Program/TypeAlgebra.lean:1271`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/TypeAlgebra.lean#L1271)): Partial order instance.
  - `instLawfulOrderSup` on `CTy`: **proved** ([`Laws/Program/TypeAlgebra.lean:1288`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/TypeAlgebra.lean#L1288)): Lawful join-semilattice instance.
  - `normalize_idem`: **proved** ([`Program/Ty.lean:829`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Program/Ty.lean#L829)): Idempotence of normalization.
- **Ledger Scopes:** Core Laws in `TypeAlgebra.lean`.
- **Decisions Rows:** Row 137 (`subN` as checker's order), Row 177 (transitivity and antisymmetry proved from leaf-order table acyclicity).
- **Modules Covered:** `Program/Ty.lean`, `Laws/Program/TypeAlgebra.lean`.
- **The Language Cut:**
  TAPL Chapter 16 develops algorithmic subtyping deductively and proves transitivity/reflexivity elimination. Effect4 formalizes `sub` as a terminating boolean function (`Ty -> Ty -> Bool`), proving reflexivity, transitivity, and antisymmetry directly. Furthermore, meets ($\sqcap$) are explicitly not claimed: `CTy` is a bounded join-semilattice, not a lattice.

---

### Chapter 9: `tapl-19-nominal`
- **Book Citation:** TAPL Chapter 19: Case Study: Featherweight Java / Nominal Types (§19.1–§19.4, pp. 245–259).
- **Title:** Nominal Handle Types, Applied References, and Class Identity
- **Judgments of Ours:**
  - `Ty.handle (name : String)` ([`Program/Ty.lean:45`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Program/Ty.lean#L45)): Opaque nominal handle type.
  - `Ty.app (name : String) (args : List Ty)` ([`Program/Ty.lean`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Program/Ty.lean), proposed row 158): Structured nominal type reference.
  - `HandleFits w v ty` ([`Laws/Program/Typed/Membership.lean:62`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Typed/Membership.lean#L62)): Validity of nominal capability handles against store declarations.
  - `ExitHandlesValid root rootTy fuel m` ([`Laws/Program/Typed/Assembly.lean:1787`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Typed/Assembly.lean#L1787)): Invariant that recorded exit values carry only live allocated handles.
- **Theorems:**
  - `sub_handle`: **proved** ([`Program/Ty.lean:357`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Program/Ty.lean#L357)): Nominal subtyping on handles is strict name equality.
  - `handles_minted`: **proved** ([`Laws/Machine/Handles.lean:1042`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Machine/Handles.lean#L1042)): Capability handles originate exclusively from allocator instructions.
  - `exitHandles_valid_of_registered`: **proved** ([`Laws/Program/Typed/Assembly.lean:1515`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Typed/Assembly.lean#L1515)): Proving exit handle validity up to registered bytes (row 180).
  - `M7.exitHandles_valid`: **open** ([`Laws/Program/Typed/Assembly.lean:1857`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Typed/Assembly.lean#L1857)): Exit handle validity ledger goal.
- **Ledger Scopes:** `M7`.
- **Decisions Rows:** Row 97 (interim handle rule: no internal handles in host replies), Row 158 (`Ty.app` nominal references to Effect module types), Row 180 (registered handle bytes for exit validity).
- **Modules Covered:** `Program/Ty.lean`, `Laws/Machine/Handles.lean`, `Laws/Program/Typed/Membership.lean`.
- **The Language Cut:**
  TAPL Chapter 19 formalizes object-oriented classes with method suites and nominal subtyping hierarchies. Effect4 models nominal types as pure first-order data tags (`handle`, `app`) indexing runtime capabilities (`FiberId`, `CellId`, `ScopeId`) or external nominal types (`Queue.Dequeue<Job>`, `Data.TaggedError`). Subtyping on handles is nominal equality; on `app` it is governed by a static variance table per name (`variancesOf`, row 158).

---

### Chapter 10: `tapl-20-recursive`
- **Book Citation:** TAPL Chapter 20: Recursive Types (§20.1 Examples, §20.2 Formalities, pp. 261–280).
- **Title:** Recursive Types, Inhabitance, and Emptiness Tests
- **Judgments of Ours:**
  - `Ty.inhabited : Ty -> Bool` ([`Program/Admission.lean:79`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Program/Admission.lean#L79)): Decidable emptiness/inhabitance fold over regular tree types.
  - `AdmittedProgram.columnsTable` ([`Program/Admission.lean:145`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Program/Admission.lean#L145)): Inhabitance gate on program columns.
- **Theorems:**
  - `inhabited_of_fits`: **proved** ([`Laws/Program/Typed/Membership.lean:2188`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Typed/Membership.lean#L2188)): Semantic value membership implies inhabitance.
  - `inhabited_of_hasTy`: **proved** ([`Laws/Program/Typed/Membership.lean:2224`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Typed/Membership.lean#L2224)): Pure value typing implies inhabitance.
  - `inhabited_iff_fits`: **proved** ([`Laws/Program/Typed/Membership.lean:2240`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Typed/Membership.lean#L2240)): Full equivalence between `inhabited` and semantic inhabitance.
- **Ledger Scopes:** `M3aAdmissionObligations`.
- **Decisions Rows:** Row 124 (recursive types open, via nominal $\Sigma_{\text{app}}$ declarations through `Ty.app`, row 158), Row 127 (DI-67 admission gap repaired: `emptyColumn` refuses uninhabited types), Row 149 (refusal naming: `uninhabited` for `int`, `emptyColumn` for emptiness).
- **Modules Covered:** `Program/Admission.lean`, `Laws/Program/Typed/Membership.lean`.
- **The Language Cut:**
  TAPL Chapter 20 treats recursive types via equi-recursive or iso-recursive $\mu X. T$ terms. Effect4 explicitly rejects adding a recursive type constructor $\mu X. T$ to `Ty` (row 124): recursion enters strictly through nominal $\Sigma_{\text{app}}$ declarations via `Ty.app` (row 158). The sole recursive metatheorem in-tree is regular-tree inhabitance (`inhabited`), guaranteeing that no admitted program or host-row request/response column is uninhabited (`never`).

---

### Chapter 11: `tapl-22-reconstruction`
- **Book Citation:** TAPL Chapter 22: Type Reconstruction (§22.1–§22.8, pp. 317–338); Pottier and Rémy (2005).
- **Title:** Type Inference, Constraint Solving, and Template Matching
- **Judgments of Ours:**
  - `Ty.infer (σ : Subst) (template request : Ty) (join : Bool) : Subst` ([`Program/Ty.lean:508`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Program/Ty.lean#L508)): Pattern-matching inference procedure.
  - `matchTemplate (σ : Subst) (template request : Ty) (join : Bool) : Option Subst` ([`Program/Ty.lean:530`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Program/Ty.lean#L530)): Guarded template matcher.
  - `matchTemplateArgs (σ : Subst) (params requests : List Ty) (join : Bool) : Option Subst` ([`Program/Ty.lean:538`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Program/Ty.lean#L538)): Argument list matcher.
  - `Widens (σ σ' : Subst) : Prop` ([`Laws/Program/Template.lean:75`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Template.lean#L75)): Substitution widening relation.
- **Theorems:**
  - `matchTemplate_sound`: **proved** ([`Laws/Program/Template.lean:58`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Template.lean#L58)): Soundness of template matching ($\text{matchTemplate } \sigma \, t \, r = \text{some } \sigma' \implies \text{sub } r (\text{instantiate } \sigma' \, t) = \text{true}$).
  - `infer_widens`: **proved** ([`Laws/Program/Template.lean:143`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Template.lean#L143)): `infer` extends the substitution.
  - `infer_closed`: **proved** ([`Laws/Program/Template.lean:53`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Template.lean#L53)): Closed templates produce no bindings.
  - `instantiate_closed`: **proved** ([`Laws/Program/Template.lean:50`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Template.lean#L50)): Instantiating closed types is the identity.
- **Ledger Scopes:** Core Laws in `Template.lean`.
- **Decisions Rows:** Rows 42, 43 (parameterized native rows), Row 155 (template parameters in row columns), Row 183 (host adequacy at template row: `bitEntry` reads template vs instance).
- **Modules Covered:** `Program/Ty.lean`, `Laws/Program/Template.lean`.
- **The Language Cut:**
  TAPL Chapter 22 presents algorithm W / Hindley-Milner unification generating full constraint sets over first-class function types. Effect4 uses one-way first-order template pattern matching (`matchTemplate`), matching concrete request types against row templates without constraint unification. The `join` parameter controls whether multiple occurrences take the least upper bound or preserve the first binding (mirroring TypeScript's `NoInfer`).

---

### Chapter 12: `tapl-23-prenex`
- **Book Citation:** TAPL Chapter 23: Universal Polymorphism (§23.1–§23.4 System F, pp. 339–358).
- **Title:** Prenex Polymorphic Templates and First-Order Instantiation
- **Judgments of Ours:**
  - `Ty.var (i : Nat)` ([`Program/Ty.lean:39`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Program/Ty.lean#L39)): de Bruijn parameter variable.
  - `instantiate (σ : Subst) (t : Ty) : Ty` ([`Program/Ty.lean:475`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Program/Ty.lean#L475)): Parallel substitution application.
  - `Row.instantiate (σ : Subst) (r : Row) : Row` ([`Program/Native.lean:65`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Program/Native.lean#L65)): Operation row template instantiation.
- **Theorems:**
  - `NativeOp.row_closed`: **proved** ([`Laws/Program/Template.lean:220`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Template.lean#L220)): All built-in native operations are closed (parameter-free).
  - `templateAdmissible_of_closed`: **proved** ([`Laws/Program/Template.lean:276`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Template.lean#L276)): Closed types are admissible templates.
  - `rowTy_closed`: **proved** ([`Laws/Program/Template.lean:200`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Template.lean#L200)): Instantiated row types are closed.
- **Ledger Scopes:** Core Laws in `Template.lean`.
- **Decisions Rows:** Rows 42, 43 (templated rows), Row 163 (prenex templates only, no polymorphic functions $\forall X. T$).
- **Modules Covered:** `Program/Ty.lean`, `Program/Native.lean`, `Laws/Program/Template.lean`.
- **The Language Cut:**
  TAPL Chapter 23 defines System F with first-class type abstractions ($\Lambda X. t$), type applications ($t [T]$), and impredicative universal types ($\forall X. T$). Effect4 cuts System F completely: polymorphism is strictly prenex and first-order. Type variables `Ty.var` exist only within operation row signatures (`Row`); there are no type abstraction terms $\Lambda X. t$ in `Eff` and no universal quantifiers $\forall X. T$ in `Ty`.

---

### Chapter 13: `attapl-03-effects`
- **Book Citation:** ATTAPL Chapter 3: Effect Systems and Subeffecting (§3.1–§3.5, pp. 87–130); Plotkin & Pretnar, Bauer & Pretnar, Leijen (Koka).
- **Title:** Effect Signatures, Requirement Rows, and Coeffect Grading
- **Judgments of Ours:**
  - `Row` ([`Program/Native.lean:38`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Program/Native.lean#L38)): Operation row signature `⟨id, name, request, answer, error, kind⟩`.
  - `RowTable` ([`Program/Native.lean:82`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Program/Native.lean#L82)): Application effect signature table $\Sigma_{\text{app}}$.
  - `keysRow (r : List Key) : RowSet` ([`Program/Provision.lean:45`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Program/Provision.lean#L45)): Canonical set of required service keys.
  - `satisfies (ctx : Context) (req : RowSet) : Bool` ([`Program/Provision.lean:193`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Program/Provision.lean#L193)): Context satisfaction predicate.
  - `EffTy.requires` ([`Program/Ty.lean:68`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Program/Ty.lean#L68)): Flat coeffect row grading on program types.
- **Theorems:**
  - `merge_rows_comm`: **proved** ([`Laws/Program/Provision.lean:105`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Provision.lean#L105)): Commutativity of requirement row union.
  - `provide_closed`: **proved** ([`Laws/Program/Provision.lean:120`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Provision.lean#L120)): Layer provision closes service dependencies.
  - `provide_provide_rows`: **proved** ([`Laws/Program/Provision.lean:150`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Provision.lean#L150)): Reassociation of layer provision chains.
  - `satisfies_iff_subset_keysRow`: **proved** ([`Program/Provision.lean:193`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Program/Provision.lean#L193)): Context satisfaction is set inclusion.
- **Ledger Scopes:** `D12` ([`Laws/Program/Typed/ProtocolObligations.lean:66`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Typed/ProtocolObligations.lean#L66), ceiling 0).
- **Decisions Rows:** Row 111 (conservative extension obligations C1–C8), Row 115 (row table growth contract), Row 116 (domain bit for host rows), Row 117 (coeffect presence contract for requirement-sensitive exits), DB-17 (services and layers as one requirement row calculus).
- **Modules Covered:** `Program/Native.lean`, `Program/Provision.lean`, `Laws/Program/Provision.lean`, `Laws/Program/Signature.lean`.
- **The Language Cut:**
  ATTAPL Chapter 3 studies effect systems tracking computational side-effects (read, write, alloc) with subeffecting. Effect4 tracks two dual structures:
  (1) Algebraic effect operations via `RowTable` / `Signature Op`, where operations are handled by the runtime engine or host session;
  (2) Flat coeffects via `EffTy.requires` (a requirement row of ambient service keys). In Effect4, provision is substitution ($R_{\text{in}} = (R_{\text{body}} \setminus R_{\text{out}}) \cup R_{\text{layer}}$), forming a free bounded join-semilattice with relative complement.

---

### Chapter 14: `attapl-08-logical-relations`
- **Book Citation:** ATTAPL Chapter 8: Logical Relations and Kripke Models (Ahmed; Ahmed, Dreyer, Rossberg 2009; Birkedal et al. Iris).
- **Title:** Kripke Logical Relations, World-Indexed Values, and Protocol Invariants
- **Judgments of Ours:**
  - `Fits w v ty` ([`Laws/Program/Typed/Membership.lean:98`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Typed/Membership.lean#L98)): World-indexed semantic value interpretation $V\llbracket\tau\rrbracket(W)$.
  - `TypedProg root w ty p` ([`Laws/Program/Typed/Residual.lean:248`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Typed/Residual.lean#L248)): Protocol weakest-precondition on free-monad interaction programs.
  - `FrameAccepts root w final f k` ([`Laws/Program/Typed/Contracts.lean:43`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Typed/Contracts.lean#L43)): Stack frame typing invariant.
  - `SavedOk typed exitOk hooks w final saved` ([`Laws/Program/Typed/Contracts.lean:82`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Typed/Contracts.lean#L82)): Typing of saved defunctionalized call stacks.
  - `DenotesTyped root` ([`Laws/Program/Typed/Assembly.lean:1075`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Typed/Assembly.lean#L1075)): Fundamental property: checked nodes denote protocol-typed programs.
- **Theorems:**
  - `fits_mono`: **proved** ([`Laws/Program/Typed/Membership.lean:856`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Typed/Membership.lean#L856)): Monotonicity of $V\llbracket\tau\rrbracket$ along world extension.
  - `typedProg_mono`: **proved** ([`Laws/Program/Typed/Residual.lean:686`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Typed/Residual.lean#L686)): Monotonicity of `TypedProg` along world extension.
  - `stackAccepts_mono`, `savedOk_mono`: **proved** ([`Laws/Program/Typed/Contracts.lean:131-139`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Typed/Contracts.lean#L131-L139)): Kripke closure of call stacks.
  - `popR_typed`: **proved** ([`Laws/Program/Typed/Stack.lean:142`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Typed/Stack.lean#L142)): Stack popping preserves typing.
  - `seq_typed`: **proved** ([`Laws/Program/Typed/Seq.lean:59`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Typed/Seq.lean#L59)): Sequencing compatibility lemma.
  - `denoteR_typed`: **open** ([`Laws/Program/Typed/Assembly.lean:1839`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Typed/Assembly.lean#L1839)): Denotation of checked code is `TypedProg`.
  - `typedState_load`: **open** ([`Laws/Program/Typed/Assembly.lean:1838`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Typed/Assembly.lean#L1838)): Loaded state is `MachineTyped`.
- **Ledger Scopes:** `M3bWorld` ([`Assembly.lean:1872`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Typed/Assembly.lean#L1872), ceiling 0), `M4Stack` ([`Stack.lean:479`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Typed/Stack.lean#L479), ceiling 0), `M5Hooks` ([`Stack.lean:481`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Typed/Stack.lean#L481), ceiling 0), `M3bAssembly` ([`Assembly.lean:1841`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Typed/Assembly.lean#L1841), ceiling 3).
- **Decisions Rows:** Row 96 (`Fits` definition and properties), Row 135 (saved frames and hook protocols Kripke-closed over later worlds), Row 148 (M5 denotation lemma declared by name, `seq_typed`), Row 170 (M5 reference-formation premise `layerRefsWF`), Row 175 (M5 completed-view and world service table), DB-16 (typing as protocol per operation over world).
- **Modules Covered:** `Laws/Program/Typed/Membership.lean`, `Laws/Program/Typed/Residual.lean`, `Laws/Program/Typed/Contracts.lean`, `Laws/Program/Typed/Stack.lean`, `Laws/Program/Typed/Seq.lean`.
- **The Language Cut:**
  ATTAPL Chapter 8 uses step-indexed Kripke logical relations with an arrow clause ($V\llbracket T_1 \to T_2 \rrbracket$) to interpret higher-order functions and mutable store references. Effect4 needs NO step-indexing: because functions are cut from values and syntax (row 163), `Fits` has no arrow clause. Worlds hold syntactic types `Ty`, so `Fits` is defined by direct structural induction over values and types.

---

### Chapter 15: `boundary-embeddings`
- **Book Citation:** Foster et al. (TOPLAS 2007, lenses); Rendel and Ostermann (POPL 2010, invertible syntax); Pickering, Gibbons, Wu (2017, profunctor optics / lawful prisms).
- **Title:** Exact Embeddings, Invertible Syntax Descriptions, and Lawful Prisms
- **Judgments of Ours:**
  - `Canonical α` ([`Store/Domain/Canonical.lean:33`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Store/Domain/Canonical.lean#L33)): Lawful prism into `Val` with `toVal`, `ofVal`.
  - `Bridge.schema : Ty -> Representation` and `Bridge.ofSchema : Representation -> Option Ty` ([`Schema/Bridge.lean:56, 181`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Schema/Bridge.lean#L56)): Bidirectional Schema AST bridge.
  - `decodeRaw : Json -> Option Val` and `encode : Val -> Json` ([`Schema/Codec.lean:277, 286`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Schema/Codec.lean#L277)): JSON codec.
  - `printT : Eff Op -> String` and `read : String -> Option (Eff Op)` ([`Codegen/Templates.lean`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Codegen/Templates.lean), [`Codegen/Read.lean`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Codegen/Read.lean)): Invertible syntax printer/reader pair.
- **Theorems:**
  - `ofVal_toVal`, `ofVal_exact`: **proved** ([`Store/Domain/Canonical.lean:33`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Store/Domain/Canonical.lean#L33)): Retraction and exactness of `Canonical` prisms.
  - `decode_exact`: **proved** ([`Store/Domain/Canonical.lean:82`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Store/Domain/Canonical.lean#L82)): Exactness of decoded value domain.
  - `read_print`: **proved** ([`Laws/Codegen/ReadPrint.lean:1904`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Codegen/ReadPrint.lean#L1904)): Printed programs read back identically on readable domain.
  - `read_exact`: **proved** ([`Laws/Codegen/Read.lean:887`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Codegen/Read.lean#L887)): Reading inverts printing modulo layout.
  - `decode_iff`: **proved** ([`Laws/Schema/Codec.lean`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Schema/Codec.lean)): JSON codec is exact modulo key order `normJ`.
  - `ofSchema_exact`: **proved** ([`Schema/Bridge.lean:492`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Schema/Bridge.lean#L492)): Schema reader is exact modulo annotation erasure `normS`.
  - `ofSchema_schema`: **proved** ([`Schema/Bridge.lean:412`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Schema/Bridge.lean#L412)): Retraction of Schema bridge.
- **Ledger Scopes:** `Test.Contracts`, Core Schema/Codegen Laws.
- **Decisions Rows:** Row 128 (exact embeddings: JSON codec modulo `normJ`, Schema reader modulo `normS`), Row 169 (readable Schema profile), Row 179 (`N_S` annotation policy erasing 9 keys), DB-15 (boundary decode route).
- **Modules Covered:** `Store/Domain/Canonical.lean`, `Schema/Bridge.lean`, `Schema/Codec.lean`, `Codegen/Templates.lean`, `Codegen/Read.lean`, `Laws/Codegen/ReadPrint.lean`, `Laws/Schema/Codec.lean`.
- **The Language Cut:**
  Standard TAPL does not formalize external syntax generation or serialization boundaries. Effect4 formalizes boundaries via K2 exact embeddings: a pair $\text{write} : A \to F$, $\text{read} : F \to \text{Option } A$ that is total on domain, satisfies retraction $\text{read}(\text{write } a) = \text{some } a$, and exactness $\text{read } v = \text{some } a \implies v \equiv \text{write } a$ modulo a named normaliser (`Canonical`, `normJ`, `normS`). This prevents silent data widening or corruption across language boundaries (TypeScript, JSON, Schema).

---

### Chapter 16: `initial-algebra`
- **Book Citation:** Goguen, Thatcher, Wagner, Wright (GTWW 1977); Meijer, Fokkinga, Paterson (FPCA 1991); Gibbons (2002); Hinze (2013); Johann and Ghani (2007).
- **Title:** Initial Algebras, Catamorphisms, and the Coherence Principle
- **Judgments of Ours:**
  - `cataFam (alg : EffAlgebra ...) : Eff Op -> Carrier` ([`Program/LayerView.lean:414`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Program/LayerView.lean#L414)): Unique catamorphism out of program syntax.
  - `cata_eff` ([`Program/Fold.lean:1104`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Program/Fold.lean#L1104)): Fold over program terms.
  - `cata_ty (alg : TyAlgebra R) : Ty -> R` ([`Program/Fold.lean:31`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Program/Fold.lean#L31)): Unique catamorphism out of types.
  - `cata_term (alg : TermAlgebra R) : Term -> R` ([`Machine/Term.lean`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Machine/Term.lean)): Catamorphism on pure terms.
  - `build` and `view` ([`Program/LayerView.lean:278, 609`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Program/LayerView.lean#L278)): Wadler view and Gill–Launchbury–Peyton Jones build.
- **Theorems:**
  - `hom_eq_cata_eff`: **proved** ([`Program/Fold.lean:1270`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Program/Fold.lean#L1270)): Uniqueness of algebra morphisms out of `Eff`.
  - `hom_eq_cata_ty`: **proved** ([`Program/Fold.lean:89`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Program/Fold.lean#L89)): Uniqueness of algebra morphisms out of `Ty`.
  - `cata_build`: **proved** ([`Program/LayerView.lean:481`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Program/LayerView.lean#L481)): Catamorphism commutes with constructor build.
  - `build_view`: **proved** ([`Program/LayerView.lean:620`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Program/LayerView.lean#L620)): Isomorphism between view and build representations.
- **Ledger Scopes:** Core Program and Fold definitions.
- **Decisions Rows:** Row 143 (traversal census instrument), Row 171 (generator for nested families of variable arity), Row 173 (per-constructor tables cut-over), Row 182 (every `Ty` traversal an algebra of one fold), DB-01 (`Program` as well-founded higher-order proof carrier).
- **Modules Covered:** `Program/Eff.lean`, `Program/LayerView.lean`, `Program/Ty.lean`, `Program/Fold.lean`, `Machine/Term.lean`, `Laws/Auto/Traversals.lean`.
- **The Language Cut:**
  In TAPL, inductive types are presented informal-syntactically with ad-hoc inductive definitions and structural recursions. Effect4 strictly enforces the **Coherence Principle**: each syntactic sort has exactly one free object representation (`Eff`, `Ty`, `Term`, `Store.Val`, `Representation`, `List Command`). Every traversal must be an algebra of the initial fold (`cata`), making any two traversals with agreeing algebras definitionally equal by the unique homomorphism theorem (`hom_eq_cata_eff`), with hand matches strictly audited and exempted by the `#traversal_census` gate.

---

### Chapter 17: `machine-concurrency`
- **Book Citation:** Harper (PFPL 2016, ch. 28, Abstract Machines); Wright and Felleisen (1994); de Vilhena and Pottier (2021, 2022); Milner and Sangiorgi (bisimulation); Lynch and Vaandrager (forward simulations); Honda, Wadler (session types).
- **Title:** Reactive Fiber Runtime, Defunctionalized Machine, and Session Protocols
- **Judgments of Ours:**
  - `RunMachine ν σ β ε δ ι α χ St κ φ η` ([`Machine/Fibers.lean:438`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Machine/Fibers.lean#L438)): Multi-fiber reactive machine configuration.
  - `Session` ([`Api/HostSession.lean:84`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Api/HostSession.lean#L84)): Protocol automaton for host communication.
  - `HostSpec`, `LawfulHostSpec` ([`Program/Profile.lean:176, 196`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Program/Profile.lean#L176)): Contract for external host environment.
  - `Guarded (m : RunMachine ...)` ([`Laws/Machine/Lift.lean:278`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Machine/Lift.lean#L278)): Invariant of token and key ownership.
  - `DecisionLift` ([`Laws/Machine/Lift.lean:308`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Machine/Lift.lean#L308)): Transition invariance lifter for decisions.
  - `FoldLift` ([`Laws/Machine/Lift.lean:363`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Machine/Lift.lean#L363), row 150): Narrower lift over 8 operational premises.
  - `Projects`, `Refines` ([`Laws/Machine/Refinement.lean:20, 31`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Machine/Refinement.lean#L20)): Refinement mappings and forward simulations.
- **Theorems:**
  - `driveState_lift`, `stepDecisionState_lift`: **proved** ([`Laws/Machine/Lift.lean`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Machine/Lift.lean)): Invariant lifting across machine execution loops.
  - `advance_step`: **proved** ([`Laws/Run.lean:792`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Run.lean#L792)): Keyed host session step law.
  - `projects_compose`, `projects_induces_refines`: **proved** ([`Laws/Machine/Refinement.lean`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Machine/Refinement.lean)): Composition and adequacy of forward simulation relations.
  - `book_replayEval`, `bookMeans_obs`: **proved** ([`Laws/Machine/Book.lean`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Machine/Book.lean)): Forward simulation between native and reference replays.
  - `step_agrees`, `reachable_agrees`: **proved** ([`Laws/Machine/ForkLedger.lean`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Machine/ForkLedger.lean)): Fork ledger trace agreement.
  - Capstone route theorem `m7_of_ledger`: **proved** ([`Laws/Program/Typed/Assembly.lean:1580`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Typed/Assembly.lean#L1580)).
- **Ledger Scopes:** `M1Actions`..`M1Drive`, `M4Handshake` ([`Laws/Program/Guard/Handshake.lean:30`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Guard/Handshake.lean#L30), ceiling 1), `M6Ledger` (9 open, 11 proved), `M7` (4 open).
- **Decisions Rows:** Rows 91–94 (fork ledger and trace agreement), Rows 95–101 (host boundary, keyed session, replay), Row 110 (generic step lifts), Rows 134, 139, 156 (machine state invariant, halting freedom, scope presence), DB-05 (first-order fiber layer), DB-13 (one wake protocol), DB-14 (one logical clock).
- **Modules Covered:** `Machine/Fibers.lean`, `Machine/Stores.lean`, `Machine/Key.lean`, `Api/HostSession.lean`, `Api/Runner.lean`, `Laws/Machine/Lift.lean`, `Laws/Machine/Book.lean`, `Laws/Machine/Refinement.lean`, `Laws/Program/Guard/*.lean`.
- **The Language Cut:**
  Standard TAPL has no concurrency chapter (process calculi or actor systems are outside TAPL). Effect4 provides a full, reified fiber concurrency engine: cooperative fiber multitasking, fork-join supervision, structured scopes with finalizers, promises, deferreds, timers, wake queues, and race interruption. The metatheory is verified not by term rewriting or structural congruence ($\equiv$), but as an inductive invariant of a state machine lifted across execution loops via `FoldLift` / `DecisionLift` and simulated against an idealized reference machine.
