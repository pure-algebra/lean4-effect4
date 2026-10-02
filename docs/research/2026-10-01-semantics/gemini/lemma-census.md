# The Standard Lemma Census by Chapter

This document provides the closed lemma checklist for each of the 17 chapters of the Effect4 language description.

For every lemma on the textbook checklist (TAPL, ATTAPL, Software Foundations / PLF, or cited foundational literature):
- **Present (Proved):** Fully verified Lean theorem in the proof graph with exact `file:line` citation at trust ceiling `[propext, Quot.sound]`.
- **Open (Declared Goal):** Stated as a `#proof_wanted` obligation in the production ledger (`ProofGraph.Obligation`) with its ledger scope and line citation.
- **Absent (Proposed Row):** Identified as a necessary proof obligation not currently declared in the ledger.
- **Absent by Design (Cut):** Not applicable due to a fundamental, deliberate representation cut in Effect4 (e.g. no function values, no step-indexing, prenex-only polymorphism, first-order store typings).

---

## Chapter 1: `tapl-03-evaluation`
*Operational Semantics, Reduction Relations, and Abstract Machines* (TAPL ch. 3, pp. 31–43)

| Standard Lemma | Literature Citation | Status in Effect4 | Declaration / Citation / Rationale |
| :--- | :--- | :--- | :--- |
| Determinism of Evaluation | TAPL Thm 3.5.4, p. 38; PLF *Smallstep* `step_deterministic` | **Proved** | `replay_unique` ([`Laws/Api/Runner.lean:157`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Api/Runner.lean#L157)): Execution is deterministic given an explicit decision tape. |
| Termination / Budget Normal Form | TAPL Thm 3.5.12, p. 41; PLF *Smallstep* `normal_forms_unique` | **Proved** | `Beh_fuel_irrelevant` ([`Laws/Program/RuntimeR.lean:121`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/RuntimeR.lean#L121)); `conv_fixpoint` ([`Laws/Program/IterLimit.lean`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/IterLimit.lean)). |
| Invariance of Transition Step | Harper PFPL §28.2; Owicki–Gries | **Proved** | `driveState_lift`, `stepDecisionState_lift` ([`Laws/Machine/Lift.lean:48, 278`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Machine/Lift.lean#L48)). |
| Observation / Denotation Agreement | Plotkin 1977 (Adequacy); Jacobs ch. 2 | **Proved** | `run_eq_meaning` ([`Laws/Program/Agreement/Machine.lean:1922`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Agreement/Machine.lean#L1922)); `run_eq_ref` ([`Laws/Program/RuntimeR.lean:211`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/RuntimeR.lean#L211)). |
| Syntactic Term Rewriting | TAPL §3.5 Definition 3.5.1 | **Cut** | Effect4 rejects small-step term rewriting; evaluation is mediated by an explicit state machine (`RunMachine`) with defunctionalized continuations (`RSaved`). |

---

## Chapter 2: `tapl-08-typed-arith`
*Type Safety, Progress, and Invariant Preservation* (TAPL ch. 8, pp. 91–98)

| Standard Lemma | Literature Citation | Status in Effect4 | Declaration / Citation / Rationale |
| :--- | :--- | :--- | :--- |
| Inversion of Typing | TAPL Lemma 8.2.2, p. 93; PLF *Types* `inversion` | **Proved** | Covered in pure fragment (`Laws/Program/Typing/Inversion.lean:21-52`). |
| Canonical Forms | TAPL Lemma 8.3.1, p. 95; PLF *Types* `canonical_forms` | **Proved** | `ofVal_toVal` ([`Store/Domain/Canonical.lean:33`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Store/Domain/Canonical.lean#L33)): Values are classified by `Canonical` shapes. |
| Progress (Non-Halting) | TAPL Thm 8.3.2, p. 96; PLF *Types* `progress` | **Proved** | `machineTyped_not_halted` ([`Laws/Program/Typed/Assembly.lean:310`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Typed/Assembly.lean#L310)): $m.\text{stuck} = \text{none}$. |
| Progress (System-Wide Capstone) | Wright & Felleisen 1994 | **Open** | `M7.never_halts` ([`Laws/Program/Typed/Assembly.lean:1856`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Typed/Assembly.lean#L1856)): Replay never halts on answer-free tapes. |
| Preservation (Command Steps) | TAPL Thm 8.3.3, p. 96; PLF *Types* `preservation` | **11 Proved / 9 Open** | 11 goals proved (`Commands/*.lean`); 9 goals open in `M6Ledger` ([`Assembly.lean:1843-1851`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Typed/Assembly.lean#L1843-L1851)). |
| Preservation (Decision Edits) | Manna & Pnueli; Owicki–Gries | **12 Proved / 1 Open** | 12 proved in `M6Edits`; `clockSome` open ([`Assembly.lean:1867`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Typed/Assembly.lean#L1867); row 134 F1). |
| Safety Route Theorem | Wright & Felleisen 1994 | **Proved** | `m7_of_ledger` ([`Laws/Program/Typed/Assembly.lean:1580`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Typed/Assembly.lean#L1580)): Capstone safety derived from M5 and M6. |

---

## Chapter 3: `tapl-09-stlc-cut`
*Pure Program Typing, Inversion, and Decision Procedures* (TAPL ch. 9, pp. 99–112)

| Standard Lemma | Literature Citation | Status in Effect4 | Declaration / Citation / Rationale |
| :--- | :--- | :--- | :--- |
| Inversion of Declarative Typing | TAPL Lemma 9.3.1, p. 104; PLF *Stlc* `inversion` | **Proved** | `inv_succeed`, `inv_fail`, `inv_bind`, `inv_perform`, `inv_sync`, `inv_suspend` ([`Laws/Program/Typing/Inversion.lean:21-52`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Typing/Inversion.lean#L21-L52)). |
| Uniqueness of Types | TAPL Thm 9.3.3, p. 105; PLF *Stlc* `unique_types` | **Proved** | `hasTy_unique` ([`Laws/Program/Typing/Sound.lean:130`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Typing/Sound.lean#L130)): $\text{HasTy } e \, t_1 \land \text{HasTy } e \, t_2 \implies t_1 = t_2$. |
| Context Weakening | TAPL Lemma 9.3.6, p. 106; PLF *Stlc* `weakening` | **Proved** | `hasTy_weaken` ([`Laws/Program/Typing/Sound.lean:156`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Typing/Sound.lean#L156)): Typing preserved under context extension. |
| Substitution Lemma | TAPL Lemma 9.3.8, p. 106; PLF *Stlc* `substitution_preserves_typing` | **Cut** | No lambda abstractions or function values (row 163); variables are positional indices into `TyEnv`. Substitution is replaced by environment indexing and `hasTy_weaken`. |
| Soundness of Algorithmic Typechecker | TAPL §16.1; PLF *Stlc* | **Proved** | `check_sound` ([`Laws/Program/Typing/CheckSound.lean:37`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Typing/CheckSound.lean#L37)): $\text{check } e = \text{ok } t \implies \text{HasTy } e \, t$. |
| Completeness of Algorithmic Typechecker | TAPL §16.1; PLF *Stlc* | **Proved** | `check_complete` ([`Laws/Program/Typing/CheckSound.lean:361`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Typing/CheckSound.lean#L361)): $\text{HasTy } e \, t \implies \text{check } e = \text{ok } t$. |
| Decidability of Typing | TAPL p. 110 | **Proved** | `wellTyped_iff` ([`Laws/Program/Typing/Sound.lean:120`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Typing/Sound.lean#L120)): `check` terminates as a structural fold. |

---

## Chapter 4: `tapl-11-extensions`
*Structural Extensions: Products, Records, Variants, Lists, and Iteration* (TAPL ch. 11, pp. 117–152)

| Standard Lemma | Literature Citation | Status in Effect4 | Declaration / Citation / Rationale |
| :--- | :--- | :--- | :--- |
| Inversion for Extended Forms | TAPL §11.5–§11.11 | **Proved** | `inv_iterate` ([`Laws/Program/Typing/Inversion.lean:111`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Typing/Inversion.lean#L111)); record and product rules in `CheckInversion.lean`. |
| Subtyping Covariance for Products | TAPL §15.2, p. 191 | **Proved** | `sub_prod_mono` ([`Laws/Program/TypeAlgebra.lean:845`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/TypeAlgebra.lean#L845)). |
| Fixed Point Law of Iteration | TAPL §11.11; Elgot 1975 | **Proved** | `conv_fixpoint`, `conv_least`, `conv_unique` ([`Laws/Program/IterLimit.lean`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/IterLimit.lean)). |
| Canonical Record Projection | TAPL §11.6 | **Proved on Copy** | `namedHasTy`, `record_width_refused` ([`type-language-probe/P/probes/P2Ty.lean`](file:///Users/pooks/Dev/lean4-effect4/docs/research/2026-10-01-type-language-probe/P/probes/P2Ty.lean)). |
| Emptiness / Inhabitance of Products | TATA | **Proved** | `inhabited_iff_fits` ([`Laws/Program/Typed/Membership.lean:2240`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Typed/Membership.lean#L2240)). |
| General Non-Terminating Letrec | TAPL §11.11 | **Cut** | General unrestricted recursion is excluded; iteration is isolated in monadic `Eff.iterate`. |

---

## Chapter 5: `tapl-13-references`
*First-Order Mutable References and Kripke Store Typings* (TAPL ch. 13, pp. 153–178)

| Standard Lemma | Literature Citation | Status in Effect4 | Declaration / Citation / Rationale |
| :--- | :--- | :--- | :--- |
| Store Typing Preorder (Refl, Trans) | TAPL Definition 13.5.1, p. 165 | **Proved** | `order_refl`, `order_trans` ([`Laws/Program/Typed/World.lean:411-415`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Typed/World.lean#L411-L415)). |
| Store Typing Monotonicity | TAPL Lemma 13.5.1, p. 165; PLF *References* `store_weakening` | **Proved** | `fits_mono` ([`Laws/Program/Typed/Membership.lean:856`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Typed/Membership.lean#L856)): $w \le w' \implies \text{Fits } w \, v \, \tau \implies \text{Fits } w' \, v \, \tau$. |
| Scope Presence Monotonicity | Kripke semantics | **Proved** | `scopeLive_mono` ([`Laws/Program/Typed/World.lean:432`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Typed/World.lean#L432)): Allocated scopes persist under world extension. |
| Fresh Location Allocation Safety | TAPL Lemma 13.5.3, p. 166 | **Proved** | `valid_refMake_fresh`, `valid_deferredMake_fresh`, `valid_nextToken_fresh` ([`Laws/Program/Typed/Validity.lean:224-226`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Typed/Validity.lean#L224-L226)). |
| Initial Store Validity | PLF *References* | **Proved** | `initial_world_valid` ([`Laws/Program/Typed/Validity.lean:218`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Typed/Validity.lean#L218)). |
| Store Handler Adequacy (Preservation) | TAPL Thm 13.5.3, p. 166 | **66 Proved / 8 Open** | `storeStep_typed` ([`Laws/Program/Typed/Adequacy.lean:59`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Typed/Adequacy.lean#L59)); 66 instances proved, 8 open (`memoGet`, `memoComplete`, 6 `f.total`). |
| Replay Store Soundness | Wright & Felleisen 1994 | **Open** | `M7.stores_typed` ([`Laws/Program/Typed/Assembly.lean:1778`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Typed/Assembly.lean#L1778)): Replay stores fit world typing. |
| Cyclic / Higher-Order Store Typings | TAPL §13.5, p. 164 | **Cut** | References store only first-order values; no step-indexing or cyclic knot-tying is needed. |

---

## Chapter 6: `tapl-14-exceptions`
*Typed Failures, Cause Algebras, and Defect Soundness* (TAPL ch. 14, pp. 179–186)

| Standard Lemma | Literature Citation | Status in Effect4 | Declaration / Citation / Rationale |
| :--- | :--- | :--- | :--- |
| Inversion of Exception Typing | TAPL §14.2 | **Proved** | `inv_fail`, `inv_failCause`, `inv_catchCause`, `inv_matchCause` ([`Laws/Program/Typing/Inversion.lean:26-80`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Typing/Inversion.lean#L26-L80)). |
| Defect Freedom of Typed Failures | Milner 1978 ("well-typed programs cannot go wrong") | **Proved** | `noShapeDefect_failure_iff` ([`Laws/Program/Typed/Membership.lean:150`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Typed/Membership.lean#L150)): Typed exits contain no `badName`/`notImplemented`. |
| Monotonicity of Exit Typing | Kripke semantics | **Proved** | `fitsExit_mono` ([`Laws/Program/Typed/Validity.lean:237`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Typed/Validity.lean#L237)). |
| Exit Soundness Bridge | Plotkin 1977 | **Proved** | `exitHasTy_of_fitsExit` ([`Laws/Program/Typed/ExitConnector.lean:65`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Typed/ExitConnector.lean#L65)): Connecting `FitsExit` to denotational `ExitHasTy`. |
| Replay Exits Typed | Wright & Felleisen 1994 | **Open** | `M7.exits_typed` ([`Laws/Program/Typed/Assembly.lean:1774`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Typed/Assembly.lean#L1774)): Every observed exit fits declared type. |

---

## Chapter 7: `tapl-15-subtyping`
*Algorithmic Subtyping, Bounded Join-Semilattices, and Variance* (TAPL ch. 15, pp. 187–208)

| Standard Lemma | Literature Citation | Status in Effect4 | Declaration / Citation / Rationale |
| :--- | :--- | :--- | :--- |
| Reflexivity of Subtyping | TAPL Rule S-REFL, p. 189 | **Proved** | `sub_refl` ([`Program/Ty.lean:405`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Program/Ty.lean#L405)): $\forall t, \text{sub } t \, t = \text{true}$. |
| Bottom / Top Bounds | TAPL Rules S-TOP, S-BOTTOM, p. 189 | **Proved** | `sub_never` ([`Laws/Program/TypeAlgebra.lean:496`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/TypeAlgebra.lean#L496)); `sub_unknown` ([`:502`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/TypeAlgebra.lean#L502)). |
| Upper Bounds of Join | TAPL Rule S-JOIN | **Proved** | `sub_join_left`, `sub_join_right` ([`Laws/Program/TypeAlgebra.lean:734-742`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/TypeAlgebra.lean#L734-L742)). |
| Soundness against Values | Castagna 2005 (Semantic Subtyping) | **Proved** | `sub_sound` ([`Laws/Program/Template.lean:312`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Template.lean#L312)); `fits_sub` ([`Laws/Program/Typed/Membership.lean:894`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Typed/Membership.lean#L894)). |
| Completeness against Values | Castagna 2005 | **Proved False** | `sub_not_complete` ([`Laws/Program/Template.lean:322`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Template.lean#L322)): Semantic inclusion does not imply syntactic subtyping. |
| Subsumption in Declarative Typing | TAPL Rule T-SUB, p. 189 | **Cut** | Declarative `HasTy` has no subsumption rule; subsumption is pushed into specific syntax forms (`bind`, `perform`). |
| Width Subtyping for Records | TAPL Rule S-RCDWIDTH, p. 189 | **Cut** | Width subtyping is refused at program IR (`record_width_refused`) to prevent unsound type-blind projection; projected only at foreign boundaries (`fits_project`, row 119). |

---

## Chapter 8: `tapl-16-metatheory-subtyping`
*Subtyping Metatheory and Normal-Form Algebras* (TAPL ch. 16, pp. 209–224)

| Standard Lemma | Literature Citation | Status in Effect4 | Declaration / Citation / Rationale |
| :--- | :--- | :--- | :--- |
| Transitivity of Subtyping | TAPL Thm 16.1.3, p. 212 | **Proved** | `sub_trans` ([`Laws/Program/TypeAlgebra.lean:117`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/TypeAlgebra.lean#L117)); `subN_trans` ([`:1071`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/TypeAlgebra.lean#L1071)). |
| Antisymmetry on Normal Forms | TAPL §16.3; Birkhoff | **Proved** | `sub_antisymm_normal` ([`Laws/Program/TypeAlgebra.lean:618`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/TypeAlgebra.lean#L618)); `subN_equiv_iff` ([`:1088`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/TypeAlgebra.lean#L1088)). |
| Normalization Idempotence | Rewriting metatheory | **Proved** | `normalize_idem` ([`Program/Ty.lean:829`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Program/Ty.lean#L829)): $t.\text{normalize}.\text{normalize} = t.\text{normalize}$. |
| Bounded Join-Semilattice Laws | TAPL §16.3, p. 222 | **Proved** | `instLawfulOrderSup` on `CTy` ([`Laws/Program/TypeAlgebra.lean:1288`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/TypeAlgebra.lean#L1288)). |
| Decidability of Subtyping | TAPL Thm 16.1.6, p. 215 | **Proved** | `Ty.sub` is a total, terminating boolean function. |
| Algorithmic Meet (Greatest Lower Bound) | TAPL §16.3, p. 222 | **Cut** | Meets ($\sqcap$) are explicitly not claimed; `CTy` is a join-semilattice, not a full lattice. |

---

## Chapter 9: `tapl-19-nominal`
*Nominal Handle Types, Applied References, and Class Identity* (TAPL ch. 19, pp. 245–259)

| Standard Lemma | Literature Citation | Status in Effect4 | Declaration / Citation / Rationale |
| :--- | :--- | :--- | :--- |
| Nominal Identifier Equality | TAPL §19.3 | **Proved** | `sub_handle` ([`Program/Ty.lean:357`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Program/Ty.lean#L357)): Nominal equality on handles. |
| Handle Minting Soundness | Capability systems | **Proved** | `handles_minted` ([`Laws/Machine/Handles.lean:1042`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Machine/Handles.lean#L1042)): Handles originate only from allocators. |
| Exit Handle Validity | Capability safety | **Proved** | `exitHandles_valid_of_registered` ([`Laws/Program/Typed/Assembly.lean:1515`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Typed/Assembly.lean#L1515)). |
| Exit Handle Validity Capstone | Capstone safety | **Open** | `M7.exitHandles_valid` ([`Laws/Program/Typed/Assembly.lean:1857`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Typed/Assembly.lean#L1857)). |
| Class Method Dispatch Safety | TAPL Thm 19.5.1, p. 256 | **Cut** | No class inheritance tables or dynamic method dispatch; handles index first-order machine resources. |

---

## Chapter 10: `tapl-20-recursive`
*Recursive Types, Inhabitance, and Emptiness Tests* (TAPL ch. 20, pp. 261–280)

| Standard Lemma | Literature Citation | Status in Effect4 | Declaration / Citation / Rationale |
| :--- | :--- | :--- | :--- |
| Inhabitance Decidability | TATA (Tree Automata) | **Proved** | `inhabited` terminates as an inductive fold ([`Program/Admission.lean:79`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Program/Admission.lean#L79)). |
| Inhabitance Soundness | TATA | **Proved** | `inhabited_of_fits` ([`Laws/Program/Typed/Membership.lean:2188`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Typed/Membership.lean#L2188)); `inhabited_of_hasTy` ([`:2224`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Typed/Membership.lean#L2224)). |
| Inhabitance Completeness | TATA | **Proved** | `inhabited_iff_fits` ([`Laws/Program/Typed/Membership.lean:2240`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Typed/Membership.lean#L2240)). |
| Iso-/Equi-Recursive Subtyping | TAPL §20.2–§21.2 | **Cut** | No $\mu X. T$ constructor in `Ty` (row 124); recursion enters exclusively via nominal $\Sigma_{\text{app}}$ declarations (`Ty.app`, row 158). |

---

## Chapter 11: `tapl-22-reconstruction`
*Type Inference, Constraint Solving, and Template Matching* (TAPL ch. 22, pp. 317–338)

| Standard Lemma | Literature Citation | Status in Effect4 | Declaration / Citation / Rationale |
| :--- | :--- | :--- | :--- |
| Soundness of Template Matching | TAPL Thm 22.4.2, p. 327 | **Proved** | `matchTemplate_sound` ([`Laws/Program/Template.lean:58`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Template.lean#L58)): Matched substitutions satisfy subtyping. |
| Monotonicity of Inference | Pottier & Rémy 2005 | **Proved** | `infer_widens` ([`Laws/Program/Template.lean:143`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Template.lean#L143)): `infer` extends substitutions. |
| Invariance on Closed Types | Jones 1994 | **Proved** | `infer_closed` ([`Laws/Program/Template.lean:53`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Template.lean#L53)); `instantiate_closed` ([`:50`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Template.lean#L50)). |
| Most General Unifier (Algorithm W) | TAPL Thm 22.4.3, p. 328 | **Cut** | Full unification is rejected; inference is one-way first-order template pattern matching without unification cycles. |

---

## Chapter 12: `tapl-23-prenex`
*Prenex Polymorphic Templates and First-Order Instantiation* (TAPL ch. 23, pp. 339–358)

| Standard Lemma | Literature Citation | Status in Effect4 | Declaration / Citation / Rationale |
| :--- | :--- | :--- | :--- |
| Closedness of Built-in Rows | System F metatheory | **Proved** | `NativeOp.row_closed` ([`Laws/Program/Template.lean:220`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Template.lean#L220)). |
| Instantiation Preserves Closedness | System F metatheory | **Proved** | `rowTy_closed` ([`Laws/Program/Template.lean:200`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Template.lean#L200)). |
| Admissibility of Closed Templates | System F metatheory | **Proved** | `templateAdmissible_of_closed` ([`Laws/Program/Template.lean:276`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Template.lean#L276)). |
| Type Substitution Lemma | TAPL Lemma 23.4.1, p. 347 | **Proved** | `instantiate_closed` ([`Laws/Program/Template.lean:50`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Template.lean#L50)). |
| Impredicative Type Abstraction ($\Lambda X. t$) | TAPL §23.4 | **Cut** | No System F $\Lambda X. t$ or $\forall X. T$; polymorphism is strictly prenex and first-order within row signatures (`Row`). |

---

## Chapter 13: `attapl-03-effects`
*Effect Signatures, Requirement Rows, and Coeffect Grading* (ATTAPL ch. 3, pp. 87–130)

| Standard Lemma | Literature Citation | Status in Effect4 | Declaration / Citation / Rationale |
| :--- | :--- | :--- | :--- |
| Row Algebra Laws (Comm, Assoc, Idem) | Leijen 2014 (Koka) | **Proved** | `merge_rows_comm` ([`Laws/Program/Provision.lean:105`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Provision.lean#L105)); `merge_rows_assoc`, `merge_rows_idem`. |
| Dependency Discharge by Provision | Katsumata 2014 (Coeffects) | **Proved** | `provide_closed` ([`Laws/Program/Provision.lean:120`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Provision.lean#L120)): Layer provision closes required services. |
| Reassociation of Layer Chains | Petricek et al. 2014 | **Proved** | `provide_provide_rows` ([`Laws/Program/Provision.lean:150`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Provision.lean#L150)). |
| Satisfaction Characterization | Katsumata 2014 | **Proved** | `satisfies_iff_subset_keysRow` ([`Program/Provision.lean:193`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Program/Provision.lean#L193)): Satisfaction is subset inclusion. |
| Conservative Extension (C1–C8) | DB-01; decisions row 111 | **Proved / Open** | `SigExtends`, `check_ext`, `check_restrict`, `lawful_append` ([`Laws/Program/Signature.lean`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Signature.lean); C1, C3, C5, C6 proved; C2, C7, C8 open). |

---

## Chapter 14: `attapl-08-logical-relations`
*Kripke Logical Relations and Protocol Weakest Preconditions* (ATTAPL ch. 8, pp. 343–388)

| Standard Lemma | Literature Citation | Status in Effect4 | Declaration / Citation / Rationale |
| :--- | :--- | :--- | :--- |
| Value Interpretation Monotonicity | Ahmed 2004; ATTAPL §8.4 | **Proved** | `fits_mono` ([`Laws/Program/Typed/Membership.lean:856`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Typed/Membership.lean#L856)): $w \le w' \implies \text{Fits } w \, v \, \tau \implies \text{Fits } w' \, v \, \tau$. |
| Program WP Monotonicity | de Vilhena 2022 §2.4 | **Proved** | `typedProg_mono` ([`Laws/Program/Typed/Residual.lean:686`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Typed/Residual.lean#L686)): Monotonicity of `TypedProg`. |
| Stack Typing Monotonicity | Harper PFPL ch. 28 | **Proved** | `stackAccepts_mono`, `savedOk_mono` ([`Laws/Program/Typed/Contracts.lean:131-139`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Typed/Contracts.lean#L131-L139)). |
| Stack Popping Typing Preservation | Harper PFPL ch. 28 | **Proved** | `popR_typed` ([`Laws/Program/Typed/Stack.lean:142`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Typed/Stack.lean#L142)). |
| Sequencing Compatibility Lemma | de Vilhena 2022 | **Proved** | `seq_typed` ([`Laws/Program/Typed/Seq.lean:59`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Typed/Seq.lean#L59)): Sequencing under equal error columns. |
| Monadic Bind Closure | Standard Monad Metatheory | **Proved False** | `typedProg_not_bind_closed` ([`Test/Program/TypedProgBindRed.lean:32`](file:///Users/pooks/Dev/lean4-effect4/Test/Program/TypedProgBindRed.lean#L32)): Non-local exits break raw bind closure. |
| Fundamental Property / Denotational Adequacy | ATTAPL Thm 8.5.1; Xia et al. 2020 | **Open** | `denoteR_typed` ([`Laws/Program/Typed/Assembly.lean:1839`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Typed/Assembly.lean#L1839)): Checked nodes denote protocol-typed programs. |
| Loaded Configuration Safety | Wright & Felleisen 1994 | **Open** | `typedState_load` ([`Laws/Program/Typed/Assembly.lean:1838`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Typed/Assembly.lean#L1838)). |
| Step-Indexed Logical Relations | Appel–McAllester 2001; Ahmed 2006 | **Cut** | No step-indexing is used; absence of function values leaves `Fits` strictly structural over first-order data. |

---

## Chapter 15: `boundary-embeddings`
*Invertible Syntax Descriptions and Exact Embeddings* (Foster 2007; Rendel 2010)

| Standard Lemma | Literature Citation | Status in Effect4 | Declaration / Citation / Rationale |
| :--- | :--- | :--- | :--- |
| Prism Retraction | Pickering et al. 2017 | **Proved** | `ofVal_toVal` ([`Store/Domain/Canonical.lean:33`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Store/Domain/Canonical.lean#L33)): $\text{ofVal}(\text{toVal } a) = \text{some } a$. |
| Prism Exactness | Pickering et al. 2017 | **Proved** | `ofVal_exact` ([`Store/Domain/Canonical.lean:33`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Store/Domain/Canonical.lean#L33)): $\text{ofVal } v = \text{some } a \implies v = \text{toVal } a$. |
| Schema Bridge Retraction | Rendel & Ostermann 2010 | **Proved** | `ofSchema_schema` ([`Schema/Bridge.lean:412`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Schema/Bridge.lean#L412)): Retraction of Schema bridge. |
| Schema Bridge Exactness modulo `normS` | Foster et al. 2007 | **Proved** | `ofSchema_exact` ([`Schema/Bridge.lean:492`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Schema/Bridge.lean#L492)): Exactness modulo erased annotations. |
| JSON Codec Exactness modulo `normJ` | Foster et al. 2007 | **Proved** | `decode_iff` ([`Laws/Schema/Codec.lean`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Schema/Codec.lean)): Exactness modulo key ordering. |
| Syntax Invertibility (Print/Read) | Rendel & Ostermann 2010 | **Proved** | `read_print` ([`Laws/Codegen/ReadPrint.lean:1904`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Codegen/ReadPrint.lean#L1904)); `read_exact` ([`Laws/Codegen/Read.lean:887`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Codegen/Read.lean#L887)). |

---

## Chapter 16: `initial-algebra`
*Initial Algebras, Catamorphisms, and Coherence* (GTWW 1977; Meijer 1991)

| Standard Lemma | Literature Citation | Status in Effect4 | Declaration / Citation / Rationale |
| :--- | :--- | :--- | :--- |
| Catamorphism Commutation | Meijer et al. 1991 (Bananas) | **Proved** | `cata_build` ([`Program/LayerView.lean:481`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Program/LayerView.lean#L481)): $\text{cata } (\text{build } t) = \text{alg } (\text{map } \text{cata } t)$. |
| View/Build Isomorphism | Wadler 1987; Gill et al. 1993 | **Proved** | `build_view` ([`Program/LayerView.lean:620`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Program/LayerView.lean#L620)): Isomorphism between syntax and description. |
| Unique Homomorphism Theorem | GTWW 1977; Johann & Ghani 2007 | **Proved** | `hom_eq_cata_eff` ([`Program/Fold.lean:1270`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Program/Fold.lean#L1270)); `hom_eq_cata_ty` ([`:89`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Program/Fold.lean#L89)). |
| Coherence Census Verification | Coherence Principle | **Proved** | Audited by `#traversal_census` ([`Laws/Auto/Traversals.lean`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Auto/Traversals.lean)). |

---

## Chapter 17: `machine-concurrency`
*Reactive Fiber Runtime, Defunctionalization, and Session Protocols* (Harper PFPL ch. 28; Wright 1994)

| Standard Lemma | Literature Citation | Status in Effect4 | Declaration / Citation / Rationale |
| :--- | :--- | :--- | :--- |
| Invariant Lifting across Loops | Owicki–Gries; Manna & Pnueli | **Proved** | `driveState_lift`, `stepDecisionState_lift` ([`Laws/Machine/Lift.lean:48, 278`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Machine/Lift.lean#L48)). |
| Host Session Monotonic Advance | Honda 1998; Wadler 2014 | **Proved** | `advance_step` ([`Laws/Run.lean:792`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Run.lean#L792)). |
| Forward Simulation Composition | Lynch & Vaandrager 1995 | **Proved** | `projects_compose`, `projects_induces_refines` ([`Laws/Machine/Refinement.lean:20, 31`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Machine/Refinement.lean#L20)). |
| Simulation to Reference Machine | Milner 1989; Sangiorgi 2011 | **Proved** | `book_replayEval`, `bookMeans_obs` ([`Laws/Machine/Book.lean:196`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Machine/Book.lean#L196)). |
| Trace Agreement with Fork Ledger | Abadi & Lamport 1991 | **Proved** | `step_agrees`, `reachable_agrees` ([`Laws/Machine/ForkLedger.lean`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Machine/ForkLedger.lean)). |
| Capstone Type Safety via Simulation | Wright & Felleisen 1994 | **Proved Route** | `m7_of_ledger` ([`Laws/Program/Typed/Assembly.lean:1580`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Typed/Assembly.lean#L1580)). |
