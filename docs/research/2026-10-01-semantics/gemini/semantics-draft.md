# The Semantics of Effect4: A Chapter-by-Chapter Formalization

Authority: this document is the planned content of `docs/core/semantics.md`. It owns the semantic judgments of Effect4, their formal requirements against Benjamin Pierce's *Types and Programming Languages* (TAPL, 2002) and *Advanced Topics in Types and Programming Languages* (ATTAPL, 2005), their concrete Lean instantiations, and their open obligations.

The architectural frame, sorts, and requirement inventory R1–R13 are owned by [`docs/core/system-map.md`](file:///Users/pooks/Dev/lean4-effect4/docs/core/system-map.md). Open decisions are owned by [`docs/core/decisions.md`](file:///Users/pooks/Dev/lean4-effect4/docs/core/decisions.md).

---

## 1. Operational Semantics and Evaluation (`tapl-03-evaluation`)

### 1.1 What the Judgment Says
Evaluation in Effect4 is defined over defunctionalized abstract machine configurations (`RunMachine`, [`Machine/Fibers.lean:438`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Machine/Fibers.lean#L438)). The judgment `driveStep` ([`Machine/Fibers.lean:1846`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Machine/Fibers.lean#L1846)) evaluates one synchronous command against fiber state, updating the continuation stack or yielding to the scheduler. Multi-fiber execution is driven by `stepDecisionState` ([`Machine/Fibers.lean:2111`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Machine/Fibers.lean#L2111)), consuming an explicit decision tape. At the semantic level, `denoteR` ([`Laws/Program/DenoteR.lean:799`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/DenoteR.lean#L799)) maps a program AST into an interaction tree with bracket markers, whose infinite runs are approximated by budget limits (`denoteB`, [`Laws/Program/DenoteB.lean:208`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/DenoteB.lean#L208)).

### 1.2 What the Chapter Demands
TAPL Chapter 3 demands an operational semantics satisfying determinism of single-step reduction (Theorem 3.5.4), existence of evaluation normal forms (Theorem 3.5.12), and induction principles over evaluation derivations.

### 1.3 The Effect4 Cut
Effect4 rejects syntactic small-step term rewriting ($t \to t'$). Programs are immutable data structures (`Eff`); execution operates via an explicit defunctionalized fiber machine carrying continuation frames (`RSaved`). All non-determinism, interleaving, and timing choices are recorded on an external decision tape (`List Decision`).

### 1.4 Instantiating Theorems
- Determinism of tape replay: `replay_unique` ([`Laws/Api/Runner.lean:157`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Api/Runner.lean#L157)).
- Event-sourced trace reconstruction: `journal_replays` ([`Laws/Run.lean:184`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Run.lean#L184)).
- Fuel independence: `Beh_fuel_irrelevant` ([`Laws/Program/RuntimeR.lean:121`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/RuntimeR.lean#L121)).
- Simulation agreement with denotation on straight-line code: `run_eq_meaning` ([`Laws/Program/Agreement/Machine.lean:1922`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Agreement/Machine.lean#L1922)).
- Simulation agreement on loops: `loopAgreement` ([`Laws/Program/Agreement/Loop.lean:839`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Agreement/Loop.lean#L839)).
- Agreement between frame and reference machines at empty host table: `run_eq_ref` ([`Laws/Program/RuntimeR.lean:211`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/RuntimeR.lean#L211)).

### 1.5 Open Obligations
None. Operational determinism and simulation on host-free fragments are fully verified.

---

## 2. Type Safety, Progress, and Preservation (`tapl-08-typed-arith`)

### 2.1 What the Judgment Says
Type safety is formulated as the maintenance of a configuration invariant across machine steps. `MachineTyped` ($J$, [`Laws/Program/Typed/Assembly.lean:251`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Typed/Assembly.lean#L251)) asserts world validity, store typing, inert fiber code, and scheduler liveness on machine states. `ConfigTyped` ($I$, [`Assembly.lean:263`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Typed/Assembly.lean#L263)) extends $J$ to the live execution queue, typing running fibers by the queued command that continues them. `MachineLive` ([`Assembly.lean:239`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Typed/Assembly.lean#L239)) establishes halting-freedom ($m.\text{stuck} = \text{none}$).

### 2.2 What the Chapter Demands
TAPL Chapter 8 demands Type Safety established via Progress (well-typed terms are either values or can step) and Preservation (stepping preserves typing).

### 2.3 The Effect4 Cut
Syntactic progress is replaced by non-halting of the transition system (`machineTyped_not_halted`). Preservation is factored through the $J$/$I$ split keyed on `running` (decisions row 134), isolating command queue state from the cut-tolerant invariant $J$, and verified across execution loops via `FoldLift` ([`Laws/Machine/Lift.lean:363`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Machine/Lift.lean#L363), row 150).

### 2.4 Instantiating Theorems
- Halting freedom: `machineTyped_not_halted` ([`Laws/Program/Typed/Assembly.lean:310`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Typed/Assembly.lean#L310)).
- Configuration projection: `machineTyped_of_configTyped` ([`Laws/Program/Typed/Assembly.lean:271`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Typed/Assembly.lean#L271)).
- Loop entry premise: `evaluate_entry` ([`Laws/Program/Typed/Assembly.lean:413`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Typed/Assembly.lean#L413)).
- Capstone safety route: `m7_of_ledger` ([`Laws/Program/Typed/Assembly.lean:1580`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Typed/Assembly.lean#L1580)).
- Proved command preservations in `M6Ledger`: `step_trackChild`, `step_drainDue`, `step_link`, `step_evaluate`, `step_resume`, `step_observe`, `step_interruptTarget`, `step_raceCancel`, `step_enrollRace`, `step_afterInterrupt`, `step_closeParAwait` ([`Laws/Program/Typed/Commands/*.lean`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Typed/Commands/Observe.lean#L1353)).

### 2.5 Open Obligations
- `M6Ledger`: `step_loop`, `step_deliver`, `step_finish`, `step_launch`, `step_registrationDone`, `step_exitDone`, `step_wake`, `decision_preserves`, `typedState_reachable` ([`Assembly.lean:1843-1851`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Typed/Assembly.lean#L1843-L1851)).
- `M6Edits`: `clockSome` ([`Assembly.lean:1867`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Typed/Assembly.lean#L1867)).
- `M7`: `never_halts` ([`Assembly.lean:1856`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Typed/Assembly.lean#L1856)).
All wait on decisions row 134 clauses (a)–(e) to land with seat D5.

---

## 3. Pure Program Typing and Decidability (`tapl-09-stlc-cut`)

### 3.1 What the Judgment Says
`HasTy sig env e t` ([`Laws/Program/Typing/HasTy.lean:64`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Typing/HasTy.lean#L64)) is the declarative typing judgment for programs over signature `sig` and environment `env`. `check sig env path e` ([`Program/Checker.lean:24`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Program/Checker.lean#L24)) is the sound and complete decision procedure returning a certificate `EffTy` or a located refusal.

### 3.2 What the Chapter Demands
TAPL Chapter 9 demands Typing Inversion (Lemma 9.3.1), Uniqueness of Types (Theorem 9.3.3), Context Weakening (Lemma 9.3.6), the Substitution Lemma (Lemma 9.3.8), and Decidability of Typing.

### 3.3 The Effect4 Cut
Function values ($\lambda x. t$, arrow types $T_1 \to T_2$) are completely excluded from the language (decisions row 163). Variables are de Bruijn positions indexing an immutable input environment `TyEnv`. Substitution is replaced by positional indexing and environment weakening (`hasTy_weaken`). Subsumption is syntax-directed.

### 3.4 Instantiating Theorems
- Soundness of checker: `check_sound` ([`Laws/Program/Typing/CheckSound.lean:37`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Typing/CheckSound.lean#L37)).
- Completeness of checker: `check_complete` ([`Laws/Program/Typing/CheckSound.lean:361`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Typing/CheckSound.lean#L361)).
- Uniqueness of types: `hasTy_unique` ([`Laws/Program/Typing/Sound.lean:130`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Typing/Sound.lean#L130)).
- Context weakening: `hasTy_weaken` ([`Laws/Program/Typing/Sound.lean:156`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Typing/Sound.lean#L156)).
- Typing inversions: `inv_succeed`, `inv_fail`, `inv_bind`, `inv_perform`, `inv_sync`, `inv_suspend` ([`Laws/Program/Typing/Inversion.lean:21-52`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Typing/Inversion.lean#L21-L52)).
- Decidability: `wellTyped_iff` ([`Laws/Program/Typing/Sound.lean:120`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Typing/Sound.lean#L120)).

### 3.5 Open Obligations
None. The STLC cut and its decision procedures are closed and audited at `[propext, Quot.sound]`.

---

## 4. Structural Extensions: Records, Variants, and Iteration (`tapl-11-extensions`)

### 4.1 What the Judgment Says
Types are extended with first-order products, records, tagged unions, lists, options, and primitives (`unit`, `boolean`, `string`, `nat`, `int`, `number`) ([`Program/Ty.lean:37-65`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Program/Ty.lean#L37-L65)). Pure terms are extended with first-order record construction and projection (`Term.record`, `Term.field`, decisions row 166). General recursion is encapsulated in `Eff.iterate` ([`Program/Eff.lean:559`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Program/Eff.lean#L559)).

### 4.2 What the Chapter Demands
TAPL Chapter 11 demands typing rules, canonical forms, subtyping covariance, and evaluation rules for pairs, records, variants, and general recursion ($\text{fix}$).

### 4.3 The Effect4 Cut
Unrestricted non-terminating letrec is prohibited. Recursion is strictly isolated in monadic `Eff.iterate`, whose denotation is the Kleene limit of budget approximants (`denoteB`, [`Laws/Program/IterLimit.lean`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/IterLimit.lean)). Records carry fields in canonical name order (row 119); projection is untyped and field-name directed (row 165); width subtyping is refused inside programs and projected only at foreign boundaries.

### 4.4 Instantiating Theorems
- Covariance of product subtyping: `sub_prod_mono` ([`Laws/Program/TypeAlgebra.lean:845`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/TypeAlgebra.lean#L845)).
- Iteration typing inversion: `inv_iterate` ([`Laws/Program/Typing/Inversion.lean:111`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Typing/Inversion.lean#L111)).
- Kleene limit fixed-point laws: `conv_fixpoint`, `conv_least`, `conv_unique` ([`Laws/Program/IterLimit.lean`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/IterLimit.lean)).
- Monotonicity of budget approximants: `denoteB_mono` ([`Laws/Program/DenoteB.lean:208`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/DenoteB.lean#L208)).
- Inhabitance agreement: `inhabited_iff_fits` ([`Laws/Program/Typed/Membership.lean:2240`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Typed/Membership.lean#L2240)).

### 4.5 Open Obligations
The data wave (decisions rows 119–132, rows 157–167) lands the record, map, tuple, and number constructors on `Ty` in commits 2–10.

---

## 5. First-Order Mutable References and Store Typings (`tapl-13-references`)

### 5.1 What the Judgment Says
`World` ([`Laws/Program/Typed/World.lean:52`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Typed/World.lean#L52)) is a Kripke store typing holding ghost tables $\Gamma, \Pi, \mathrm{P}, \Theta$. `World.le` ([`World.lean:137`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Typed/World.lean#L137)) defines store extension. `WorldValid` ([`Laws/Program/Typed/Validity.lean:19`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Typed/Validity.lean#L19)) asserts physical store conformity. `ScopeLive` ([`World.lean:149`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Typed/World.lean#L149)) tracks persistent scope presence. `StoreTyped` ([`Laws/Program/Typed/Adequacy.lean:39`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Typed/Adequacy.lean#L39)) asserts store handler adequacy.

### 5.2 What the Chapter Demands
TAPL Chapter 13 demands store typings $\Sigma$, store typing extension $\Sigma \le \Sigma'$, store typing monotonicity ($w \le w' \implies \dots$), location typing inversion, and preservation of store typing under allocation and assignment.

### 5.3 The Effect4 Cut
References are first-order capability indices (`CellId`, `ScopeId`, `FiberId`), never syntactic terms. Store typings $W$ map handles to purely first-order syntactic types (`Ty`). Because stored values contain no closures, store typings require **no step-indexing** or cyclic knot-tying.

### 5.4 Instantiating Theorems
- Store typing preorder: `order_refl`, `order_trans` ([`Laws/Program/Typed/World.lean:411-415`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Typed/World.lean#L411-L415)).
- Value interpretation monotonicity: `fits_mono` ([`Laws/Program/Typed/Membership.lean:856`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Typed/Membership.lean#L856)).
- Scope presence persistence: `scopeLive_mono` ([`Laws/Program/Typed/World.lean:432`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Typed/World.lean#L432)).
- Fresh allocation validity: `valid_refMake_fresh`, `valid_deferredMake_fresh`, `valid_nextToken_fresh` ([`Laws/Program/Typed/Validity.lean:224-226`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Typed/Validity.lean#L224-L226)).
- Store handler adequacy: `storeStep_typed` ([`Laws/Program/Typed/Adequacy.lean:59`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Typed/Adequacy.lean#L59)), with 66 concrete row instances proved ([`Adequacy.lean:1705-1716`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Typed/Adequacy.lean#L1705-L1716)).

### 5.5 Open Obligations
- `M3bAdequacy`: `memoGet_implements`, `memoComplete_implements` ([`Adequacy.lean:1717-1718`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Typed/Adequacy.lean#L1717-L1718)) and 6 `f.total` ref rows, waiting on memo-table typing and `fits_nat_irrel`.
- `M7`: `stores_typed` ([`Laws/Program/Typed/Assembly.lean:1778`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Typed/Assembly.lean#L1778)).

---

## 6. Typed Failures, Cause Algebras, and Defect Freedom (`tapl-14-exceptions`)

### 6.1 What the Judgment Says
`ExitOk w ty ex` ([`Laws/Program/Typed/Admission.lean:31`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Typed/Admission.lean#L31)) defines valid machine exit values. It conjoins semantic exit typing `FitsExit w ty ex` with `NoShapeDefect ty ex` ([`Admission.lean:24`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Typed/Admission.lean#L24)), guaranteeing that typed exits contain no internal dispatch errors (`badName`, `notImplemented`). `ShapeFree` ([`Laws/Program/Typed/Membership.lean:135`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Typed/Membership.lean#L135)) enforces defect-freedom over stored cause trees.

### 6.2 What the Chapter Demands
TAPL Chapter 14 demands typing rules for raising and handling exceptions carrying values, along with progress and preservation in the presence of abortive control flow.

### 6.3 The Effect4 Cut
Effect4 models Effect rc.112's algebraic cause model: structured exits (`Exit.Success`, `Exit.Failure`), composite cause trees (`Cause.Fail`, `Cause.Die`, `Cause.Interrupt`, `Cause.Parallel`, `Cause.Sequential`), cleanly separating typed domain failures (`Fail e`) from untyped runtime defects (`Die d`). The exit judgment guarantees that well-typed programs never encounter internal dispatch defects.

### 6.4 Instantiating Theorems
- Monotonicity of exit typing: `fitsExit_mono` ([`Laws/Program/Typed/Validity.lean:237`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Typed/Validity.lean#L237)).
- Defect exclusion characterization: `noShapeDefect_failure_iff` ([`Laws/Program/Typed/Membership.lean:150`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Typed/Membership.lean#L150)).
- Exit connector to denotational semantics: `exitHasTy_of_fitsExit` ([`Laws/Program/Typed/ExitConnector.lean:65`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Typed/ExitConnector.lean#L65)).
- Exception typing inversions: `inv_fail`, `inv_failCause`, `inv_catchCause`, `inv_matchCause` ([`Laws/Program/Typing/Inversion.lean:26-80`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Typing/Inversion.lean#L26-L80)).

### 6.5 Open Obligations
- `M7`: `exits_typed` ([`Laws/Program/Typed/Assembly.lean:1774`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Typed/Assembly.lean#L1774)).
- H2 part two: coeffect presence contract for `missingService` in `NoShapeDefect` (decisions row 117).

---

## 7. Algorithmic Subtyping and Variance (`tapl-15-subtyping`)

### 7.1 What the Judgment Says
`Ty.sub : Ty -> Ty -> Bool` ([`Program/Ty.lean:352`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Program/Ty.lean#L352)) is the computable algorithmic subtyping judgment. `Ty.subN` ([`Program/Ty.lean:835`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Program/Ty.lean#L835)) defines subtyping on canonical normalized types.

### 7.2 What the Chapter Demands
TAPL Chapter 15 demands Reflexivity (S-REFL), Transitivity (S-TRANS), Top/Bottom bounds (S-TOP, S-BOTTOM), union bounds, and Subsumption (T-SUB).

### 7.3 The Effect4 Cut
Declarative typing `HasTy` contains no subsumption rule; subsumption is pushed into specific syntax forms (`bind`, `perform`). Subtyping is verified algorithmically via boolean decision procedures over normalized types (`subN`). Record subtyping is strictly exact: width subtyping is refused in program syntax to ensure soundness of untyped projection.

### 7.4 Instantiating Theorems
- Subtyping reflexivity: `sub_refl` ([`Program/Ty.lean:405`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Program/Ty.lean#L405)).
- Bottom and top bounds: `sub_never` ([`Laws/Program/TypeAlgebra.lean:496`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/TypeAlgebra.lean#L496)); `sub_unknown` ([`:502`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/TypeAlgebra.lean#L502)).
- Union upper bounds: `sub_join_left`, `sub_join_right` ([`Laws/Program/TypeAlgebra.lean:734-742`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/TypeAlgebra.lean#L734-L742)).
- Soundness against value membership: `sub_sound` ([`Laws/Program/Template.lean:312`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Template.lean#L312)); `fits_sub` ([`Laws/Program/Typed/Membership.lean:894`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Typed/Membership.lean#L894)).
- Incompleteness against semantic values: `sub_not_complete` ([`Laws/Program/Template.lean:322`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Template.lean#L322)).

### 7.5 Open Obligations
None. Algorithmic subtyping is fully verified at `[propext, Quot.sound]`.

---

## 8. Subtyping Metatheory and Normal Forms (`tapl-16-metatheory-subtyping`)

### 8.1 What the Judgment Says
`CTy` ([`Program/Ty.lean:842`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Program/Ty.lean#L842)) is the subtype of normalized types. `CTy.join` ([`Program/Ty.lean:848`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Program/Ty.lean#L848)) computes least upper bounds. `subN` orders canonical types.

### 8.2 What the Chapter Demands
TAPL Chapter 16 demands transitivity and reflexivity elimination, algorithmic termination, soundness and completeness of algorithmic subtyping, and existence of joins and meets.

### 8.3 The Effect4 Cut
`sub` is implemented directly as a terminating boolean function. Meets ($\sqcap$) are explicitly omitted; `CTy` is a bounded join-semilattice, not a lattice.

### 8.4 Instantiating Theorems
- Subtyping transitivity: `sub_trans` ([`Laws/Program/TypeAlgebra.lean:117`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/TypeAlgebra.lean#L117)); `subN_trans` ([`:1071`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/TypeAlgebra.lean#L1071)).
- Antisymmetry on normal forms: `sub_antisymm_normal` ([`Laws/Program/TypeAlgebra.lean:618`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/TypeAlgebra.lean#L618)); `subN_equiv_iff` ([`:1088`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/TypeAlgebra.lean#L1088)).
- Idempotence of normalization: `normalize_idem` ([`Program/Ty.lean:829`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Program/Ty.lean#L829)).
- Lawful join-semilattice instance: `instLawfulOrderSup` on `CTy` ([`Laws/Program/TypeAlgebra.lean:1288`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/TypeAlgebra.lean#L1288)).
- Partial order instance: `instIsPartialOrder` on `CTy` ([`Laws/Program/TypeAlgebra.lean:1271`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/TypeAlgebra.lean#L1271)).

### 8.5 Open Obligations
None. Metatheory of the normalized join-semilattice is closed.

---

## 9. Nominal Types, Handles, and Class Identity (`tapl-19-nominal`)

### 9.1 What the Judgment Says
`Ty.handle` ([`Program/Ty.lean:45`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Program/Ty.lean#L45)) and `Ty.app` (decisions row 158) represent nominal types. `HandleFits` ([`Laws/Program/Typed/Membership.lean:62`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Typed/Membership.lean#L62)) validates capability handles against world declarations. `ExitHandlesValid` ([`Laws/Program/Typed/Assembly.lean:1787`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Typed/Assembly.lean#L1787)) asserts that recorded exits reference only live allocated handles.

### 9.2 What the Chapter Demands
TAPL Chapter 19 demands class table typing, nominal subtyping, and safe capability lookup.

### 9.3 The Effect4 Cut
Classes and dynamic method dispatch are cut. Nominal types represent either runtime capability handles (`FiberId`, `CellId`, `ScopeId`) or external TypeScript nominal classes (`Queue.Dequeue<Job>`, `Data.TaggedError`).

### 9.4 Instantiating Theorems
- Nominal equality: `sub_handle` ([`Program/Ty.lean:357`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Program/Ty.lean#L357)).
- Capability minting soundness: `handles_minted` ([`Laws/Machine/Handles.lean:1042`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Machine/Handles.lean#L1042)).
- Exit handle validity up to registered bytes: `exitHandles_valid_of_registered` ([`Laws/Program/Typed/Assembly.lean:1515`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Typed/Assembly.lean#L1515)).

### 9.5 Open Obligations
- `M7`: `exitHandles_valid` ([`Laws/Program/Typed/Assembly.lean:1857`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Typed/Assembly.lean#L1857)), waiting on decisions row 180 (registered handle bytes invariant).

---

## 10. Recursive Types and Inhabitance (`tapl-20-recursive`)

### 10.1 What the Judgment Says
`Ty.inhabited : Ty -> Bool` ([`Program/Admission.lean:79`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Program/Admission.lean#L79)) is an inductive decision procedure checking regular-tree type non-emptiness.

### 10.2 What the Chapter Demands
TAPL Chapter 20 demands iso-/equi-recursive type formalisms ($\mu X. T$) and unfolding laws.

### 10.3 The Effect4 Cut
`Ty` excludes an explicit $\mu X. T$ constructor (decisions row 124). Recursion enters strictly through nominal $\Sigma_{\text{app}}$ declarations via `Ty.app` (row 158). The sole recursive metatheorem is regular-tree non-emptiness (`inhabited`), ensuring admitted program columns are never uninhabited (`never`).

### 10.4 Instantiating Theorems
- Inhabitance soundness against value membership: `inhabited_of_fits` ([`Laws/Program/Typed/Membership.lean:2188`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Typed/Membership.lean#L2188)).
- Inhabitance soundness against pure typing: `inhabited_of_hasTy` ([`Laws/Program/Typed/Membership.lean:2224`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Typed/Membership.lean#L2224)).
- Inhabitance completeness: `inhabited_iff_fits` ([`Laws/Program/Typed/Membership.lean:2240`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Typed/Membership.lean#L2240)).

### 10.5 Open Obligations
None. Inhabitance metatheory is closed (pass I2, merged `c898ad04`).

---

## 11. Type Inference and Template Matching (`tapl-22-reconstruction`)

### 11.1 What the Judgment Says
`matchTemplate` ([`Program/Ty.lean:530`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Program/Ty.lean#L530)) matches an incoming request type against an operation row template, computing a substitution `Subst`. `Ty.infer` ([`Program/Ty.lean:508`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Program/Ty.lean#L508)) threads substitutions across argument lists.

### 11.2 What the Chapter Demands
TAPL Chapter 22 demands Algorithm W, unification soundness and completeness, and most general unifiers.

### 11.3 The Effect4 Cut
Full unification is rejected. Effect4 uses one-way first-order template pattern matching without unification cycles. The `join` parameter mirrors TypeScript's `NoInfer` and common supertype heuristics.

### 11.4 Instantiating Theorems
- Soundness of template matching: `matchTemplate_sound` ([`Laws/Program/Template.lean:58`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Template.lean#L58)).
- Substitution extension: `infer_widens` ([`Laws/Program/Template.lean:143`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Template.lean#L143)).
- Invariance on closed types: `infer_closed` ([`Laws/Program/Template.lean:53`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Template.lean#L53)).

### 11.5 Open Obligations
None. Template matching metatheory is closed.

---

## 12. Prenex Universal Polymorphism (`tapl-23-prenex`)

### 12.1 What the Judgment Says
`Ty.var (i : Nat)` ([`Program/Ty.lean:39`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Program/Ty.lean#L39)) represents de Bruijn parameters within row templates. `instantiate` ([`Program/Ty.lean:475`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Program/Ty.lean#L475)) applies concrete type substitutions.

### 12.2 What the Chapter Demands
TAPL Chapter 23 demands System F impredicative polymorphism, type abstractions ($\Lambda X. t$), type applications ($t [T]$), and type substitution lemmas.

### 12.3 The Effect4 Cut
Impredicative polymorphism is cut. Type variables exist only inside operation row templates (`Row`), instantiated at request sites. Program syntax contains no type abstractions or applications.

### 12.4 Instantiating Theorems
- Built-in rows closed: `NativeOp.row_closed` ([`Laws/Program/Template.lean:220`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Template.lean#L220)).
- Closed template admissibility: `templateAdmissible_of_closed` ([`Laws/Program/Template.lean:276`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Template.lean#L276)).
- Row instantiation closedness: `rowTy_closed` ([`Laws/Program/Template.lean:200`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Template.lean#L200)).
- Identity substitution on closed types: `instantiate_closed` ([`Laws/Program/Template.lean:50`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Template.lean#L50)).

### 12.5 Open Obligations
None.

---

## 13. Effect Signatures, Requirement Rows, and Coeffects (`attapl-03-effects`)

### 13.1 What the Judgment Says
`RowTable` ([`Program/Native.lean:82`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Program/Native.lean#L82)) specifies algebraic effect rows $\Sigma_{\text{app}}$. `EffTy.requires` ([`Program/Ty.lean:68`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Program/Ty.lean#L68)) grades program types with requirement rows. Layer provision (`provideLayer`, [`Program/Provision.lean:322`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Program/Provision.lean#L322)) discharges dependencies via the substitution equation $R_{\text{in}} = (R_{\text{body}} \setminus R_{\text{out}}) \cup R_{\text{layer}}$.

### 13.2 What the Chapter Demands
ATTAPL Chapter 3 demands effect rows, row polymorphism, effect masking, and coeffect grading soundness.

### 13.3 The Effect4 Cut
Algebraic effects and coeffects are cleanly factored: operation requests are handled by the runtime or host session, while service dependencies are flat coeffect sets forming a bounded join-semilattice with relative complement.

### 13.4 Instantiating Theorems
- Row commutativity: `merge_rows_comm` ([`Laws/Program/Provision.lean:105`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Provision.lean#L105)).
- Provision closure: `provide_closed` ([`Laws/Program/Provision.lean:120`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Provision.lean#L120)).
- Chain reassociation: `provide_provide_rows` ([`Laws/Program/Provision.lean:150`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Provision.lean#L150)).
- Satisfaction characterization: `satisfies_iff_subset_keysRow` ([`Program/Provision.lean:193`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Program/Provision.lean#L193)).
- Conservative extension: `SigExtends`, `check_ext`, `check_restrict`, `lawful_append` ([`Laws/Program/Signature.lean`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Signature.lean)).

### 13.5 Open Obligations
Conservative extension obligations C2, C7, C8 remain open (decisions row 111).

---

## 14. Kripke Logical Relations and Protocol Invariants (`attapl-08-logical-relations`)

### 14.1 What the Judgment Says
`Fits w v ty` ([`Laws/Program/Typed/Membership.lean:98`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Typed/Membership.lean#L98)) is the world-indexed value interpretation $V\llbracket\tau\rrbracket(W)$. `TypedProg root w ty p` ([`Laws/Program/Typed/Residual.lean:248`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Typed/Residual.lean#L248)) is the weakest-precondition predicate on interaction trees. `FrameAccepts` and `SavedOk` ([`Laws/Program/Typed/Contracts.lean:43, 82`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Typed/Contracts.lean#L43)) define Kripke-closed stack typings. `DenotesTyped` ([`Laws/Program/Typed/Assembly.lean:1075`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Typed/Assembly.lean#L1075)) is the Fundamental Property of Logical Relations.

### 14.2 What the Chapter Demands
ATTAPL Chapter 8 demands Kripke logical relations, world monotonicity, the Fundamental Theorem of Logical Relations, and semantic soundness.

### 14.3 The Effect4 Cut
Because higher-order function values are excised (row 163), `Fits` contains no arrow clause. Store typings $W$ are first-order syntactic types. Consequently, the Kripke model requires **no step-indexing**. Non-local exit markers (`unguard`) break raw monadic bind closure (`typedProg_not_bind_closed`); sequencing is mediated by construct-specific lemmas (`seq_typed`).

### 14.4 Instantiating Theorems
- Value relation monotonicity: `fits_mono` ([`Laws/Program/Typed/Membership.lean:856`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Typed/Membership.lean#L856)).
- Program relation monotonicity: `typedProg_mono` ([`Laws/Program/Typed/Residual.lean:686`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Typed/Residual.lean#L686)).
- Stack typing monotonicity: `stackAccepts_mono`, `savedOk_mono` ([`Laws/Program/Typed/Contracts.lean:131-139`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Typed/Contracts.lean#L131-L139)).
- Stack popping preservation: `popR_typed` ([`Laws/Program/Typed/Stack.lean:142`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Typed/Stack.lean#L142)).
- Sequencing compatibility lemma: `seq_typed` ([`Laws/Program/Typed/Seq.lean:59`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Typed/Seq.lean#L59)).

### 14.5 Open Obligations
- `M3bAssembly.denoteR_typed` ([`Laws/Program/Typed/Assembly.lean:1839`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Typed/Assembly.lean#L1839), wanted): Fundamental property of denotation.
- `M3bAssembly.typedState_load` ([`Laws/Program/Typed/Assembly.lean:1838`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Typed/Assembly.lean#L1838), wanted).
Waiting on reference-formation premise `layerRefsWF` (row 170) and completed-view typing (row 175).

---

## 15. Invertible Syntax and Exact Embeddings (`boundary-embeddings`)

### 15.1 What the Judgment Says
A K2 exact embedding consists of a pair $\text{write} : A \to F$, $\text{read} : F \to \text{Option } A$ that is total on domain, satisfies retraction $\text{read}(\text{write } a) = \text{some } a$, and exactness $\text{read } v = \text{some } a \implies v \equiv \text{write } a \pmod{\text{norm}}$.

### 15.2 What the Chapter Demands
Foundational literature on lenses (Foster 2007) and invertible syntax (Rendel & Ostermann 2010) demands bidirectional partial isomorphisms without silent data loss.

### 15.3 The Effect4 Cut
All external boundaries (JSON, Schema AST, printed TypeScript) are formalized as lawful prisms (`Canonical`) or exact embeddings modulo named normalisers (`normJ` for JSON key ordering, `normS` for Schema annotation erasure).

### 15.4 Instantiating Theorems
- `Canonical` retraction and exactness: `ofVal_toVal`, `ofVal_exact` ([`Store/Domain/Canonical.lean:33`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Store/Domain/Canonical.lean#L33)).
- JSON codec exactness modulo `normJ`: `decode_iff` ([`Laws/Schema/Codec.lean`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Schema/Codec.lean)).
- Schema bridge exactness modulo `normS`: `ofSchema_exact` ([`Schema/Bridge.lean:492`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Schema/Bridge.lean#L492)); retraction: `ofSchema_schema` ([`:412`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Schema/Bridge.lean#L412)).
- Syntax printer/reader invertibility: `read_print` ([`Laws/Codegen/ReadPrint.lean:1904`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Codegen/ReadPrint.lean#L1904)); `read_exact` ([`Laws/Codegen/Read.lean:887`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Codegen/Read.lean#L887)).

### 15.5 Open Obligations
None. Exactness of embeddings at today's forms is verified (seat W1, merged `cdd62673`).

---

## 16. Initial Algebras, Catamorphisms, and Coherence (`initial-algebra`)

### 16.1 What the Judgment Says
`cataFam` ([`Program/LayerView.lean:414`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Program/LayerView.lean#L414)), `cata_eff` ([`Program/Fold.lean:1104`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Program/Fold.lean#L1104)), and `cata_ty` ([`Program/Fold.lean:31`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Program/Fold.lean#L31)) define unique catamorphisms over initial syntax algebras.

### 16.2 What the Chapter Demands
Categorical initial algebra semantics (GTWW 1977, Meijer 1991) demands existence and uniqueness of algebra homomorphisms (the universal mapping property).

### 16.3 The Effect4 Cut
Effect4 strictly enforces the **Coherence Principle**: each syntax sort has exactly one free object representation. Every traversal must be an algebra of the initial fold (`cata`), ensuring that any two traversals agreeing on constructor algebras are definitionally equal by fold uniqueness (`hom_eq_cata_eff`), with hand matches audited by `#traversal_census`.

### 16.4 Instantiating Theorems
- Unique homomorphism out of `Eff`: `hom_eq_cata_eff` ([`Program/Fold.lean:1270`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Program/Fold.lean#L1270)).
- Unique homomorphism out of `Ty`: `hom_eq_cata_ty` ([`Program/Fold.lean:89`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Program/Fold.lean#L89)).
- Catamorphism commutation: `cata_build` ([`Program/LayerView.lean:481`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Program/LayerView.lean#L481)).
- View/Build isomorphism: `build_view` ([`Program/LayerView.lean:620`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Program/LayerView.lean#L620)).

### 16.5 Open Obligations
None.

---

## 17. Reactive Fiber Concurrency and Session Protocols (`machine-concurrency`)

### 17.1 What the Judgment Says
`RunMachine` ([`Machine/Fibers.lean:438`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Machine/Fibers.lean#L438)) represents a concurrent machine state with cooperative fibers, wake queues, and supervision trees. `Session` ([`Api/HostSession.lean:84`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Api/HostSession.lean#L84)) manages host interaction protocols. `DecisionLift` and `FoldLift` ([`Laws/Machine/Lift.lean:308, 363`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Machine/Lift.lean#L308)) lift state invariants across reactive loops.

### 17.2 What the Chapter Demands
Concurrency metatheory (Harper PFPL ch. 28, Milner 1989, Lynch & Vaandrager 1995) demands forward simulations, step invariance, trace agreements, and protocol conformance.

### 17.3 The Effect4 Cut
Concurrency is verified not through process calculus structural congruences, but as an inductive state invariant lifted across loops via `FoldLift` and related to an idealized reference interpreter via forward simulation `BMeans` (`run_eq_ref`).

### 17.4 Instantiating Theorems
- Invariant lifting: `driveState_lift`, `stepDecisionState_lift` ([`Laws/Machine/Lift.lean`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Machine/Lift.lean)).
- Session protocol advance: `advance_step` ([`Laws/Run.lean:792`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Run.lean#L792)).
- Refinement simulation composition: `projects_compose`, `projects_induces_refines` ([`Laws/Machine/Refinement.lean`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Machine/Refinement.lean)).
- Simulation between reference and compiled runs: `book_replayEval`, `bookMeans_obs` ([`Laws/Machine/Book.lean`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Machine/Book.lean)).
- Fork ledger trace agreement: `step_agrees`, `reachable_agrees` ([`Laws/Machine/ForkLedger.lean`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Machine/ForkLedger.lean)).
- Capstone route: `m7_of_ledger` ([`Laws/Program/Typed/Assembly.lean:1580`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Typed/Assembly.lean#L1580)).

### 17.5 Open Obligations
M7 capstone obligations (`M7.exits_typed`, `M7.stores_typed`, `M7.never_halts`, `M7.exitHandles_valid`, [`Assembly.lean:1854-1857`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Typed/Assembly.lean#L1854-L1857)), which follow by `m7_of_ledger` once M5 and M6 close.
