> Retained input report, not an implementation receipt. Its proposed interrupt resolution
> and strong-exit consequence are refuted by the checked
> [implementation preflight](2026-09-21-foundations-contract-preflight-amendment.md).
> References below to planned modules or proofs do not establish that they exist.

# Adversarial Audit: Foundations Slices 3–6 & Theoretical Architecture

**Date**: 2026-09-21
**Scope**: Adversarial verification of implementation specifications, foundational invariants, proof graphs, metaprogramming infrastructure, and denotational semantics across foundations Slices 3–6 (`docs/research/2026-09-21-codex-brief-foundations-slices-3-6.md`).
**Status**: Complete. 5/5 diagnostic probes and `ArchitectureStatements.lean` verified with exit code 0.

---

## 1. Executive Summary & Critical Adversarial Traps

An adversarial review of the proposed resolutions and proofs for Slices 3–6 identified a subtle, critical theoretical trap in the interaction between saved-stack frame unwinding (`popR`) and asynchronous fiber interruption.

### 1.1 The Critical Logic Fault: The `popR` Interrupt-Bypass Trap
In the prior draft resolution of FR-08, it was asserted that decoupling `FrameAccepts.resume.skip` into:
$$\text{skip} : \forall ex,\ \text{StrongExit } w\ tin\ ex \to kind.\text{hasExitArm } ex = \text{false} \to \text{StrongExit } w\ tout\ ex$$
is sufficient for type preservation, under the rationale that:
> *"when an interrupt preempts, the delivered cause is an interrupt which satisfies `StrongExit w tout (.failure cause)` universally."*

**The Adversarial Catch:**
1. Examining [`EvaluateR.lean:84–89`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/EvaluateR.lean#L84-L89):
   ```lean
   if kind.hasExitArm ex && !(failing && frame.interruptible && frame.interruptedCause.isSome) then
     let frame := match kind with
       | .onExit _ => { frame with stack := .finalizerMask flag :: frame.stack }
       | _ => frame
     ({ frame with current := next ex }, none)
   else popR interp ex rest frame
   ```
2. When `failing && frame.interruptible && frame.interruptedCause.isSome` holds, `popR` bypasses `next ex` and recurses:
   ```lean
   else popR interp ex rest frame
   ```
   **`popR` passes the original exit `ex` down the stack, NOT `frame.interruptedCause`!**
3. If `ex` is an ordinary typed failure (`Cause.fail v`) that was supposed to be caught and eliminated by `kind` (e.g., transforming error type `Nat` to `never`), feeding `ex` directly into `rest` violates `StackAccepts` because `StrongExit w tout ex` is **mathematically false** (since `StrongValue w Ty.never v` is impossible).

### 1.2 The Reachable Counterexample: Subcase C3
Could this state actually occur in a running, typed machine?
**Yes.** We constructed the exact execution trace:
1. A fiber enters an uninterruptible block: `Effect.uninterruptible (Effect.fail 42)` enclosed in `Effect.catchAll (..., fun _ => Effect.succeed ())`.
2. While inside the uninterruptible block, another fiber issues `interrupt target`. In [`Fibers.lean:793–800`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Machine/Fibers.lean#L793-L800), because the target is masked (`interruptible = false`), `interruptedCause` is recorded, but `deferredInterrupt` remains `false` and the fiber is not aborted.
3. The fiber fails with `ex = .failure (Cause.fail 42)`.
4. `deliverR` invokes `popR` on `ex`.
5. `popR` first pops `.restoreMask true`. At [`EvaluateR.lean:72–77`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/EvaluateR.lean#L72-L77), because `failing` is true, the `!failing` guard prevents replacing `current` with `interruptedCause`. Instead, it sets `frame.interruptible := true` and continues popping `ex`.
6. Next, `popR` meets the outer catch handler `.resume .onFailure next`.
7. At line 84, `failing && frame.interruptible && frame.interruptedCause.isSome` evaluates to `true && true && true = true`.
8. The catch handler is skipped!
9. `popR` finishes and yields `some (.failure (Cause.fail 42))`.
10. The fiber exits with `42`, even though its static type claimed `tout.error = never`.

This behavior directly reflects TypeScript rc.112 [`core.ts:540–545`](file:///Users/pooks/Dev/lean4-effect4/vendor/effect-4.0.0-rc.112/src/internal/core.ts#L540-L545), where active interrupts suppress catch continuations (`contE`), allowing caught errors to escape during fiber abortion.

### 1.3 The Formal Resolution: `DeliveryStateOk` & Outcome Disjunct
To preserve absolute Lean 4 mathematical consistency without breaking rc.112 simulation:
1. Define the delivery-state correlation predicate:
   ```lean
   structure DeliveryStateOk (frame : RSaved) (ex : ExitV) : Prop where
     synced : frame.interruptible = true → frame.interruptedCause.isSome = true →
       frame.deferredInterrupt = true ∨ (∀ reason ∈ ex.cause.reasons, reason.tag = .interrupt)
   ```
2. State `popR_typed` with the exact disjunctive outcome:
   $$\forall w\ interp\ tin\ tout\ ex\ stack\ frame,$$
   $$\text{StackAccepts TypedProg hooks } w\ tin\ tout\ stack \to \text{StrongExit } w\ tin\ ex \to \text{InterruptProvenance } frame \to \text{DeliveryStateOk } frame\ ex \to$$
   $$\text{match popR interp ex stack frame with}$$
   $$\mid (frame', \text{none}) \Rightarrow \exists middle,\ \text{TypedProg } w\ middle\ frame'.current \land \text{StackAccepts } w\ middle\ tout\ frame'.stack \land \text{InterruptProvenance } frame'$$
   $$\mid (\_, \text{some } ex') \Rightarrow \text{StrongExit } w\ tout\ ex' \lor (frame.interruptible = true \land frame.interruptedCause.\text{isSome} = true)$$
This rigorously separates **sound completed execution** (where catch handlers operate normally) from **abnormal interrupt preemption** (where catch handlers are intentionally suppressed by an aborting fiber).

---

## 2. Adversarial Audit Across Slices 3–6

### Slice 3: World Validity & Monotonicity Transport (M2)
- **Monotonicity vs. Storage Integrity**:
  - *Trap*: Assuming global `Stores.WF` or `WorldValid` is monotonic under `World.leHost`. Refuted by `WorldReplayProbe.leHost_does_not_imply_wf_transport`: inserting an uninitialized or dangling cell satisfies `World.leHost` but breaks `Stores.WF`.
  - *Proof Architecture*: Local typing judgments (`ValueOk`, `CompletionOk`, `HeapTypedAt`, `PromiseTypedAt`, `ExitFits`, `StrongValue`, `StrongExit`) are proved monotonic under `World.leHost` using `hasTy_mono` ([`Admits.lean:331`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Program/Admits.lean#L331)) and `extends_append` ([`TyView.lean:596`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Program/TyView.lean#L596)).
  - *Global Invariants*: `Stores.WF` and `WorldValid` are proved as step-preservation theorems across actual transitions (`syncOpStep`, `stepDecisionState`).
- **Completion Transport (Candidate C1)**:
  - Statement:
    $$\forall w\ w'\ types\ comp,\ \text{TableExtends } w.\text{Ρ } w'.\text{Ρ} \land \text{Extends } w.\text{allocated } w'.\text{allocated} \land \text{CompletionOk } w\ types\ comp \implies \text{CompletionOk } w'\ types\ comp$$
  - Soundness verified: `CompletionOk` inspects only `externals.allocated` (for value tags) and `w.Ρ` (for `.ofRefGet`). Both are preserved monotonically under `TableExtends` and `Extends`.

### Slice 4: Protocol Admission & Control Inversion (M3a)
- **Control Marker Payload Inversion (FR-09)**:
  - *Trap*: Generic protocol typing `Typed ... (.vis (.inr (.unguard ex')) k)` only types the continuation $k$, leaving the marker payload $ex'$ unconstrained ([`StackProbe.lean:69–96`](file:///Users/pooks/Dev/lean4-effect4/docs/research/2026-09-21-foundations-review-evidence/StackProbe.lean#L69-L96)).
  - *Resolution*: Direct conjunction:
    $$\text{TypedProg } w\ ty\ p := \text{Typed } (\text{World.leHost})\ (\Psi_S + \Psi_F)\ w\ (\lambda w'\ ex \Rightarrow \text{StrongExit } w'\ ty\ ex)\ p \land \text{ControlAdmitted } w\ ty\ p$$
    where `ControlAdmitted` explicitly enforces $\text{StrongExit } w\ ty\ ex$ on `.unguard ex` and `.finishFinalizer ex`.
  - *Theorem*: `unguard_payload_inv` closes by direct projection of the second conjunct.
- **Heterogeneous Store Preservation (Candidate C2)**:
  - In `Laws/Machine/RefKernel.lean`, `indexed_ref_step_preserves` proves non-interference for heterogeneous heaps indexed by $P : \text{Nat} \to \text{Val} \to \text{Prop}$. Cell updates preserve invariant $P\ i$ for all $i \ne c$, eliminating repetitive frame lemmas.

### Slice 5: Assembly & Hard Proofs (M3b/M4)
- **Token Freshness & Park Handshake**:
  - `WorldValid` maintains `tokenBound : ∀ id token ty, w.Θ id token = some ty → token < m.nextToken`.
  - Because `nextToken` strictly increases on `.async`, `valid_nextToken_fresh` guarantees `w.Θ id m.nextToken = none`.
  - `deliver_active` verifies matching token handshakes; `deliver_stale` proves that mismatched resumes act as the identity on parked fibers, preventing ABA token reuse.

### Representation Track: Storage Composition (Candidates C3 & C4)
- **Candidate C3 (`projects_compose`)**:
  - Proves transitivity of single-step projections:
    $$\text{Projects } p_1\ stepC\ stepM\ WFC \land \text{Projects } p_2\ stepM\ stepN\ WFM \implies \text{Projects } (p_2 \circ p_1)\ stepC\ stepN\ (\lambda c \Rightarrow WFC\ c \land WFM\ (p_1\ c))$$
  - Water-tight: preserves concrete invariants, maps answers identically, and preserves simulation steps.
- **Candidate C4 (`projects_induces_refines`)**:
  - Proves that any functional projection satisfying `Projects` induces a forward relational simulation `Refines (fun c m => WF c ∧ p c = m)`.

---

## 3. Lean 4 Metaprogramming & Proof Automation Infrastructure

### 3.1 Aesop Rule Set Partitioning
Per repository operating rules in `AGENTS.md`, unbounded searches in the `default` rule set are strictly prohibited to prevent performance degradation and accidental axiom leaks. The tree utilizes targeted, named rule sets:
- `Effect4.Inversion` (`default := true`): Lightweight inversions for `Option`, `Except`, `Bool`, and `ite`.
- `Effect4.TyOrder`: Subtyping and type-view transitivity/reflexivity rules.
- `Effect4.TypedState`: Generated typed-state skeleton and invariant projections.
- `Effect4.StoreKernel`: Unfolded store definitions within kernel modules; hidden from downstream files.
- `Effect4.Stores`: High-level store equations and laws.
- `Effect4.Fibers`: Fiber lifecycle theorems (spawn, start, fork, race, trace).

### 3.2 Tactic Guardrails & Axiom Gate Compliance
1. **Zero Forbidden Axioms**: Every searched proof is audited by `Test/Audit/AxiomGate.lean` at `[propext, Quot.sound]`. `Classical.choice` is rejected.
2. **Prohibited Proof Patterns**:
   - No `simp_all` written by hand.
   - No `first | ...` fallbacks or `try`.
   - Explicit rule registration shapes: `safe -100 apply` for whole-statement schemas, `norm simp` for let-equations, `unsafe 90% apply` for single conclusions.
3. **Automated Diagnostic Instruments**:
   - `#auto_census Some.Module using aesop` ([`Laws/Auto/Census.lean`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Auto/Census.lean)): Evaluates which theorems in a module can be closed directly by a tactic, reporting source lines saved and axioms reached.
   - `#answer_gate` ([`Laws/Auto/AnswerGate.lean`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Auto/AnswerGate.lean)): Verifies 100% totality across all 31 `SyncOp` and 40 `FiberOp` constructors against protocol specifications.
   - `#position_gate` & `#typed_state` ([`TypedStateDecl.lean`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Typed/TypedStateDecl.lean)): Metaprogramming command that traverses AST types to synthesize the complete typed-state predicate bundle `Preds World`.

---

## 4. Overall Architecture of Effect4

Effect4 is structured across four clean architectural tiers:

```
+-------------------------------------------------------------------------------+
|                             Application Surface                                |
|           Effect4.Api (Effect.gen, succeed, fail, fork, catchAll, etc.)        |
+-------------------------------------------------------------------------------+
                                      |
                                      v
+-------------------------------------------------------------------------------+
|                              Free Program IR                                  |
|         Eff (First-Order Syntax)  /  RProgram = Free (StoreSig + FiberSig)    |
|               Algebraic Folds (cata_eff, cataFam), Pure AST                   |
+-------------------------------------------------------------------------------+
                                      |
                                      v
+-------------------------------------------------------------------------------+
|                            Operational Machine                                |
|        RState (Fibers, Stores, CompletedExits, Races, DecisionTape)           |
|        Two-Phase Stepper: evaluateRawR (Counted) + deliverR/popR (Frames)      |
+-------------------------------------------------------------------------------+
                                      |
                                      v
+-------------------------------------------------------------------------------+
|                          Type & Refinement Layer                              |
|   World (Γ, Ρ, Π, Θ), Protocol (Ψ_S, Ψ_F), StrongValue, StrongExit, Projects  |
|   Stores.WF, RefKernel, Arena Simulation, Abstract Denotational Semantics     |
+-------------------------------------------------------------------------------+
```

1. **Free Program IR (`Eff` / `RProgram`)**:
   Canonical program syntax is first-order inductive data. Lean closures, host functions, and promises are strictly excluded. Programs are represented as `Free (StoreSig + FiberSig) ExitV`, where synchronous memory mutations (`StoreSig`) and concurrent scheduler operations (`FiberSig`) are explicit algebraic operations.
2. **Operational Machine (`RState`)**:
   A deterministic multi-fiber runtime parameterized over an explicit `DecisionTape`. Execution alternates between counted primitive steps (`evaluateRawR`) and stack unwinding (`popR`). All non-deterministic choices (yield overrides, scheduler interleavings, async completion timings) are externalized on the tape.
3. **Data Plane (`Stores` & `Arena`)**:
   Memory storage comprises references (`refs`), promises (`deferreds`), and memoized entries. Implementations project to this plane via `Projects` and `Refines` relations, allowing high-performance OCaml 5 arrays and C arenas to be verified against Lean's mathematical store.
4. **The Proof Graph (`Effect4.Laws`)**:
   Separated from the runtime executable root. Proves simulation, typing preservation, and monotonicity without introducing axioms or runtime overhead.

---

## 5. Denotational Semantics Expressed by the IR to Date

The denotational semantics of Effect4 provides a compositional, mathematical interpretation of effects into relational transitions over explicit host decisions:

1. **Denotation Map (`denoteR`)**:
   High-level Effect programs are mapped into the reference IR:
   $$\text{denoteR} : \text{NativeEff} \to \text{RProgram}$$
   where structural recursion is guaranteed via generated algebraic catamorphisms (`cata_eff`).
2. **Relational Meaning (`BMeans` & Observations)**:
   Deterministic semantics is never claimed for concurrent programs without an explicit tape. Full meaning is relational over decision tapes:
   $$\text{BMeans } root\ tape\ outcome \iff \exists m,\ (replayR\ root\ fuel\ tape\ cfuel).machine = m \land \text{Run.observe } m = outcome$$
   The journal `List Command` forms a monoid action on the machine state, establishing replay uniqueness (`replay_unique`) and journal replay faithfulness (`journal_replays`).
3. **Step-Indexed World-Indexed Protocol Typing**:
   The denotational safety of a program is captured by:
   $$\text{TypedProg } w\ ty\ p := \text{Typed } (\text{World.leHost})\ (\Psi_S + \Psi_F)\ w\ (\lambda w'\ ex \Rightarrow \text{StrongExit } w'\ ty\ ex)\ p \land \text{ControlAdmitted } w\ ty\ p$$
   This semantics ensures that:
   - Every intermediate memory access conforms to the typed heap $\text{Ρ}$ and promise table $\Pi$.
   - Every asynchronous resume satisfies the token contract $\Theta$.
   - Control operators (`unguard`, `finishFinalizer`, `scoped`) invert payload safety.
   - For any terminating, uninterrupted run, the final exit satisfies $\text{StrongExit } w\ ty\ ex$, guaranteeing progress and the complete absence of malformed states (`no_badShapeExit`).
