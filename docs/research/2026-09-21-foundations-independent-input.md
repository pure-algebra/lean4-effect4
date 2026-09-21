> Retained owner-supplied probe input. The strategic scope is approved; proposed runtime
> corrections remain unratified. See the independent plan and implementation receipt.
> Attachment SHA-256: `f33cd2225965c1a75e6023b2f73c2efdc4840dc382d206374a169c3262ebb99f`.

### Strategic Recommendation: Land Independent Foundations, Hold Dependent Contracts

You should **land Slice 4’s independent protocol and storage foundations** (`D12`, `C2`, `Candidates C3/C4`) in an isolated commit, while **holding the dependent residual and stack contracts** (`FrameAccepts.resume`, `TypedProg`, `popR_typed`).

#### Why this follows repository rules:
1. **Decoupling (`AGENTS.md`)**:
   - `D12` (Certificate-indexed protocols in [`Laws/Effects/Protocol.lean`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Effects/Protocol.lean)), `C2` (indexed heterogeneous heap preservation in [`Laws/Machine/RefKernel.lean`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Machine/RefKernel.lean)), and `C3/C4` (representation composition in [`Laws/Machine/Refinement.lean`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Machine/Refinement.lean)) do not mention `ScopeFrame`, `popR`, `deliverR`, or fiber interruption.
   - Holding verified algebraic foundations hostage to an unresolved scheduler edge case stalls the representation track unnecessarily.
2. **Strict Stop on Refuted Contracts**:
   - As required by dispatch §2 and the brief, the dependent scheduler slice must stop because checked counterexamples (`E4-SCHED-CE-006`, `E4-SCHED-CE-007`, `E4-TYPED-CE-003`) refute the proposed contract. Landing the independent lemmas keeps the ledger clean without ratifying a false scheduler theorem.

---

### Adversarial Review of the Counterexamples

The counterexamples in [`InterruptDelivery.lean`](file:///private/tmp/effect4-foundations-slices/Test/Counterexamples/Machine/Semantics/InterruptDelivery.lean) and [`StrongExitDefect.lean`](file:///private/tmp/effect4-foundations-slices/Test/Counterexamples/Machine/Semantics/StrongExitDefect.lean) are valid, exact, and expose the underlying operational mechanics:

| Counterexample | Mechanism Tested | Why the Draft Proposal Broke |
| :--- | :--- | :--- |
| **`E4-SCHED-CE-006`** | Mid-walk unmasking: `[.restoreMask true, .resume .onFailure recovery]` with `interruptible = false` and `interruptedCause = some ...` | On entry, `frame.interruptible = false`, so entry-time correlation held vacuously. But `popR` pops `.restoreMask true`, setting `interruptible := true`. The subsequent catch handler is skipped, popping the raw `Nat` failure into an outer context expecting `never`. |
| **`E4-SCHED-CE-007`** | Failing exit arrival with `deferredInterrupt = true` | [`EvaluateR.lean:128`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/EvaluateR.lean#L128) checks `deferredInterrupt` **only on `.success _`**. On `.failure _`, it clears `deferredInterrupt` without intercepting, then calls `popR`, which skips the catch handler and terminates with the raw failure. |
| **`E4-TYPED-CE-003`** | Defect admission in `StrongExit` | `badShapeExit` carries `Reason.die Defect.badName`. In [`ErrorImage.lean:37`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Program/ErrorImage.lean#L37), `reasonAdmits` accepts `.die` at *every* type `ty`. Strengthening `Reason.fail` checks cannot exclude `Die`. |

---

### Root Causes in the Runtime Engine & Concrete Improvements

#### 1. The Asymmetry in `deliverR` (Fixing `E4-SCHED-CE-007`)

* **The Issue:**
  In [`EvaluateR.lean:128`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/EvaluateR.lean#L128):
  ```lean
  let deferred := match ex with | .success _ => f.frame.deferredInterrupt | _ => false
  ```
  `EvaluateR.lean` only intercepts deferred interrupts if the incoming exit is a `.success`.
* **Vendor rc.112 Reality:**
  In [`vendor/effect-4.0.0-rc.112/src/internal/effect.ts:684–686`](file:///Users/pooks/Dev/lean4-effect4/vendor/effect-4.0.0-rc.112/src/internal/effect.ts#L684-L686):
  ```typescript
  if (this._deferredInterrupt) {
    this._deferredInterrupt = false
    return deferredInterruptCont // returns failCause(fiber._interruptedCause!) for both contA and contE!
  }
  ```
  `getCont` intercepts `_deferredInterrupt` on **both** success (`contA`) and failure (`contE`), replacing the current exit with `_interruptedCause!`.
* **Concrete Improvement:**
  In `deliverR`, remove the success-only restriction:
  ```lean
  def deliverR (interp : RInterp) (m : RState) (f : RFiber) (yielding : Bool) (ex : ExitV) : RIter :=
    let deferred := f.frame.deferredInterrupt && f.frame.interruptible
    if deferred then
      ⟨m, { f with frame := { f.frame with
        current := .pure (.failure f.frame.pendingCause)
        deferredInterrupt := false } }, yielding, .continue_, []⟩
    else
      let (frame, done) := popR interp ex f.frame.stack { f.frame with deferredInterrupt := false }
      ⟨m, { f with frame }, yielding, outcomeOfWalk done, []⟩
  ```
  This guarantees that whenever `deferredInterrupt && interruptible` holds, `popR` is never invoked on an unhandled typed failure. This resolves `E4-SCHED-CE-007`.

---

#### 2. The Mid-Walk Unmasking Trap (Fixing `E4-SCHED-CE-006`)

Fixing `deliverR` does not resolve `E4-SCHED-CE-006`, because in `E4-SCHED-CE-006`, `deferredInterrupt` was `false` (the interrupt arrived while the fiber was masked).

* **The Reality of Asynchronous Cancellation:**
  In Effect rc.112, when an interrupt arrives while masked, the fiber is allowed to finish its uninterruptible critical section. But the moment it unmasks (`.restoreMask true`), the pending interrupt activates: catch handlers are suppressed, and the computation aborts.
  Because the catch handler is suppressed, any failure produced inside the critical section **escapes uncaught**.
* **Why Static Error Types Cannot Bound Escaping Failures:**
  If an uninterruptible block fails with `Nat` inside a `catchAll` typed for `never`, unmasking causes the catch to be skipped. The fiber aborts with `Nat`.
  No static type system can prove that an escaping, suppressed failure conforms to `never`.
* **Concrete Improvement:**
  Formulate the typing of `popR` as a **two-phase outcome** reflecting the walk's dynamic mask horizon:

  1. **Dynamic Mask Tracking in `StackAccepts`**:
     Index `StackAccepts` by the dynamic interruptibility mask:
     $$\text{StackAccepts } TypedProg\ hooks\ w\ (tin, m_{in})\ (tout, m_{out})\ stack$$
     - `.restoreMask flag` transitions mask state from $m$ to $flag$.
     - `.resume kind next` requires $m = \text{false}$ (masked) or $kind.\text{hasExitArm } ex = \text{false}$ to guarantee standard propagation.
  2. **Disjunctive Abort Outcome in `popR_typed`**:
     The theorem must account for whether the walk ever reached an unmasked state with a pending interrupt:
     $$\forall w\ interp\ tin\ tout\ ex\ stack\ frame,$$
     $$\text{StackAccepts } \dots \to \text{StrongExit } w\ tin\ ex \to \text{InterruptProvenance } frame \to$$
     $$\text{match popR interp ex stack frame with}$$
     $$\mid (frame', \text{none}) \Rightarrow \exists middle,\ \text{TypedProg } w\ middle\ frame'.current \land \text{StackAccepts } \dots$$
     $$\mid (\_, \text{some } ex') \Rightarrow \text{StrongExit } w\ tout\ ex' \lor \text{WalkPreempted } frame\ stack$$
     where $\text{WalkPreempted } frame\ stack$ holds if:
     $$frame.\text{interruptedCause.isSome} = \text{true} \land (frame.\text{interruptible} = \text{true} \lor \exists s \in stack,\ s = \text{.restoreMask true} \lor s = \text{.finalizerMask true})$$
  This captures the operational fact: **an unmasked frame with a pending interrupt aborts the fiber, bypassing remaining error handlers.**

---

#### 3. Defect Safety & `badShapeExit` (Fixing `E4-TYPED-CE-003`)

* **The Reality of Defects:**
  In [`ErrorImage.lean:37`](file:///Users/pooks/Dev/lean4-effect4/src/Effect4/Program/ErrorImage.lean#L37), defects (`Reason.die`) are admitted at every type `ty`, because defects represent unchecked panics.
* **Concrete Improvement:**
  Accept the amendment's correction:
  - Keep `StrongExit` as the exit-typing judgment for values, typed errors, and admitted defects.
  - Formulate the absence of `badShapeExit` as a **Semantic Progress/Safety Theorem**, not a clause of `StrongExit`:
    $$\forall w\ ty\ p,\ \text{TypedProg } w\ ty\ p \implies \forall m\ fuel\ cfuel,\ \text{Run.observe } (replayR\ p\ fuel\ tape\ cfuel).machine \ne \text{badShapeExit}$$
  This separates typing (which allows arbitrary panics/defects) from program admission (which proves that well-typed programs never step into malformed markers like unadmitted `scopeExit` or `frontier`).

---

### Suggested Action Plan

1. **Slice 4 (Foundations)**:
   - Land `Protocol.lean` (D12 certificate protocols and compatibility).
   - Land `RefKernel.lean` (Candidate C2 heterogeneous indexed heap preservation).
   - Land `Refinement.lean` (Candidates C3 and C4 representation composition).
   - Commit as: `feat(laws): land D12 protocol certificates and C2-C4 representation foundations`.
2. **Slice 4 (Scheduler Contract - Held)**:
   - Keep `FrameAccepts.resume`, `TypedProg`, and `popR_typed` open under `#proof_wanted` until the dynamic mask tracking in `StackAccepts` and the `deliverR` failure-interception fix are drafted and tested against `E4-SCHED-CE-006` and `E4-SCHED-CE-007`.
