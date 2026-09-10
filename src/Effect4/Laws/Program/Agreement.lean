import Effect4.Laws.Program.Denote

/-!
# Program.Agreement — the compile agrees with the denotation, one fiber at a time

Packet: `Test/contracts/program-denotation.contract.md`; plan
`docs/research/2026-09-05-slice-1-compile-ground.md` §9. This module is the frame half of
the packet's theorem: a compiled program of the plain fragment, run by the frame machine
over the stores from *any* outer stack `K`, reaches the exit and the stores its meaning
predicts, and continues from there exactly as the run from that exit would. The machine's
command loop over one fiber is related to this local run in `Program/Agreement/Machine.lean`.

`Plain` is `Denote.Straight`, including `onExit`. Its finalizer runs under a mask,
then the restoring frame returns to the body's interruption mode.

The local step is the machine's `evaluatePrim` on a fiber of the fragment: a `sync` thunk
answers through the store (`Fibers.lean:831-843`), and every other plain primitive is the
frame machine's `step` (`Fibers.lean:848`, `stepFrame`). Names get their meaning from
`interpAt root []`: the running one-fiber machine has no completed fiber. Lazy callbacks
refresh their captured point to that empty view; eager bodies retain their point.
-/

set_option autoImplicit false

namespace Effect4.Program.Agreement

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Denote

/-! ## The fragment -/

/-- The straight-line fragment, spelled here so its closure lemmas and measures live with the
run; `Plain_eq_Straight` says it is `Denote.Straight`. -/
def Plain : NativeEff → Bool
  | .succeed _ => true
  | .fail _ => true
  | .failCause _ => true
  | .yieldError _ => true
  | .sync _ => true
  | .suspend b => Plain b
  | .perform op _ =>
    match (NativeOp.row op).kind with
    | .sync => true
    | _ => false
  | .bind a b => Plain a && Plain b
  | .branch _ a b => Plain a && Plain b
  | .exit b => Plain b
  | .catchCause b h => Plain b && Plain h
  | .matchCause b v c => Plain b && Plain v && Plain c
  | .onExit b f => Plain b && Plain f
  | _ => false

theorem Plain_eq_Straight : ∀ e : NativeEff, Plain e = Straight e
  | .suspend b => by simp only [Plain, Straight, Plain_eq_Straight b]
  | .bind a b => by simp only [Plain, Straight, Plain_eq_Straight a, Plain_eq_Straight b]
  | .branch _ a b => by simp only [Plain, Straight, Plain_eq_Straight a, Plain_eq_Straight b]
  | .exit b => by simp only [Plain, Straight, Plain_eq_Straight b]
  | .catchCause b h => by simp only [Plain, Straight, Plain_eq_Straight b, Plain_eq_Straight h]
  | .matchCause b v c => by
    simp only [Plain, Straight, Plain_eq_Straight b, Plain_eq_Straight v, Plain_eq_Straight c]
  | .onExit b f => by simp only [Plain, Straight, Plain_eq_Straight b, Plain_eq_Straight f]
  | .succeed _ | .fail _ | .failCause _ | .yieldError _ | .sync _ | .perform _ _ | .gen _
  | .uninterruptible _ | .interruptible _ | .whileLoop _ _ _ _ | .yieldNow _ | .callback _ _
  | .awaitFiber _ _ | .withFiber _ | .scoped _ | .acquireRelease _ _ | .choose _ _ _
  | .provideLayer _ _ _ | .service _ | .provideService _ _ _ | .catchIf _ _ _ => rfl

theorem Plain.suspend {b : NativeEff} (h : Plain (.suspend b) = true) : Plain b = true := h

theorem Plain.onExit {b f : NativeEff} (h : Plain (.onExit b f) = true) :
    Plain b = true ∧ Plain f = true := by
  simpa [Plain, Bool.and_eq_true] using h

theorem Plain.bind {a b : NativeEff} (h : Plain (.bind a b) = true) :
    Plain a = true ∧ Plain b = true := by
  simpa [Plain, Bool.and_eq_true] using h

theorem Plain.branch {t : Term} {a b : NativeEff} (h : Plain (.branch t a b) = true) :
    Plain a = true ∧ Plain b = true := by
  simpa [Plain, Bool.and_eq_true] using h

theorem Plain.exit {b : NativeEff} (h : Plain (.exit b) = true) : Plain b = true := h

theorem Plain.catchCause {b h' : NativeEff} (h : Plain (.catchCause b h') = true) :
    Plain b = true ∧ Plain h' = true := by
  simpa [Plain, Bool.and_eq_true] using h

theorem Plain.matchCause {b v c : NativeEff} (h : Plain (.matchCause b v c) = true) :
    Plain b = true ∧ Plain v = true ∧ Plain c = true := by
  simpa [Plain, Bool.and_eq_true, and_assoc] using h

theorem Plain.perform_sync {op : NativeOp} {r : Term} (h : Plain (.perform op r) = true) :
    (NativeOp.row op).kind = .sync := by
  unfold Plain at h
  revert h
  cases (NativeOp.row op).kind <;> simp

theorem Plain.not_gen {e : NativeEff} (h : Plain e = true) : ∀ ss, e ≠ .gen ss := by
  intro ss heq
  subst heq
  simp [Plain] at h

theorem Plain.not_whileLoop {e : NativeEff} (h : Plain e = true) :
    ∀ i t s b, e ≠ .whileLoop i t s b := by
  intro i t s b heq
  subst heq
  simp [Plain] at h

theorem Plain.not_provideLayer {e : NativeEff} (h : Plain e = true) :
    ∀ l i b, e ≠ .provideLayer l i b := by
  intro l i b heq
  subst heq
  simp [Plain] at h

/-- The depth the compile's fuel must cover: every child costs one (`Compile.lean:113`). -/
def depth : NativeEff → Nat
  | .suspend b => depth b + 1
  | .bind a b => max (depth a) (depth b) + 1
  | .branch _ a b => max (depth a) (depth b) + 1
  | .exit b => depth b + 1
  | .catchCause b h => max (depth b) (depth h) + 1
  | .matchCause b v c => max (depth b) (max (depth v) (depth c)) + 1
  | .onExit b f => max (depth b) (depth f) + 1
  | _ => 1

/-- A bound on the local steps a plain program takes before it is its exit. -/
def steps : NativeEff → Nat
  | .yieldError _ => 1
  | .sync _ => 1
  | .perform _ _ => 1
  | .suspend b => steps b + 1
  | .bind a b => steps a + steps b + 2
  | .branch _ a b => steps a + steps b + 1
  | .exit b => steps b + 2
  | .catchCause b h => steps b + steps h + 2
  | .matchCause b v c => steps b + steps v + steps c + 2
  | .onExit b f => steps b + steps f + 5
  | _ => 0

theorem depth_pos (e : NativeEff) : 1 ≤ depth e := by
  cases e <;> simp [depth]

/-! ## The local step and the local run -/

abbrev NFiber := FrameFiber EffName EffThunk Val Err Defect FiberId Ann
abbrev NInterp := PrimInterp EffName EffThunk Val Err Defect FiberId Ann

/-- The local run uses the completed-exit view of a live one-fiber machine. -/
def primOf (root : NativeEff) : NInterp := (interpAt root []).toPrimInterp

/-- A fiber of the fragment: no cause recorded, no interrupt deferred, interruptible unless
it is running a finalizer under the `onExit` mask (`Frames.lean`, `ensure`). -/
def fiberOf (current : NCode) (stack : List NCode) (i : Bool := true) : NFiber :=
  ⟨current, stack, i, none, false⟩

/-- Where one local step leaves the fiber. -/
inductive LocalStep
  | running (fr : NFiber) (s : Stores)
  | finished (ex : ExitV) (s : Stores)

abbrev NPop := FramePop EffName EffThunk Val Err Defect FiberId Ann
abbrev NStep := FrameStep EffName EffThunk Val Err Defect FiberId Ann

/-- The frame machine's step as a local step: the stores pass through. -/
def ofFrameStep (st : NStep) (s : Stores) : LocalStep :=
  match st with
  | FrameStep.running fr' => .running fr' s
  | FrameStep.finished ex => .finished ex s

/-- The pop an exit makes: the value arm without skipping, the cause arm skipping the
interrupted (`Frames.lean`, `resumeValue`, `resumeCause`; `Fibers.lean`, `finalizerOr`). -/
def popOf (fr : NFiber) (ex : ExitV) : NPop :=
  match ex with
  | Exit.success _ => fr.getCont Effect4.Arm.contA false
  | Exit.failure _ => fr.getCont Effect4.Arm.contE true

/-- What `resumeValue`/`resumeCause` make of a pop: read from its answer and its fiber. -/
def resumeOf (root : NativeEff) (ex : ExitV) (pop : NPop) : NStep :=
  match pop.answer with
  | ContAnswer.empty => FrameStep.finished ex
  | ContAnswer.deferred cause => FrameStep.running { pop.fiber with current := Prim.failure cause }
  | ContAnswer.replacement next => FrameStep.running { pop.fiber with current := next }
  | ContAnswer.frame frame =>
    match (match ex with
           | Exit.success v => frame.armA (primOf root) v (some ex)
           | Exit.failure c => frame.armE (primOf root) c (some ex)) with
    | some (next, pushed) =>
      FrameStep.running { pop.fiber with current := next, stack := pushed ++ pop.fiber.stack }
    | none => FrameStep.finished ex

/-- What an exit does with its pop, as the machine's `finalizerOr` does it:
an `onExit` program finalizer runs under the mask through the shared `finalizerCode`.
The success frame restores the body exit; only a failed body adds the failure handler
(`internal/effect.ts:3800-3804,4019-4030`). Otherwise use the frame machine's answer. -/
def exitFrom (root : NativeEff) (ex : ExitV) (pop : NPop) (s : Stores) : LocalStep :=
  match pop.answer with
  | ContAnswer.frame (Prim.onExit _ fin _) =>
    match (interpAt root []).finalizerProgram fin ex with
    | some program =>
      .running { pop.fiber with
        current := finalizerCode (interpAt root []) ex program } s
    | none => ofFrameStep (resumeOf root ex pop) s
  | _ => ofFrameStep (resumeOf root ex pop) s

/-- An answering `onExit` always leaves a running local step, including the
static finalizer fallback. A locally finished step therefore cannot take the
native scoped-exit branch. -/
theorem exitFrom_finished_not_onExit (root : NativeEff) (ex : ExitV) (pop : NPop)
    (s : Stores) (finished : ExitV) (s' : Stores)
    (h : exitFrom root ex pop s = .finished finished s')
    (body : NCode) (fin : EffName) (flag : Bool) :
    pop.answer ≠ ContAnswer.frame (Prim.onExit body fin flag) := by
  intro hanswer
  cases hfin : (interpAt root []).finalizerProgram fin ex
  · cases ex <;>
      simp [exitFrom, hanswer, hfin, ofFrameStep, resumeOf, Prim.armA, Prim.armE] at h
  · simp [exitFrom, hanswer, hfin] at h

/-- One local step (`evaluatePrim` on a fiber of the fragment): a store `sync` answers
through `syncOpStep` with the machine's `Val.unit` fallback (`Fibers.lean:837-843`), a pure
`sync` answers the term's value (`Compile.lean:593`), an exit pops through `exitFrom`
(`Fibers.lean:845-848`), and everything else is the frame machine's `step`
(`Fibers.lean:849`). -/
def localStep (root : NativeEff) (fr : NFiber) (s : Stores) : LocalStep :=
  match fr.current with
  | Prim.sync (EffThunk.op o) =>
    match syncOpStep o s with
    | some (s', v) => .running { fr with current := Prim.success v } s'
    | none => .running { fr with current := Prim.success Val.unit } s
  | Prim.sync thunk => .running { fr with current := Prim.success (syncValueAt root thunk) } s
  | Prim.success v => exitFrom root (Exit.success v) (popOf fr (Exit.success v)) s
  | Prim.failure c => exitFrom root (Exit.failure c) (popOf fr (Exit.failure c)) s
  | _ => ofFrameStep (fr.step (primOf root)).1 s

/-- `exitFrom` reads a pop's answer and fiber only. -/
theorem exitFrom_ext (root : NativeEff) (ex : ExitV) {p₁ p₂ : NPop} (s : Stores)
    (h₁ : p₁.answer = p₂.answer) (h₂ : p₁.fiber = p₂.fiber) :
    exitFrom root ex p₁ s = exitFrom root ex p₂ s := by
  rcases p₁ with ⟨a₁, _, _, f₁⟩
  rcases p₂ with ⟨a₂, _, _, f₂⟩
  simp only at h₁ h₂
  subst h₁
  subst h₂
  rfl

/-- The stores pass through an exit's pop. -/
theorem exitFrom_running_stores {root : NativeEff} {ex : ExitV} {pop : NPop} {s s' : Stores}
    {fr' : NFiber} (h : exitFrom root ex pop s = .running fr' s') : s = s' := by
  unfold exitFrom at h
  split at h
  · split at h
    · cases h; rfl
    · unfold ofFrameStep at h; split at h <;> cases h; rfl
  · unfold ofFrameStep at h; split at h <;> cases h; rfl

theorem exitFrom_finished_stores {root : NativeEff} {ex ex' : ExitV} {pop : NPop} {s s' : Stores}
    (h : exitFrom root ex pop s = .finished ex' s') : s = s' := by
  unfold exitFrom at h
  split at h
  · split at h
    · cases h
    · unfold ofFrameStep at h; split at h <;> cases h; rfl
  · unfold ofFrameStep at h; split at h <;> cases h; rfl

/-- The local run: `n` steps at most, the exit and the stores when the fiber finishes. -/
def localRun (root : NativeEff) : Nat → NFiber → Stores → Option (ExitV × Stores)
  | 0, _, _ => none
  | n + 1, fr, s =>
    match localStep root fr s with
    | .running fr' s' => localRun root n fr' s'
    | .finished ex s' => some (ex, s')

theorem localRun_zero (root : NativeEff) (fr : NFiber) (s : Stores) :
    localRun root 0 fr s = none := rfl

theorem localRun_running {root : NativeEff} {fr fr' : NFiber} {s s' : Stores}
    (h : localStep root fr s = .running fr' s') (n : Nat) :
    localRun root (n + 1) fr s = localRun root n fr' s' := by
  simp [localRun, h]

theorem localRun_finished {root : NativeEff} {fr : NFiber} {s s' : Stores} {ex : ExitV}
    (h : localStep root fr s = .finished ex s') (n : Nat) :
    localRun root (n + 1) fr s = some (ex, s') := by
  simp [localRun, h]

/-- Two fibers with the same next step have the same runs. -/
theorem localRun_congr {root : NativeEff} {fr fr' : NFiber}
    (h : ∀ s, localStep root fr s = localStep root fr' s) :
    ∀ n s, localRun root n fr s = localRun root n fr' s
  | 0, _ => rfl
  | n + 1, s => by simp only [localRun, h s]

theorem localRun_mono {root : NativeEff} :
    ∀ {n : Nat} {fr : NFiber} {s : Stores} {r : ExitV × Stores},
      localRun root n fr s = some r → ∀ k, localRun root (n + k) fr s = some r
  | 0, _, _, _, h, _ => by simp [localRun] at h
  | n + 1, fr, s, r, h, k => by
    rw [Nat.add_right_comm]
    rcases hs : localStep root fr s with ⟨fr', s'⟩ | ⟨ex, s'⟩
    · rw [localRun_running hs] at h
      rw [localRun_running hs]
      exact localRun_mono h k
    · rw [localRun_finished hs] at h
      rw [localRun_finished hs]
      exact h

/-! ## The frame steps of the fragment, as local steps -/

section frames

variable (root : NativeEff)

theorem step_push_onSuccess (body : NCode) (n : EffName) (K : List NCode) (i : Bool)
    (s : Stores) :
    localStep root (fiberOf (Prim.onSuccess body n) K i) s =
      .running (fiberOf body (Prim.onSuccess body n :: K) i) s := rfl

theorem step_push_onFailure (body : NCode) (n : EffName) (K : List NCode) (i : Bool)
    (s : Stores) :
    localStep root (fiberOf (Prim.onFailure body n) K i) s =
      .running (fiberOf body (Prim.onFailure body n :: K) i) s := rfl

theorem step_push_onSuccessAndFailure (body : NCode) (n₁ n₂ : EffName) (K : List NCode)
    (i : Bool) (s : Stores) :
    localStep root (fiberOf (Prim.onSuccessAndFailure body n₁ n₂) K i) s =
      .running (fiberOf body (Prim.onSuccessAndFailure body n₁ n₂ :: K) i) s := rfl

theorem step_push_exitFrame (body : NCode) (K : List NCode) (i : Bool) (s : Stores) :
    localStep root (fiberOf (Prim.exitFrame body) K i) s =
      .running (fiberOf body (Prim.exitFrame body :: K) i) s := rfl

theorem step_push_onExit (body : NCode) (n : EffName) (flag : Bool) (K : List NCode) (i : Bool)
    (s : Stores) :
    localStep root (fiberOf (Prim.onExit body n flag) K i) s =
      .running (fiberOf body (Prim.onExit body n flag :: K) i) s := rfl

theorem step_yieldableError (e : Err) (K : List NCode) (i : Bool) (s : Stores) :
    localStep root (fiberOf (Prim.yieldableError e) K i) s =
      .running (fiberOf (Prim.failure (Cause.fail e)) K i) s := rfl

theorem step_suspend (thunk : EffThunk) (K : List NCode) (i : Bool) (s : Stores) :
    localStep root (fiberOf (Prim.suspend thunk) K i) s =
      .running (fiberOf ((interpAt root []).suspendBody thunk) K i) s := rfl

theorem step_sync_pure (p : Point) (K : List NCode) (i : Bool) (s : Stores) :
    localStep root (fiberOf (Prim.sync (EffThunk.pure p)) K i) s =
      .running (fiberOf (Prim.success (syncValueAt root (EffThunk.pure p))) K i) s := rfl

theorem step_sync_op (o : SyncOp) (K : List NCode) (i : Bool) (s : Stores) :
    localStep root (fiberOf (Prim.sync (EffThunk.op o)) K i) s =
      (match syncOpStep o s with
       | some (s', v) => .running (fiberOf (Prim.success v) K i) s'
       | none => .running (fiberOf (Prim.success Val.unit) K i) s) := by
  simp only [localStep, fiberOf]

/-- An exit on the empty stack finishes the fiber with itself. -/
theorem step_exit_empty (ex : ExitV) (i : Bool) (s : Stores) :
    localStep root (fiberOf (Prim.ofExit ex) [] i) s = .finished ex s := by
  cases ex <;> cases i <;> rfl

/-- A value meets its `OnSuccess` frame: the continuation at the value. -/
theorem step_success_onSuccess (v : Val) (body : NCode) (n : EffName) (K : List NCode)
    (i : Bool) (s : Stores) :
    localStep root (fiberOf (Prim.success v) (Prim.onSuccess body n :: K) i) s =
      .running (fiberOf ((interpAt root []).contA n v) K i) s := by
  cases i <;> rfl

/-- A value meets its `OnSuccessAndFailure` frame: the value arm. -/
theorem step_success_onSuccessAndFailure (v : Val) (body : NCode) (n₁ n₂ : EffName)
    (K : List NCode) (i : Bool) (s : Stores) :
    localStep root (fiberOf (Prim.success v) (Prim.onSuccessAndFailure body n₁ n₂ :: K) i) s =
      .running (fiberOf ((interpAt root []).contA n₁ v) K i) s := by
  cases i <;> rfl

/-- A value meets the `Exit` frame: the reified success. -/
theorem step_success_exitFrame (v : Val) (body : NCode) (K : List NCode) (i : Bool)
    (s : Stores) :
    localStep root (fiberOf (Prim.success v) (Prim.exitFrame body :: K) i) s =
      .running (fiberOf (Prim.success (reifyExitVal (Exit.success v))) K i) s := by
  cases i <;> rfl

/-- A cause meets its `OnFailure` frame: the handler at the cause. -/
theorem step_failure_onFailure (c : CauseV) (body : NCode) (n : EffName) (K : List NCode)
    (i : Bool) (s : Stores) :
    localStep root (fiberOf (Prim.failure c) (Prim.onFailure body n :: K) i) s =
      .running (fiberOf ((interpAt root []).contE n c) K i) s := by
  cases i <;> rfl

/-- A cause meets its `OnSuccessAndFailure` frame: the cause arm. -/
theorem step_failure_onSuccessAndFailure (c : CauseV) (body : NCode) (n₁ n₂ : EffName)
    (K : List NCode) (i : Bool) (s : Stores) :
    localStep root (fiberOf (Prim.failure c) (Prim.onSuccessAndFailure body n₁ n₂ :: K) i) s =
      .running (fiberOf ((interpAt root []).contE n₂ c) K i) s := by
  cases i <;> rfl

/-- A cause meets the `Exit` frame: the reified failure. -/
theorem step_failure_exitFrame (c : CauseV) (body : NCode) (K : List NCode) (i : Bool)
    (s : Stores) :
    localStep root (fiberOf (Prim.failure c) (Prim.exitFrame body :: K) i) s =
      .running (fiberOf (Prim.success (reifyExitVal (Exit.failure c))) K i) s := by
  cases i <;> rfl

/-- The stack under a finalizer: the restoring frame when the fiber was interruptible,
nothing when it was already masked (`Frames.lean`, `ensure` on `onExit`). -/
def maskStack : Bool → List NCode → List NCode
  | true, K => Prim.setInterruptible true :: K
  | false, K => K

/-- An exit meets an `onExit` program finalizer: the frame is popped, the mask is set,
and the shared exit-dependent wrapper runs (`internal/effect.ts:4019-4030`). -/
theorem step_ofExit_onExit (ex : ExitV) (body : NCode) (p : Point) (K : List NCode) (i : Bool)
    (s : Stores) :
    localStep root (fiberOf (Prim.ofExit ex) (Prim.onExit body (EffName.fin p) false :: K) i) s =
      .running (fiberOf (finalizerCode (interpAt root []) ex
          (resolve root ({ p with completed := [] }.childWith 1 (reifyExitVal ex))))
        (maskStack i K) false) s := by
  cases ex <;> cases i <;> rfl

/-- The finalizer's exit meets its frame: the body's exit restored on success, merged on
failure (`Compile.lean:555`, `:577`). -/
theorem step_ofExit_finalizer (ex fex : ExitV) (body : NCode) (K : List NCode) (i : Bool)
    (s : Stores) :
    localStep root (fiberOf (Prim.ofExit fex)
        (Prim.onSuccessAndFailure body (EffName.restore ex) (EffName.merge ex) :: K) i) s =
      .running (fiberOf (Prim.ofExit (Exit.restoreAfterFinalizer ex (finVoid fex))) K i) s := by
  cases fex <;> cases ex <;> cases i <;> rfl

/-- The pop through a frame that does not answer the demand and runs no hook is the pop of
the frames below it, up to what it records. -/
theorem popFrom_pass (demand : Effect4.Arm) (skip : Bool) (frame : NCode) (K : List NCode)
    (cur : NCode) (i : Bool) (hno : frame.hasArm demand = false)
    (hall : frame.hasArm Effect4.Arm.contAll = false) :
    (FrameFiber.popFrom demand skip (frame :: K) (fiberOf cur [] i)).answer =
        (FrameFiber.popFrom demand skip K (fiberOf cur [] i)).answer ∧
      (FrameFiber.popFrom demand skip (frame :: K) (fiberOf cur [] i)).fiber =
        (FrameFiber.popFrom demand skip K (fiberOf cur [] i)).fiber := by
  have he := Prim.ensure_of_no_contAll frame (fiberOf cur [] i) hall
  have hnone : frame.answerOf demand (frame.ensure (fiberOf cur [] i)).snd = none := by
    rw [he]; exact Prim.answerOf_missing frame demand hno
  have hcont := FrameFiber.popFrom_pass_no_push demand skip frame K (fiberOf cur [] i) rfl
    (by rw [he])
  rw [he] at hcont
  exact ⟨by rw [FrameFiber.popFrom_continue_answer demand skip frame K _ (Or.inl hnone), hcont],
    by rw [FrameFiber.popFrom_continue_fiber demand skip frame K _ (Or.inl hnone), hcont]⟩

/-- The pop through the restoring frame a mask left: the fiber is interruptible again, and
the pop is the pop of the frames below (`Frames.lean`, `ensure` on `setInterruptible`; the
frame declares `contAll` only, so no value or cause demand stops at it). -/
theorem popFrom_pass_setInterruptible (demand : Effect4.Arm) (skip : Bool) (K : List NCode)
    (cur : NCode) (i : Bool) (hno : (Prim.setInterruptible true : NCode).hasArm demand = false) :
    (FrameFiber.popFrom demand skip (Prim.setInterruptible true :: K) (fiberOf cur [] i)).answer =
        (FrameFiber.popFrom demand skip K (fiberOf cur [] true)).answer ∧
      (FrameFiber.popFrom demand skip (Prim.setInterruptible true :: K) (fiberOf cur [] i)).fiber =
        (FrameFiber.popFrom demand skip K (fiberOf cur [] true)).fiber := by
  have he : (Prim.setInterruptible true : NCode).ensure (fiberOf cur [] i) =
      (fiberOf cur [] true, none) := rfl
  have hnone : (Prim.setInterruptible true : NCode).answerOf demand
      ((Prim.setInterruptible true : NCode).ensure (fiberOf cur [] i)).snd = none := by
    rw [he]; exact Prim.answerOf_missing _ demand hno
  have hcont := FrameFiber.popFrom_pass_no_push demand skip (Prim.setInterruptible true) K
    (fiberOf cur [] i) rfl (by rw [he]; rfl)
  rw [he] at hcont
  exact ⟨by rw [FrameFiber.popFrom_continue_answer demand skip _ K _ (Or.inl hnone), hcont],
    by rw [FrameFiber.popFrom_continue_fiber demand skip _ K _ (Or.inl hnone), hcont]⟩

/-- A cause passes an `OnSuccess` frame: the step is the step without the frame. -/
theorem step_failure_pass_onSuccess (c : CauseV) (body : NCode) (n : EffName) (K : List NCode)
    (i : Bool) (s : Stores) :
    localStep root (fiberOf (Prim.failure c) (Prim.onSuccess body n :: K) i) s =
      localStep root (fiberOf (Prim.failure c) K i) s := by
  have hpop := popFrom_pass Effect4.Arm.contE true (Prim.onSuccess body n) K (Prim.failure c) i
    rfl rfl
  exact exitFrom_ext root _ s hpop.1 hpop.2

/-- A value passes an `OnFailure` frame: the step is the step without the frame. -/
theorem step_success_pass_onFailure (v : Val) (body : NCode) (n : EffName) (K : List NCode)
    (i : Bool) (s : Stores) :
    localStep root (fiberOf (Prim.success v) (Prim.onFailure body n :: K) i) s =
      localStep root (fiberOf (Prim.success v) K i) s := by
  have hpop := popFrom_pass Effect4.Arm.contA false (Prim.onFailure body n) K (Prim.success v) i
    rfl rfl
  exact exitFrom_ext root _ s hpop.1 hpop.2

/-- A value passes the restoring frame a mask left: the fiber is interruptible again. -/
theorem step_success_pass_setInterruptible (v : Val) (K : List NCode) (i : Bool) (s : Stores) :
    localStep root (fiberOf (Prim.success v) (Prim.setInterruptible true :: K) i) s =
      localStep root (fiberOf (Prim.success v) K true) s := by
  have hpop := popFrom_pass_setInterruptible Effect4.Arm.contA false K (Prim.success v) i rfl
  exact exitFrom_ext root _ s hpop.1 hpop.2

/-- A cause passes the restoring frame a mask left: the fiber is interruptible again. -/
theorem step_failure_pass_setInterruptible (c : CauseV) (K : List NCode) (i : Bool)
    (s : Stores) :
    localStep root (fiberOf (Prim.failure c) (Prim.setInterruptible true :: K) i) s =
      localStep root (fiberOf (Prim.failure c) K true) s := by
  have hpop := popFrom_pass_setInterruptible Effect4.Arm.contE true K (Prim.failure c) i rfl
  exact exitFrom_ext root _ s hpop.1 hpop.2

/-- Either exit passes the restoring frame. -/
theorem step_ofExit_pass_setInterruptible (ex : ExitV) (K : List NCode) (i : Bool)
    (s : Stores) :
    localStep root (fiberOf (Prim.ofExit ex) (Prim.setInterruptible true :: K) i) s =
      localStep root (fiberOf (Prim.ofExit ex) K true) s := by
  cases ex
  · exact step_success_pass_setInterruptible root _ K i s
  · exact step_failure_pass_setInterruptible root _ K i s

end frames

/-! ## Addresses -/

theorem Node.at_append (n : Node NativeOp) : ∀ (path : List Nat) (i : Nat),
    Node.at_ n (path ++ [i]) = (Node.at_ n path).bind fun m => m.child i
  | [], _ => by simp [Node.at_]
  | j :: rest, i => by
    simp only [List.cons_append, Node.at_]
    rcases n.child j with _ | m
    · rfl
    · exact Node.at_append m rest i

theorem at_child {root : NativeEff} {p : Point} {e : NativeEff}
    (h : Node.at_ (Node.eff root) p.path = some (Node.eff e)) (i : Nat) :
    Node.at_ (Node.eff root) (p.child i).path = (Node.eff e).child i := by
  simp only [Point.child, Node.at_append, h, Option.bind]

theorem at_childWith {root : NativeEff} {p : Point} {e : NativeEff}
    (h : Node.at_ (Node.eff root) p.path = some (Node.eff e)) (i : Nat) (v : Val) :
    Node.at_ (Node.eff root) (p.childWith i v).path = (Node.eff e).child i := by
  simp only [Point.childWith, Node.at_append, h, Option.bind]

theorem resolve_of_at {root : NativeEff} {q : Point} {e : NativeEff}
    (h : Node.at_ (Node.eff root) q.path = some (Node.eff e)) :
    resolve root q = compileEff e q := by
  simp [resolve, h]

/-! ## The compile, one arm at a time, at positive fuel -/

section compile

variable {p : Point} {k : Nat}

theorem compileEff_succeed (v : Term) (hf : p.fuel = k + 1) :
    compileEff (.succeed v) p =
      (match evalTerm p.env v with | some val => Prim.success val | none => badShape) := by
  simp [compileEff, hf]; rfl

theorem compileEff_fail (e : Term) (hf : p.fuel = k + 1) :
    compileEff (.fail e) p =
      (match evalTerm p.env e with
       | some val => Prim.failure (Cause.fail (errOf val)) | none => badShape) := by
  simp [compileEff, hf]; rfl

theorem compileEff_failCause (c : CauseTerm) (hf : p.fuel = k + 1) :
    compileEff (.failCause c) p =
      (match causeOf p.env c with | some cause => Prim.failure cause | none => badShape) := by
  simp [compileEff, hf]; rfl

theorem compileEff_yieldError (e : Term) (hf : p.fuel = k + 1) :
    compileEff (.yieldError e) p =
      (match evalTerm p.env e with
       | some val => Prim.yieldableError (errOf val) | none => badShape) := by
  simp [compileEff, hf]; rfl

theorem compileEff_sync (t : Term) (hf : p.fuel = k + 1) :
    compileEff (.sync t) p = Prim.sync (EffThunk.pure p) := by
  simp [compileEff, hf]

theorem compileEff_suspend (b : NativeEff) (hf : p.fuel = k + 1) :
    compileEff (.suspend b) p = Prim.suspend (EffThunk.body p) := by
  simp [compileEff, hf]

-- the join's three constructors
theorem compileEff_provideLayer (l : LayerTerm NativeOp) (i : Bool) (b : NativeEff)
    (hf : p.fuel = k + 1) :
    compileEff (.provideLayer l i b) p = Prim.suspend (EffThunk.body p) := by
  simp [compileEff, hf]

theorem compileEff_service (key : ServiceKey) (hf : p.fuel = k + 1) :
    compileEff (.service key) p =
      Prim.onSuccess (Prim.withFiber EffThunk.getCtx) (EffName.serviceLookup key) := by
  simp [compileEff, hf]

theorem compileEff_provideService (key : ServiceKey) (value : Term) (b : NativeEff)
    (hf : p.fuel = k + 1) :
    compileEff (.provideService key value b) p =
      (match evalTerm p.env value with
       | some v =>
         updateContextAt (Env.ContextUpdate.provideService key v) (Region.program (p.child 0))
       | none => badShape) := by
  simp [compileEff, hf]
  try rfl

theorem compileEff_perform_sync (op : NativeOp) (r : Term) (hf : p.fuel = k + 1)
    (hkind : (NativeOp.row op).kind = .sync) :
    compileEff (.perform op r) p =
      (match evalTerm p.env r with
       | some val =>
         match NativeOp.syncOpOf op val with
         | some operation => Prim.sync (EffThunk.op operation)
         | none => badShape
       | none => badShape) := by
  cases op with
  | scopeMake strategy => cases strategy <;> simp [compileEff, hf, NativeOp.row] <;> rfl
  | external _ => cases hkind
  | _ => simp_all [NativeOp.row, compileEff, hf] <;> rfl

theorem compileEff_bind (a b : NativeEff) (hf : p.fuel = k + 1) :
    compileEff (.bind a b) p =
      Prim.onSuccess (compileEff a (p.child 0)) (EffName.cont p) := by
  simp [compileEff, hf]

theorem compileEff_branch (t : Term) (a b : NativeEff) (hf : p.fuel = k + 1) :
    compileEff (.branch t a b) p = Prim.suspend (EffThunk.body p) := by
  simp [compileEff, hf]

/-- `Effect.exit` folds a body that is already an exit (`internal/effect.ts:3621-3622`,
P0 record row D1); otherwise it pushes the `exitFrame`. -/
theorem compileEff_exit (b : NativeEff) (hf : p.fuel = k + 1) :
    compileEff (.exit b) p =
      (match (compileEff b (p.child 0)).asExit? with
       | some exit => Prim.success (reifyExitVal exit)
       | none => Prim.exitFrame (compileEff b (p.child 0))) := by
  simp [compileEff, hf] <;> rfl

theorem compileEff_exit_fold (b : NativeEff) (hf : p.fuel = k + 1) {exit : ExitV}
    (h : (compileEff b (p.child 0)).asExit? = some exit) :
    compileEff (.exit b) p = Prim.success (reifyExitVal exit) := by
  rw [compileEff_exit b hf, h]

theorem compileEff_exit_frame (b : NativeEff) (hf : p.fuel = k + 1)
    (h : (compileEff b (p.child 0)).asExit? = none) :
    compileEff (.exit b) p = Prim.exitFrame (compileEff b (p.child 0)) := by
  rw [compileEff_exit b hf, h]

/-- At fuel zero every program is the frontier at its point. -/
theorem compileEff_at_zero (e : NativeEff) (hf : p.fuel = 0) : compileEff e p = frontier p := by
  unfold compileEff
  simp only [hf]

theorem compileEff_catchCause (b h : NativeEff) (hf : p.fuel = k + 1) :
    compileEff (.catchCause b h) p =
      Prim.onFailure (compileEff b (p.child 0)) (EffName.caught p) := by
  simp [compileEff, hf]

theorem compileEff_catchIf (test : Term) (b h : NativeEff) (hf : p.fuel = k + 1) :
    compileEff (.catchIf test b h) p =
      Prim.onFailure (compileEff b (p.child 0)) (EffName.caughtError p) := by
  simp [compileEff, hf]

theorem compileEff_matchCause (b v c : NativeEff) (hf : p.fuel = k + 1) :
    compileEff (.matchCause b v c) p =
      Prim.onSuccessAndFailure (compileEff b (p.child 0)) (EffName.onValue p)
        (EffName.onCause p) := by
  simp [compileEff, hf]

theorem compileEff_onExit (b f : NativeEff) (hf : p.fuel = k + 1) :
    compileEff (.onExit b f) p =
      Prim.onExit (compileEff b (p.child 0)) (EffName.fin p) false := by
  simp [compileEff, hf]

end compile

/-! ### The join's continuations, one equation per arm

The value-reading continuations are the named `*K` functions of `Compile.lean` by `rfl`; the
arms that match a handle have their handle equation and their wrong-shape equation, proved
the way `contAOf_acquireIn_other` is. -/

section joinConts

variable (root : NativeEff)

theorem contAOf_provideLayerWith_scope (p : Point) (scope : Nat) :
    Program.contAOf root (.provideLayerWith p) (Val.scopeHandle scope) =
      provideLayerWithK root p scope := rfl

theorem contAOf_provideLayerWith_other (p : Point) (v : Val) (hne : ∀ x, v ≠ Val.scopeHandle x) :
    Program.contAOf root (.provideLayerWith p) v = badShape := by
  unfold Program.contAOf
  revert hne
  split <;> intro hne <;> first
    | rfl
    | contradiction
    | exact absurd rfl (hne _)
    | (rename_i heq; exact absurd heq (hne _))
    | simp_all

theorem contAOf_provideLayerBody (p : Point) (v : Val) :
    Program.contAOf root (.provideLayerBody p) v = provideLayerBodyK root p v := rfl

theorem contAOf_updateThen (u : Env.ContextUpdate) (body : Region) (v : Val) :
    Program.contAOf root (.updateThen u body) v = updateThenK root u body v := rfl

theorem contAOf_bodyThen (body : Region) (previous : Ctx) (v : Val) :
    Program.contAOf root (.bodyThen body previous) v =
      Prim.onExit (regionCode root body) (.restoreCtx previous) false := rfl

theorem contAOf_buildWithScopeFromContext (q : Point) (scope : Nat) (v : Val) :
    Program.contAOf root (.buildWithScopeFromContext q scope) v = buildWithScopeK q scope v := rfl

theorem contAOf_withMemoMapThen_memoMap (q : Point) (scope : Nat) (id : MemoMapId) :
    Program.contAOf root (.withMemoMapThen q scope) (Val.memoMap id) =
      updateContextAt (Env.ContextUpdate.provideService Env.currentMemoMapKey (Val.memoMap id))
        (Region.buildAdding q id scope) := by
  cases id; rfl

theorem contAOf_withMemoMapThen_other (q : Point) (scope : Nat) (v : Val) (hne : ∀ x, v ≠ Val.memoMap x) :
    Program.contAOf root (.withMemoMapThen q scope) v = badShape := by
  unfold Program.contAOf
  revert hne
  split <;> intro hne <;> first
    | rfl
    | contradiction
    | exact absurd rfl (hne _)
    | (rename_i heq; exact absurd heq (hne _))
    | simp_all

theorem contAOf_addCurrentMemoMap (m : MemoMapId) (v : Val) :
    Program.contAOf root (.addCurrentMemoMap m) v = addCurrentMemoMapK m v := rfl

theorem contAOf_fromBuildThen_scope (q : Point) (m : MemoMapId) (child : Nat) :
    Program.contAOf root (.fromBuildThen q m) (Val.scopeHandle child) =
      Prim.onExit (innerLayerAt root q m child)
        (.store (Name.finalizerName (FinName.closeChildOnFailure child))) false := rfl

theorem contAOf_fromBuildThen_other (q : Point) (m : MemoMapId) (v : Val) (hne : ∀ x, v ≠ Val.scopeHandle x) :
    Program.contAOf root (.fromBuildThen q m) v = badShape := by
  unfold Program.contAOf
  revert hne
  split <;> intro hne <;> first
    | rfl
    | contradiction
    | exact absurd rfl (hne _)
    | (rename_i heq; exact absurd heq (hne _))
    | simp_all

theorem contAOf_memoize_hit (q : Point) (m : MemoMapId) (scope : Nat) (cell : DeferredKey)
    (owner : MemoMapId) :
    Program.contAOf root (.memoize q m scope) (.pair (Val.promise cell) (Val.memoMap owner)) =
      Prim.onSuccess (scopeAddAt scope (FinName.memoEntry q.path owner)) (.awaitPromise cell) := by
  cases cell; cases owner; rfl

theorem contAOf_memoize_unit (q : Point) (m : MemoMapId) (scope : Nat) :
    Program.contAOf root (.memoize q m scope) Val.unit =
      Prim.onSuccess (Prim.sync (EffThunk.op (SyncOp.memoBuild q.path m)))
        (.buildIntoLayerScope q m scope) := rfl

theorem contAOf_memoize_other (q : Point) (m : MemoMapId) (scope : Nat) (v : Val)
    (hhit : ∀ c o, v ≠ .pair (Val.promise c) (Val.memoMap o)) (hunit : v ≠ Val.unit) :
    Program.contAOf root (.memoize q m scope) v = badShape := by
  unfold Program.contAOf
  revert hhit hunit
  split <;> intro hhit hunit <;> first
    | rfl
    | contradiction
    | exact absurd rfl (hhit _ _)
    | exact absurd rfl hunit
    | (rename_i heq; exact absurd heq (hhit _ _))
    | (rename_i heq; exact absurd heq hunit)
    | simp_all

theorem contAOf_awaitPromise (cell : DeferredKey) (v : Val) :
    Program.contAOf root (.awaitPromise cell) v =
      Prim.async (.registerAwait cell) true (some (.cancelAwait cell)) := rfl

theorem contAOf_buildIntoLayerScope_scope (q : Point) (m : MemoMapId) (scope layerScope : Nat) :
    Program.contAOf root (.buildIntoLayerScope q m scope) (Val.scopeHandle layerScope) =
      Prim.onSuccess (scopeAddAt scope (FinName.memoEntry q.path m))
        (.thenBuildInto q m layerScope) := rfl

theorem contAOf_buildIntoLayerScope_other (q : Point) (m : MemoMapId) (scope : Nat) (v : Val) (hne : ∀ x, v ≠ Val.scopeHandle x) :
    Program.contAOf root (.buildIntoLayerScope q m scope) v = badShape := by
  unfold Program.contAOf
  revert hne
  split <;> intro hne <;> first
    | rfl
    | contradiction
    | exact absurd rfl (hne _)
    | (rename_i heq; exact absurd heq (hne _))
    | simp_all

theorem contAOf_thenBuildInto (q : Point) (m : MemoMapId) (layerScope : Nat) (v : Val) :
    Program.contAOf root (.thenBuildInto q m layerScope) v =
      Prim.onExit (constructionAt root q layerScope)
        (.store (Name.finalizerName (FinName.memoDone q.path m))) false := rfl

theorem contAOf_freshThen_memoMap (q : Point) (scope : Nat) (id : MemoMapId) :
    Program.contAOf root (.freshThen q scope) (Val.memoMap id) = resolveLayer root q id scope := by
  cases id; rfl

theorem contAOf_freshThen_other (q : Point) (scope : Nat) (v : Val) (hne : ∀ x, v ≠ Val.memoMap x) :
    Program.contAOf root (.freshThen q scope) v = badShape := by
  unfold Program.contAOf
  revert hne
  split <;> intro hne <;> first
    | rfl
    | contradiction
    | exact absurd rfl (hne _)
    | (rename_i heq; exact absurd heq (hne _))
    | simp_all

theorem contAOf_provideThen (q : Point) (m : MemoMapId) (scope : Nat) (mode : CombineMode)
    (v : Val) :
    Program.contAOf root (.provideThen q m scope mode) v = provideThenK q m scope mode v := rfl

theorem contAOf_combineWith (mode : CombineMode) (that : Env.Ctx) (v : Val) :
    Program.contAOf root (.combineWith mode that) v = combineWithK mode that v := rfl

theorem contAOf_mergeChildren_scope (q : Point) (m : MemoMapId) (parent : Nat) :
    Program.contAOf root (.mergeChildren q m) (Val.scopeHandle parent) =
      Prim.onSuccess
        (Prim.sync (EffThunk.op (SyncOp.scopeFork parent FinalizerStrategy.sequential)))
        (.mergeForkOne q 0 m parent []) := rfl

theorem contAOf_mergeChildren_other (q : Point) (m : MemoMapId) (v : Val) (hne : ∀ x, v ≠ Val.scopeHandle x) :
    Program.contAOf root (.mergeChildren q m) v = badShape := by
  unfold Program.contAOf
  revert hne
  split <;> intro hne <;> first
    | rfl
    | contradiction
    | exact absurd rfl (hne _)
    | (rename_i heq; exact absurd heq (hne _))
    | simp_all

theorem contAOf_mergeForkOne_scope (q : Point) (i : Nat) (m : MemoMapId) (parent : Nat)
    (forked : List FiberId) (child : Nat) :
    Program.contAOf root (.mergeForkOne q i m parent forked) (Val.scopeHandle child) =
      Prim.onSuccess (Prim.withFiber (EffThunk.forkLayer (q.child i) m child))
        (.mergeForkNext q i m parent forked) := rfl

theorem contAOf_mergeForkOne_other (q : Point) (i : Nat) (m : MemoMapId) (parent : Nat)
    (forked : List FiberId) (v : Val) (hne : ∀ x, v ≠ Val.scopeHandle x) :
    Program.contAOf root (.mergeForkOne q i m parent forked) v = badShape := by
  unfold Program.contAOf
  revert hne
  -- the table's catch-all row carries "the wrong-shape row did not match", refuted at the
  -- row's own arguments (five of them: past what `simp_all` instantiates)
  split <;> intro hne <;> first
    | rfl
    | contradiction
    | exact absurd rfl (hne _)
    | (rename_i heq; exact absurd heq (hne _))
    | exact (‹∀ (a : Point) (b : Nat) (c : MemoMapId) (d : Nat) (e : List FiberId),
        EffName.mergeForkOne q i m parent forked = EffName.mergeForkOne a b c d e → False›
        q i m parent forked rfl).elim
    | simp_all

theorem contAOf_mergeForkNext_fiber (q : Point) (i : Nat) (m : MemoMapId) (parent : Nat)
    (forked : List FiberId) (id : FiberId) :
    Program.contAOf root (.mergeForkNext q i m parent forked) (Val.fiber id) =
      (if i = 0 then
        Prim.onSuccess
          (Prim.sync (EffThunk.op (SyncOp.scopeFork parent FinalizerStrategy.sequential)))
          (.mergeForkOne q 1 m parent (forked ++ [id]))
      else
        Prim.onSuccess (Prim.withFiber (EffThunk.awaitAllFailFast (forked ++ [id])))
          .mergeContexts) := by
  cases id; rfl

theorem contAOf_mergeForkNext_other (q : Point) (i : Nat) (m : MemoMapId) (parent : Nat)
    (forked : List FiberId) (v : Val) (hne : ∀ x, v ≠ Val.fiber x) :
    Program.contAOf root (.mergeForkNext q i m parent forked) v = badShape := by
  unfold Program.contAOf
  revert hne
  -- the table's catch-all row carries "the wrong-shape row did not match", refuted at the
  -- row's own arguments (five of them: past what `simp_all` instantiates)
  split <;> intro hne <;> first
    | rfl
    | contradiction
    | exact absurd rfl (hne _)
    | (rename_i heq; exact absurd heq (hne _))
    | exact (‹∀ (a : Point) (b : Nat) (c : MemoMapId) (d : Nat) (e : List FiberId),
        EffName.mergeForkNext q i m parent forked = EffName.mergeForkNext a b c d e → False›
        q i m parent forked rfl).elim
    | simp_all

/-! The n-ary merge's three names (the host rows slice): the same protocol over the
`layers` spine, the sibling count read off the node at `q` (`mergeAllCount`). -/

theorem contAOf_mergeAllChildren_scope (q : Point) (m : MemoMapId) (parent : Nat) :
    Program.contAOf root (.mergeAllChildren q m) (Val.scopeHandle parent) =
      (if 0 < mergeAllCount root q then
        Prim.onSuccess
          (Prim.sync (EffThunk.op (SyncOp.scopeFork parent FinalizerStrategy.sequential)))
          (.mergeAllForkOne q 0 m parent [])
      else
        Prim.onSuccess (Prim.withFiber (EffThunk.awaitAllFailFast [])) .mergeContexts) := rfl

theorem contAOf_mergeAllChildren_other (q : Point) (m : MemoMapId) (v : Val)
    (hne : ∀ x, v ≠ Val.scopeHandle x) :
    Program.contAOf root (.mergeAllChildren q m) v = badShape := by
  unfold Program.contAOf
  revert hne
  split <;> intro hne <;> first
    | rfl
    | contradiction
    | exact absurd rfl (hne _)
    | (rename_i heq; exact absurd heq (hne _))
    | simp_all

theorem contAOf_mergeAllForkOne_scope (q : Point) (i : Nat) (m : MemoMapId) (parent : Nat)
    (forked : List FiberId) (child : Nat) :
    Program.contAOf root (.mergeAllForkOne q i m parent forked) (Val.scopeHandle child) =
      Prim.onSuccess (Prim.withFiber (EffThunk.forkLayer (q.spineChild i) m child))
        (.mergeAllForkNext q i m parent forked) := rfl

theorem contAOf_mergeAllForkOne_other (q : Point) (i : Nat) (m : MemoMapId) (parent : Nat)
    (forked : List FiberId) (v : Val) (hne : ∀ x, v ≠ Val.scopeHandle x) :
    Program.contAOf root (.mergeAllForkOne q i m parent forked) v = badShape := by
  unfold Program.contAOf
  revert hne
  split <;> intro hne <;> first
    | rfl
    | contradiction
    | exact absurd rfl (hne _)
    | (rename_i heq; exact absurd heq (hne _))
    | exact (‹∀ (a : Point) (b : Nat) (c : MemoMapId) (d : Nat) (e : List FiberId),
        EffName.mergeAllForkOne q i m parent forked = EffName.mergeAllForkOne a b c d e → False›
        q i m parent forked rfl).elim
    | simp_all

theorem contAOf_mergeAllForkNext_fiber (q : Point) (i : Nat) (m : MemoMapId) (parent : Nat)
    (forked : List FiberId) (id : FiberId) :
    Program.contAOf root (.mergeAllForkNext q i m parent forked) (Val.fiber id) =
      (if i + 1 < mergeAllCount root q then
        Prim.onSuccess
          (Prim.sync (EffThunk.op (SyncOp.scopeFork parent FinalizerStrategy.sequential)))
          (.mergeAllForkOne q (i + 1) m parent (forked ++ [id]))
      else
        Prim.onSuccess (Prim.withFiber (EffThunk.awaitAllFailFast (forked ++ [id])))
          .mergeContexts) := by
  cases id; rfl

theorem contAOf_mergeAllForkNext_other (q : Point) (i : Nat) (m : MemoMapId) (parent : Nat)
    (forked : List FiberId) (v : Val) (hne : ∀ x, v ≠ Val.fiber x) :
    Program.contAOf root (.mergeAllForkNext q i m parent forked) v = badShape := by
  unfold Program.contAOf
  revert hne
  split <;> intro hne <;> first
    | rfl
    | contradiction
    | exact absurd rfl (hne _)
    | (rename_i heq; exact absurd heq (hne _))
    | exact (‹∀ (a : Point) (b : Nat) (c : MemoMapId) (d : Nat) (e : List FiberId),
        EffName.mergeAllForkNext q i m parent forked = EffName.mergeAllForkNext a b c d e → False›
        q i m parent forked rfl).elim
    | simp_all

theorem contAOf_mergeContexts (v : Val) :
    Program.contAOf root .mergeContexts v = mergeContextsK v := rfl

theorem contAOf_serviceLookup (key : ServiceKey) (v : Val) :
    Program.contAOf root (.serviceLookup key) v = serviceLookupK key v := rfl

theorem contAOf_bindService (key : Option ServiceKey) (v : Val) :
    Program.contAOf root (.bindService key) v = bindServiceK key v := rfl

theorem contEOf_orDie (c : CauseV) :
    Program.contEOf root .orDie c = Prim.failure (orDieCause c) := rfl

theorem suspendBodyAt_memoLookup (q : Point) (m : MemoMapId) (scope : Nat) :
    suspendBodyAt root (.memoLookup q m scope) =
      Prim.onSuccess (Prim.sync (EffThunk.op (SyncOp.memoGet q.path m))) (.memoize q m scope) :=
  rfl

theorem withFiberOf_forkLayer (q : Point) (m : MemoMapId) (scope : Nat) :
    (interpOf root).withFiberOf (.forkLayer q m scope) =
      some (.fork (resolveLayer root q m scope) ⟨true, true, .inherit⟩) := rfl

theorem withFiberOf_awaitAllFailFast (targets : List FiberId) :
    (interpOf root).withFiberOf (.awaitAllFailFast targets) = some (.awaitAllFailFast targets) :=
  rfl

/-- The layer at a point, resolved: the node's term, built — `compileLayer` for every
constructor but a reference, which hops to its target (`resolveLayer.resolveLayerTerm`, the
host rows slice). -/
theorem resolveLayer_of_at {q : Point} {l : LayerTerm NativeOp}
    (h : Node.at_ (Node.eff root) q.path = some (Node.layer l)) (m : MemoMapId) (scope : Nat) :
    resolveLayer root q m scope = resolveLayer.resolveLayerTerm root l q m scope := by
  simp [resolveLayer, h]

/-- A term that is no reference resolves as `compileLayer`. -/
theorem resolveLayerTerm_of_nonref (l : LayerTerm NativeOp) (q : Point) (m : MemoMapId)
    (scope : Nat) (hl : ∀ t, l ≠ .ref t) :
    resolveLayer.resolveLayerTerm root l q m scope = compileLayer l q m scope := by
  cases l <;> first | rfl | exact absurd rfl (hl _)

/-- A reference with fuel hops to its target, one fuel down; with none it is the frontier. -/
theorem resolveLayerTerm_ref (target : List Nat) (q : Point) (m : MemoMapId) (scope : Nat) :
    resolveLayer.resolveLayerTerm root (.ref target) q m scope =
      match q.fuel with
      | 0 => frontier q
      | _ + 1 =>
        match Node.at_ (Node.eff root) target with
        | some (Node.layer (.ref _)) => badShape
        | some (Node.layer l) => compileLayer l (q.redirect target) m scope
        | _ => badShape := rfl

theorem innerLayerAt_effect {q : Point} {key : ServiceKey} {body : NativeEff}
    (h : Node.at_ (Node.eff root) q.path = some (Node.layer (.effect key body)))
    (m : MemoMapId) (child : Nat) :
    innerLayerAt root q m child = Prim.suspend (EffThunk.memoLookup q m child) := by
  simp [innerLayerAt, h]

theorem innerLayerAt_effectDiscard {q : Point} {body : NativeEff}
    (h : Node.at_ (Node.eff root) q.path = some (Node.layer (.effectDiscard body)))
    (m : MemoMapId) (child : Nat) :
    innerLayerAt root q m child = Prim.suspend (EffThunk.memoLookup q m child) := by
  simp [innerLayerAt, h]

theorem innerLayerAt_provide {q : Point} {self that : LayerTerm NativeOp}
    (h : Node.at_ (Node.eff root) q.path = some (Node.layer (.provide self that)))
    (m : MemoMapId) (child : Nat) :
    innerLayerAt root q m child =
      Prim.onSuccess (resolveLayer root (q.child 1) m child)
        (.provideThen q m child CombineMode.provide) := by
  simp [innerLayerAt, h]

theorem innerLayerAt_provideMerge {q : Point} {self that : LayerTerm NativeOp}
    (h : Node.at_ (Node.eff root) q.path = some (Node.layer (.provideMerge self that)))
    (m : MemoMapId) (child : Nat) :
    innerLayerAt root q m child =
      Prim.onSuccess (resolveLayer root (q.child 1) m child)
        (.provideThen q m child CombineMode.provideMerge) := by
  simp [innerLayerAt, h]

theorem innerLayerAt_merge {q : Point} {left right : LayerTerm NativeOp}
    (h : Node.at_ (Node.eff root) q.path = some (Node.layer (.merge left right)))
    (m : MemoMapId) (child : Nat) :
    innerLayerAt root q m child =
      Prim.onSuccess
        (Prim.sync (EffThunk.op (SyncOp.scopeFork child FinalizerStrategy.parallel)))
        (.mergeChildren q m) := by
  simp [innerLayerAt, h]

theorem innerLayerAt_mergeAll {q : Point} {layers : LayerTerms NativeOp}
    (h : Node.at_ (Node.eff root) q.path = some (Node.layer (.mergeAll layers)))
    (m : MemoMapId) (child : Nat) :
    innerLayerAt root q m child =
      Prim.onSuccess
        (Prim.sync (EffThunk.op (SyncOp.scopeFork child FinalizerStrategy.parallel)))
        (.mergeAllChildren q m) := by
  simp [innerLayerAt, h]

/-- The count of a `mergeAll` at its node is the spine's length. -/
theorem mergeAllCount_of_at {q : Point} {layers : LayerTerms NativeOp}
    (h : Node.at_ (Node.eff root) q.path = some (Node.layer (.mergeAll layers))) :
    mergeAllCount root q = layers.length := by
  simp [mergeAllCount, h]

theorem constructionAt_effect {q : Point} {key : ServiceKey} {body : NativeEff}
    (h : Node.at_ (Node.eff root) q.path = some (Node.layer (.effect key body)))
    (layerScope : Nat) :
    constructionAt root q layerScope =
      updateContextAt (Env.ContextUpdate.provideService Env.scopeKey (Val.scopeHandle layerScope))
        (Region.construct (q.child 0) (some key)) := by
  simp [constructionAt, h]

theorem constructionAt_effectDiscard {q : Point} {body : NativeEff}
    (h : Node.at_ (Node.eff root) q.path = some (Node.layer (.effectDiscard body)))
    (layerScope : Nat) :
    constructionAt root q layerScope =
      updateContextAt (Env.ContextUpdate.provideService Env.scopeKey (Val.scopeHandle layerScope))
        (Region.construct (q.child 0) none) := by
  simp [constructionAt, h]

end joinConts

/-! ## The layer rows of the census, on the compile route (the join, commit 5)

The compile-route restatements of what `Machine/Layer.lean` (`4aae12f`) witnessed for the
eighteen `layer.*` rows and the two scope rows of `Test/Audit/RuntimeCoverage.lean`: the
constructor arms of `compileLayer`, the readers behind the `*K` continuations on the values
they read, the region programs, `Effect.provide`'s frame, and the native `scoped` entry and
exit. Each is an equation, `rfl` or one `simp` with the reader's lemma; the rows cite them
beside the `contAOf_*` equations above and the store laws (`Machine/StoresLaws.lean`). -/
section joinWitnesses

variable (root : NativeEff)

/-- `Layer.succeed` is `fromBuildUnsafe(succeed(Context.make(key, value)))` (`Layer.ts:1129`):
the context, no scope handling of its own. census: layer.from-build-unsafe -/
theorem compileLayer_succeed (key : ServiceKey) (value : Lit) (q : Point) (m : MemoMapId)
    (scope : Nat) (v : Val) (h : Lit.toVal value = some v) :
    compileLayer (.succeed key value) q m scope =
      Prim.success (Env.encode (Env.Context.empty.addV key v)) := by
  simp [compileLayer, h]

/-- `fromBuild` (`:333-345`): a child of the caller's scope forked first, the rest named.
census: layer.from-build-child-scope -/
theorem compileLayer_effect (key : ServiceKey) (body : NativeEff) (q : Point) (m : MemoMapId)
    (scope : Nat) :
    compileLayer (.effect key body) q m scope =
      Prim.onSuccess
        (Prim.sync (EffThunk.op (SyncOp.scopeFork scope FinalizerStrategy.sequential)))
        (.fromBuildThen q m) := rfl

theorem compileLayer_effectDiscard (body : NativeEff) (q : Point) (m : MemoMapId) (scope : Nat) :
    compileLayer (.effectDiscard body) q m scope =
      Prim.onSuccess
        (Prim.sync (EffThunk.op (SyncOp.scopeFork scope FinalizerStrategy.sequential)))
        (.fromBuildThen q m) := rfl

/-- `provide` is a `fromBuild` wrapper too (`:1915`). census: layer.provide-dependency-first -/
theorem compileLayer_provide (self that : LayerTerm NativeOp) (q : Point) (m : MemoMapId)
    (scope : Nat) :
    compileLayer (.provide self that) q m scope =
      Prim.onSuccess
        (Prim.sync (EffThunk.op (SyncOp.scopeFork scope FinalizerStrategy.sequential)))
        (.fromBuildThen q m) := rfl

theorem compileLayer_provideMerge (self that : LayerTerm NativeOp) (q : Point) (m : MemoMapId)
    (scope : Nat) :
    compileLayer (.provideMerge self that) q m scope =
      Prim.onSuccess
        (Prim.sync (EffThunk.op (SyncOp.scopeFork scope FinalizerStrategy.sequential)))
        (.fromBuildThen q m) := rfl

/-- `merge` is `mergeAllEffect` under `fromBuild` (`:1587`). census: layer.merge-parallel-scopes -/
theorem compileLayer_merge (left right : LayerTerm NativeOp) (q : Point) (m : MemoMapId)
    (scope : Nat) :
    compileLayer (.merge left right) q m scope =
      Prim.onSuccess
        (Prim.sync (EffThunk.op (SyncOp.scopeFork scope FinalizerStrategy.sequential)))
        (.fromBuildThen q m) := rfl

/-- `fresh` builds the inner layer with a brand-new memo map on the same scope, no `fromBuild`
child of its own (`:3851`). census: layer.fresh-drops-memoization -/
theorem compileLayer_fresh (inner : LayerTerm NativeOp) (q : Point) (m : MemoMapId) (scope : Nat) :
    compileLayer (.fresh inner) q m scope =
      Prim.onSuccess (Prim.sync (EffThunk.op (SyncOp.memoFork none)))
        (.freshThen (q.child 0) scope) := rfl

/-- `orDie` is `catch_(build, die)` (`:3327`). -/
theorem compileLayer_orDie (inner : LayerTerm NativeOp) (q : Point) (m : MemoMapId) (scope : Nat) :
    compileLayer (.orDie inner) q m scope =
      Prim.onFailure (compileLayer inner (q.child 0) m scope) .orDie := rfl

/-- `mergeAll` is `mergeAllEffect` under `fromBuild` too (`:1587`, the host rows slice). -/
theorem compileLayer_mergeAll (layers : LayerTerms NativeOp) (q : Point) (m : MemoMapId)
    (scope : Nat) :
    compileLayer (.mergeAll layers) q m scope =
      Prim.onSuccess
        (Prim.sync (EffThunk.op (SyncOp.scopeFork scope FinalizerStrategy.sequential)))
        (.fromBuildThen q m) := rfl

/-- A reference reaching the table is the refusal: `resolveLayer` redirects to the target
before consulting it, and `orDie` compiles its inner term at the table directly. -/
theorem compileLayer_ref (target : List Nat) (q : Point) (m : MemoMapId) (scope : Nat) :
    compileLayer (.ref target) q m scope = badShape := rfl

/-- `buildWithMemoMap` installs the map as the `CurrentMemoMap` service (`Layer.ts:756-762`).
census: layer.build-with-memo-map-service -/
theorem currentMemoMapOf_provideService (m : MemoMapId) (prev : Env.Ctx) :
    currentMemoMapOf
        ((Env.ContextUpdate.provideService Env.currentMemoMapKey (Val.memoMap m)).apply prev) =
      some m := by
  cases m
  unfold currentMemoMapOf
  rw [Env.ContextUpdate.apply_provideService_getV]
  rfl

/-- `forkOrCreate` reads `CurrentMemoMap` (`:585-588`): present after `Context.add`, absent from
the empty context. census: layer.current-memo-map-fork-or-create -/
theorem currentMemoMapOf_addV (ctx : Env.Ctx) (id : Nat) :
    currentMemoMapOf (ctx.addV Env.currentMemoMapKey (Val.memoMap ⟨id⟩)) = some ⟨id⟩ := by
  unfold currentMemoMapOf
  rw [Env.Context.getV_addV_same]
  rfl

theorem currentMemoMapOf_empty : currentMemoMapOf Env.Context.empty = none := rfl

theorem regionCode_program (q : Point) : regionCode root (.program q) = resolve root q := rfl

/-- The build region: `self.build(memoMap, scope)` at the point (`Layer.ts:1920-1922`).
census: layer.provide-dependency-first -/
theorem regionCode_build (q : Point) (m : MemoMapId) (scope : Nat) :
    regionCode root (.build q m scope) = resolveLayer root q m scope := rfl

/-- `buildWithMemoMap` adds the same map to the produced context (`:762`).
census: layer.build-with-memo-map-service -/
theorem regionCode_buildAdding (q : Point) (m : MemoMapId) (scope : Nat) :
    regionCode root (.buildAdding q m scope) =
      Prim.onSuccess (resolveLayer root q m scope) (.addCurrentMemoMap m) := rfl

theorem regionCode_construct (q : Point) (key : Option ServiceKey) :
    regionCode root (.construct q key) = Prim.onSuccess (resolve root q) (.bindService key) := rfl

theorem addCurrentMemoMapK_context (m : MemoMapId) (ctx : Env.Ctx) :
    addCurrentMemoMapK m (Env.encode ctx) =
      Prim.success (Env.encode (ctx.addV Env.currentMemoMapKey (Val.memoMap m))) := by
  simp [addCurrentMemoMapK, Env.decode_encode]

/-- `buildWithScope` on the fiber context: the memo map is still forked or created from it
(`:974-979`). census: layer.build-with-scope-still-forks-memo -/
theorem buildWithScopeK_context (q : Point) (scope : Nat) (ctx : Ctx) :
    buildWithScopeK q scope (Val.context ctx) =
      Prim.onSuccess
        (Prim.sync (EffThunk.op (SyncOp.memoFork (currentMemoMapOf ctx.services))))
        (.withMemoMapThen q scope) := by
  simp [buildWithScopeK, Val.context?_context]

/-- `Effect.service` on the fiber context: the value when the key is there.
census: layer.build-uses-ambient-scope -/
theorem serviceLookupK_found (key : ServiceKey) (ctx : Ctx) (value : Val)
    (h : ctx.services.getV key = some value) :
    serviceLookupK key (Val.context ctx) = Prim.success value := by
  simp [serviceLookupK, Val.context?_context, h]

/-- A missing key is the host throw of `Context.getUnsafe` as a defect (`internal/effect.ts:2134`),
never a typed error. census: layer.build-uses-ambient-scope -/
theorem serviceLookupK_missing (key : ServiceKey) (ctx : Ctx) (h : ctx.services.getV key = none) :
    serviceLookupK key (Val.context ctx) = Prim.failure (Cause.die Defect.missingService) := by
  simp [serviceLookupK, Val.context?_context, h]

/-- `provideWith` on the dependency's context: the dependent's build under `provideContext`, then
the combiner (`Layer.ts:1920-1923`). census: layer.provide-dependency-first -/
theorem provideThenK_context (q : Point) (m : MemoMapId) (scope : Nat) (mode : CombineMode)
    (ctx : Env.Ctx) :
    provideThenK q m scope mode (Env.encode ctx) =
      Prim.onSuccess
        (updateContextAt (Env.ContextUpdate.provide ctx) (Region.build (q.child 0) m scope))
        (.combineWith mode ctx) := by
  simp [provideThenK, Env.decode_encode]

/-- `provide`'s combiner is the identity: the dependency's services do not reach the caller
(`:2348`). census: layer.provide-dependency-first -/
theorem combineWithK_provide (that merged : Env.Ctx) :
    combineWithK .provide that (Env.encode merged) = Prim.success (Env.encode merged) := by
  simp [combineWithK, Env.decode_encode]

/-- `provideMerge`'s combiner is `Context.merge(that, self)` (`:2800`). -/
theorem combineWithK_provideMerge (that merged : Env.Ctx) :
    combineWithK .provideMerge that (Env.encode merged) =
      Prim.success (Env.encode (that.merge merged)) := by
  simp [combineWithK, Env.decode_encode]

/-- `updateContext` on the previous context (`internal/effect.ts:2088-2095`): the body as is when
the map is the same object, else `setContext(next)` and the restoring frame.
census: layer.provide-effect-scope -/
theorem updateThenK_context (u : Env.ContextUpdate) (body : Region) (prev : Ctx) :
    updateThenK root u body (Val.context prev) =
      (if updateKeepsIdentity u prev.services then regionCode root body
       else
        Prim.onSuccess
          (Prim.withFiber (EffThunk.setCtx (Ctx.withServices (u.apply prev.services))))
          (.bodyThen body prev)) := by
  simp [updateThenK, Val.context?_context]

theorem bindServiceK_some (key : ServiceKey) (v : Val) :
    bindServiceK (some key) v = Prim.success (Env.encode (Env.Context.empty.addV key v)) := rfl

theorem bindServiceK_none (v : Val) :
    bindServiceK none v = Prim.success (Env.encode Env.Context.empty) := rfl

theorem exitOfVal_reifyExitVal (e : ExitV) : exitOfVal (reifyExitVal e) = some e := by
  rw [reifyExitVal_eq_exitImage]
  exact exitImage.ofVal_toVal e

theorem contextsOfList_contexts :
    ∀ ctxs : List Env.Ctx,
      contextsOfList (ctxs.map fun c => reifyExitVal (Exit.success (Env.encode c))) = some ctxs
  | [] => rfl
  | c :: rest => by
    simp [contextsOfList, exitOfVal_reifyExitVal, Env.decode_encode, contextsOfList_contexts rest]

/-- `Context.mergeAll` over the awaited builds' contexts (`Layer.ts:1600`).
census: layer.merge-parallel-scopes -/
theorem mergeContextsK_contexts (ctxs : List Env.Ctx) :
    mergeContextsK (exitsVal (ctxs.map fun c => Exit.success (Env.encode c))) =
      Prim.success (Env.encode (Env.Context.mergeAll ctxs)) := by
  simp [mergeContextsK, contextsOf, exitsVal, List.map_map, Function.comp_def,
    contextsOfList_contexts]

/-- `scopedWith`'s frame at a `provideLayer` node (`internal/layer.ts:8-22`): the build into the
fresh scope — through a private memo map when `local`, off the fiber context otherwise — the
body under the built context, the scope closed with the exit.
census: layer.provide-effect-scope -/
theorem provideLayerWithK_at (p : Point) (scope : Nat) (l : LayerTerm NativeOp) (isLocal : Bool)
    (b : NativeEff) (h : Node.at_ (Node.eff root) p.path = some (Node.eff (.provideLayer l isLocal b))) :
    provideLayerWithK root p scope =
      Prim.onExit
        (Prim.onSuccess
          (if isLocal then
            Prim.onSuccess (Prim.sync (EffThunk.op (SyncOp.memoFork none)))
              (.withMemoMapThen (p.child 0) scope)
          else
            Prim.onSuccess (Prim.withFiber EffThunk.getCtx)
              (.buildWithScopeFromContext (p.child 0) scope))
          (.provideLayerBody p))
        (.scopeClose scope) false := by
  simp [provideLayerWithK, h]

/-- The body under `provideContext(built)` (`internal/layer.ts:20`).
census: layer.provide-effect-scope -/
theorem provideLayerBodyK_context (p : Point) (built : Env.Ctx)
    (h : (resolve root (p.child 1)).asExit? = none) :
    provideLayerBodyK root p (Env.encode built) =
      updateContextAt (Env.ContextUpdate.provide built) (Region.program (p.child 1)) := by
  simp [provideLayerBodyK, Env.decode_encode, h]

/-- `provideContext` of an exit is that exit (`internal/effect.ts:2196`). -/
theorem provideLayerBodyK_exit (p : Point) (built : Env.Ctx) (exit : ExitV)
    (h : (resolve root (p.child 1)).asExit? = some exit) :
    provideLayerBodyK root p (Env.encode built) = Prim.ofExit exit := by
  simp [provideLayerBodyK, Env.decode_encode, h]

/-- The scope `scopedWith` made closes with the frame's exit (`internal/effect.ts:3967`).
census: layer.provide-effect-scope -/
theorem finalizerProgram_scopeClose (scope : Nat) (exit : ExitV) :
    (interpOf root).finalizerProgram (.scopeClose scope) exit =
      some (Prim.withFiber (EffThunk.closeScope scope exit)) := rfl

/-- The native `scoped` entry (`internal/effect.ts:3938-3948`): the scope made at the supply, the
`Scope` service installed on the fiber context, the body under the frame that carries the
previous context. census: scope.remove-finalizer -/
theorem enterScoped_eq (p : Point)
    (m : RunMachine EffName EffThunk Val Err Defect FiberId Ann Ctx Stores)
    (f : RunFiber EffName EffThunk Val Err Defect FiberId Ann Ctx) (yielding : Bool) :
    enterScoped root p m f yielding =
      ⟨{ m with state := { m.state with
            scopes := m.state.scopes.make m.state.nextName .sequential
            nextName := m.state.nextName + 1 } },
        { f with
          context := f.context.withScope m.state.nextName
          maxOpsBeforeYield := (f.context.withScope m.state.nextName).maxOpsBeforeYield
          preventYield := (f.context.withScope m.state.nextName).preventYield
          frame := { f.frame with
            current := Prim.onExit (resolve root (p.child 0))
              (.scopedExit f.context m.state.nextName) false } },
        yielding, .continue_, []⟩ := rfl

/-- The scoped callback restores the previous context before the close (`:3944-3947`), whether
or not the scope is known to the store. census: scope.remove-finalizer -/
theorem exitScoped_restores
    (m : RunMachine EffName EffThunk Val Err Defect FiberId Ann Ctx Stores)
    (f : RunFiber EffName EffThunk Val Err Defect FiberId Ann Ctx) (yielding : Bool) (ex : ExitV)
    (body : NCode) (previous : Ctx) (scope : Nat) (flag : Bool)
    (ha : (f.frame.getCont (match ex with | .success _ => .contA | .failure _ => .contE)
        (match ex with | .success _ => false | .failure _ => true)).answer =
      .frame (Prim.onExit body (.scopedExit previous scope) flag)) :
    (exitScoped root m f yielding ex).fiber.context = previous := by
  unfold exitScoped
  cases ex <;> dsimp only at ha ⊢ <;> rw [ha] <;> dsimp only <;> split <;> rfl

end joinWitnesses

/-! ## The hooks at an address -/

theorem syncValueAt_pure {root : NativeEff} {p : Point} {t : Term}
    (h : Node.at_ (Node.eff root) p.path = some (Node.eff (.sync t))) :
    syncValueAt root (EffThunk.pure p) = (evalTerm p.env t).getD Val.unit := by
  simp [syncValueAt, h]

theorem suspendBodyAt_branch_true {root : NativeEff} {q : Point} {k : Nat} {t : Term}
    {a b : NativeEff} (hf : q.fuel = k + 1)
    (h : Node.at_ (Node.eff root) q.path = some (Node.eff (.branch t a b)))
    (ht : evalTerm q.env t = some (Val.bool true)) :
    suspendBodyAt root (EffThunk.body q) = resolve root (q.child 0) := by
  simp [suspendBodyAt, hf, h, ht]

theorem suspendBodyAt_branch_false {root : NativeEff} {q : Point} {k : Nat} {t : Term}
    {a b : NativeEff} (hf : q.fuel = k + 1)
    (h : Node.at_ (Node.eff root) q.path = some (Node.eff (.branch t a b)))
    (ht : evalTerm q.env t = some (Val.bool false)) :
    suspendBodyAt root (EffThunk.body q) = resolve root (q.child 1) := by
  simp [suspendBodyAt, hf, h, ht]

theorem suspendBodyAt_branch_bad {root : NativeEff} {q : Point} {k : Nat} {t : Term}
    {a b : NativeEff} (hf : q.fuel = k + 1)
    (h : Node.at_ (Node.eff root) q.path = some (Node.eff (.branch t a b)))
    (ht : ∀ flag, evalTerm q.env t ≠ some (Val.bool flag)) :
    suspendBodyAt root (EffThunk.body q) = badShape := by
  rcases hv : evalTerm q.env t with _ | v
  · simp [suspendBodyAt, hf, h, hv]
  · cases v
    all_goals first
      | exact absurd hv (ht _)
      | simp [suspendBodyAt, hf, h, hv]

/-- A source suspension returns the whole child program; it does not execute the
child's own suspension. The child lookup is established independently by `at_child`. -/
theorem suspendBodyAt_suspend {root : NativeEff} {q : Point} {k : Nat} {b : NativeEff}
    (hf : q.fuel = k + 1) (h : Node.at_ (Node.eff root) q.path = some (Node.eff (.suspend b))) :
    suspendBodyAt root (EffThunk.body q) = resolve root (q.child 0) := by
  simp only [suspendBodyAt, hf, h]

theorem suspendBodyAt_of_at {root : NativeEff} {q : Point} {k : Nat} {e : NativeEff}
    (hf : q.fuel = k + 1) (h : Node.at_ (Node.eff root) q.path = some (Node.eff e))
    (hnb : ∀ t a b, e ≠ .branch t a b) (hng : ∀ ss, e ≠ .gen ss)
    (hnw : ∀ i t s b, e ≠ .whileLoop i t s b) (hns : ∀ b, e ≠ .suspend b)
    (hnl : ∀ l i b, e ≠ .provideLayer l i b) :
    suspendBodyAt root (EffThunk.body q) = compileEff e q := by
  cases e <;> first
    | exact absurd rfl (hnb _ _ _)
    | exact absurd rfl (hng _)
    | exact absurd rfl (hnw _ _ _ _)
    | exact absurd rfl (hns _)
    | exact absurd rfl (hnl _ _ _)
    | simp [suspendBodyAt, hf, h]

/-- `Effect.provide`'s suspension answers the scope allocation (the join). -/
theorem suspendBodyAt_provideLayer {root : NativeEff} {q : Point} {k : Nat}
    {l : LayerTerm NativeOp} {i : Bool} {b : NativeEff} (hf : q.fuel = k + 1)
    (h : Node.at_ (Node.eff root) q.path = some (Node.eff (.provideLayer l i b))) :
    suspendBodyAt root (EffThunk.body q) =
      Prim.onSuccess (Prim.sync (EffThunk.op (SyncOp.scopeMake FinalizerStrategy.sequential)))
        (EffName.provideLayerWith q) := by
  simp only [suspendBodyAt, hf, h]

/-- A plain body whose compiled head is already an exit has that exit as its meaning, at
unchanged stores: the fold of `compileEff_exit_fold` is the body's meaning. -/
theorem meaning_of_asExit : ∀ (b : NativeEff) (q : Point) (s : Stores) {exit : ExitV},
    Plain b = true → (compileEff b q).asExit? = some exit → meaning b q.env s = (exit, s)
  | .succeed v, q, s, exit, _, h => by
    rcases hf : q.fuel with _ | k
    · rw [compileEff_at_zero _ hf] at h; simp [frontier, Prim.asExit?] at h
    · rw [compileEff_succeed v hf] at h
      rcases hx : evalTerm q.env v with _ | x
      · simp only [hx, badShape, Prim.asExit?_failure, Option.some.injEq] at h
        subst h
        exact meaning_succeed_none v q.env s hx
      · simp only [hx, Prim.asExit?_success, Option.some.injEq] at h
        subst h
        exact meaning_succeed_some v q.env s hx
  | .fail e, q, s, exit, _, h => by
    rcases hf : q.fuel with _ | k
    · rw [compileEff_at_zero _ hf] at h; simp [frontier, Prim.asExit?] at h
    · rw [compileEff_fail e hf] at h
      rcases hx : evalTerm q.env e with _ | x
      · simp only [hx, badShape, Prim.asExit?_failure, Option.some.injEq] at h
        subst h
        exact meaning_fail_none e q.env s hx
      · simp only [hx, Prim.asExit?_failure, Option.some.injEq] at h
        subst h
        exact meaning_fail_some e q.env s hx
  | .failCause c, q, s, exit, _, h => by
    rcases hf : q.fuel with _ | k
    · rw [compileEff_at_zero _ hf] at h; simp [frontier, Prim.asExit?] at h
    · rw [compileEff_failCause c hf] at h
      rcases hc : causeOf q.env c with _ | cause
      · simp only [hc, badShape, Prim.asExit?_failure, Option.some.injEq] at h
        subst h
        exact meaning_failCause_none c q.env s hc
      · simp only [hc, Prim.asExit?_failure, Option.some.injEq] at h
        subst h
        exact meaning_failCause_some c q.env s hc
  | .yieldError e, q, s, exit, _, h => by
    rcases hf : q.fuel with _ | k
    · rw [compileEff_at_zero _ hf] at h; simp [frontier, Prim.asExit?] at h
    · rw [compileEff_yieldError e hf] at h
      rcases hx : evalTerm q.env e with _ | x
      · simp only [hx, badShape, Prim.asExit?_failure, Option.some.injEq] at h
        subst h
        exact meaning_yieldError_none e q.env s hx
      · simp [hx, Prim.asExit?] at h
  | .sync t, q, s, exit, _, h => by
    rcases hf : q.fuel with _ | k
    · rw [compileEff_at_zero _ hf] at h; simp [frontier, Prim.asExit?] at h
    · rw [compileEff_sync t hf] at h; simp [Prim.asExit?] at h
  | .suspend b, q, s, exit, _, h => by
    rcases hf : q.fuel with _ | k
    · rw [compileEff_at_zero _ hf] at h; simp [frontier, Prim.asExit?] at h
    · rw [compileEff_suspend b hf] at h; simp [Prim.asExit?] at h
  | .perform op r, q, s, exit, hpl, h => by
    have hk := Plain.perform_sync hpl
    rcases hf : q.fuel with _ | k
    · rw [compileEff_at_zero _ hf] at h; simp [frontier, Prim.asExit?] at h
    · rw [compileEff_perform_sync op r hf hk] at h
      rcases hx : evalTerm q.env r with _ | x
      · simp only [hx, badShape, Prim.asExit?_failure, Option.some.injEq] at h
        subst h
        exact meaning_perform_noEval op r q.env s hk hx
      · rcases ho : NativeOp.syncOpOf op x with _ | o
        · simp only [hx, ho, badShape, Prim.asExit?_failure, Option.some.injEq] at h
          subst h
          exact meaning_perform_noDecode op r q.env s hk hx ho
        · simp [hx, ho, Prim.asExit?] at h
  | .bind a b, q, s, exit, _, h => by
    rcases hf : q.fuel with _ | k
    · rw [compileEff_at_zero _ hf] at h; simp [frontier, Prim.asExit?] at h
    · rw [compileEff_bind a b hf] at h; simp [Prim.asExit?] at h
  | .branch t a b, q, s, exit, _, h => by
    rcases hf : q.fuel with _ | k
    · rw [compileEff_at_zero _ hf] at h; simp [frontier, Prim.asExit?] at h
    · rw [compileEff_branch t a b hf] at h; simp [Prim.asExit?] at h
  | .exit b, q, s, exit, hpl, h => by
    rcases hf : q.fuel with _ | k
    · rw [compileEff_at_zero _ hf] at h; simp [frontier, Prim.asExit?] at h
    · rcases hx : (compileEff b (q.child 0)).asExit? with _ | inner
      · rw [compileEff_exit_frame b hf hx] at h; simp [Prim.asExit?] at h
      · rw [compileEff_exit_fold b hf hx] at h
        simp only [Prim.asExit?_success, Option.some.injEq] at h
        subst h
        have hb : meaning b q.env s = (inner, s) :=
          meaning_of_asExit b (q.child 0) s (Plain.exit hpl) hx
        rw [meaning_exit, hb]
  | .catchCause b hh, q, s, exit, _, h => by
    rcases hf : q.fuel with _ | k
    · rw [compileEff_at_zero _ hf] at h; simp [frontier, Prim.asExit?] at h
    · rw [compileEff_catchCause b hh hf] at h; simp [Prim.asExit?] at h
  | .matchCause b v c, q, s, exit, _, h => by
    rcases hf : q.fuel with _ | k
    · rw [compileEff_at_zero _ hf] at h; simp [frontier, Prim.asExit?] at h
    · rw [compileEff_matchCause b v c hf] at h; simp [Prim.asExit?] at h
  | .onExit b f, q, s, exit, _, h => by
    rcases hf : q.fuel with _ | k
    · rw [compileEff_at_zero _ hf] at h; simp [frontier, Prim.asExit?] at h
    · rw [compileEff_onExit b f hf] at h; simp [Prim.asExit?] at h
  | .gen _, _, _, _, hpl, _ | .uninterruptible _, _, _, _, hpl, _
  | .interruptible _, _, _, _, hpl, _ | .whileLoop _ _ _ _, _, _, _, hpl, _
  | .yieldNow _, _, _, _, hpl, _ | .callback _ _, _, _, _, hpl, _
  | .awaitFiber _ _, _, _, _, hpl, _ | .withFiber _, _, _, _, hpl, _
  | .«scoped» _, _, _, _, hpl, _ | .acquireRelease _ _, _, _, _, hpl, _
  | .choose _ _ _, _, _, _, hpl, _ | .provideLayer _ _ _, _, _, _, hpl, _
  | .service _, _, _, _, hpl, _ | .provideService _ _ _, _, _, _, hpl, _
  | .catchIf _ _ _, _, _, _, hpl, _ => by simp [Plain] at hpl

theorem contAOf_cont (root : NativeEff) (p : Point) (v : Val) :
    contAOf root (EffName.cont p) v = resolve root (p.childWith 1 v) := rfl

theorem contAOf_onValue (root : NativeEff) (p : Point) (v : Val) :
    contAOf root (EffName.onValue p) v = resolve root (p.childWith 1 v) := rfl

theorem contEOf_caught (root : NativeEff) (p : Point) (c : CauseV) :
    contEOf root (EffName.caught p) c = resolve root (p.childWith 1 (Val.exitErr c)) := rfl

theorem contEOf_onCause (root : NativeEff) (p : Point) (c : CauseV) :
    contEOf root (EffName.onCause p) c = resolve root (p.childWith 2 (Val.exitErr c)) := rfl

/-- The restoring continuation of a finalizer: the body's exit, whatever the finalizer
answered (`Compile.lean:555`). -/
theorem contAOf_restore (root : NativeEff) (ex : ExitV) (v : Val) :
    contAOf root (EffName.restore ex) v = Prim.ofExit ex := rfl

/-- The merging continuation of a finalizer: the body's exit with the finalizer's cause
(`Compile.lean:577`). -/
theorem contEOf_merge (root : NativeEff) (ex : ExitV) (c : CauseV) :
    contEOf root (EffName.merge ex) c =
      Prim.ofExit (Exit.restoreAfterFinalizer ex (Exit.failure c)) := rfl

theorem badShape_eq : badShape = Prim.ofExit badShapeExit := rfl

/-- An exit meets the `Exit` frame: the reified exit, whichever side it is. -/
theorem step_ofExit_exitFrame (root : NativeEff) (ex : ExitV) (body : NCode) (K : List NCode)
    (i : Bool) (s : Stores) :
    localStep root (fiberOf (Prim.ofExit ex) (Prim.exitFrame body :: K) i) s =
      .running (fiberOf (Prim.success (reifyExitVal ex)) K i) s := by
  cases ex <;> cases i <;> rfl

/-! ## Two classifiers, so the case splits stay decidable -/

/-- Whether a program is a `branch`: the one plain constructor `suspend` compiles through
without a thunk of its own (`Compile.lean:604-611`). -/
def isBranch : NativeEff → Bool
  | .branch _ _ _ => true
  | _ => false

theorem not_branch_of_isBranch_false {e : NativeEff} (h : isBranch e = false) :
    ∀ t a b, e ≠ .branch t a b := by
  intro t a b heq
  subst heq
  simp [isBranch] at h

theorem eq_branch_of_isBranch {e : NativeEff} (h : isBranch e = true) :
    ∃ t a b, e = .branch t a b := by
  cases e <;> simp [isBranch] at h
  exact ⟨_, _, _, rfl⟩

/-- The boolean a test evaluated to, if it evaluated to one. -/
def boolOf : Option Val → Option Bool
  | some (Val.bool flag) => some flag
  | _ => none

theorem boolOf_some {x : Option Val} {flag : Bool} (h : boolOf x = some flag) :
    x = some (Val.bool flag) := by
  rcases x with _ | v
  · simp [boolOf] at h
  · cases v <;> simp [boolOf] at h
    rw [h]

theorem boolOf_none {x : Option Val} (h : boolOf x = none) (flag : Bool) :
    x ≠ some (Val.bool flag) := by
  intro hx
  rw [hx] at h
  simp [boolOf] at h

/-! ## Reaching: the local run from one fiber is, after `c` steps, the run from another -/

/-- After `c` steps the local run from `fr` at `s` is the local run from `fr'` at `s'`,
whatever budget is left. Chains compose by adding their counts. -/
def Reaches (root : NativeEff) (c : Nat) (fr : NFiber) (s : Stores) (fr' : NFiber)
    (s' : Stores) : Prop :=
  ∀ n, localRun root (n + c) fr s = localRun root n fr' s'

theorem Reaches.refl (root : NativeEff) (fr : NFiber) (s : Stores) :
    Reaches root 0 fr s fr s := by
  intro n
  rfl

theorem Reaches.step {root : NativeEff} {fr fr' : NFiber} {s s' : Stores}
    (h : localStep root fr s = .running fr' s') : Reaches root 1 fr s fr' s' := by
  intro n
  exact localRun_running h n

/-- Two fibers with the same next step reach each other for free. -/
theorem Reaches.same {root : NativeEff} {fr fr' : NFiber} (s : Stores)
    (h : ∀ s, localStep root fr s = localStep root fr' s) : Reaches root 0 fr s fr' s := by
  intro n
  exact localRun_congr h n s

theorem Reaches.trans {root : NativeEff} {c₁ c₂ : Nat} {fr₁ fr₂ fr₃ : NFiber}
    {s₁ s₂ s₃ : Stores} (h₁ : Reaches root c₁ fr₁ s₁ fr₂ s₂)
    (h₂ : Reaches root c₂ fr₂ s₂ fr₃ s₃) : Reaches root (c₁ + c₂) fr₁ s₁ fr₃ s₃ := by
  intro n
  rw [← Nat.add_assoc, Nat.add_right_comm, h₁, h₂]

/-! ## Points, one level down -/

theorem Point.child_env (p : Point) (i : Nat) : (p.child i).env = p.env := rfl

theorem Point.childWith_env (p : Point) (i : Nat) (v : Val) :
    (p.childWith i v).env = p.env ++ [v] := rfl

/-- Positive fuel, spelled as the compile's match wants it. -/
theorem fuel_succ {e : NativeEff} {p : Point} (hd : depth e ≤ p.fuel) :
    p.fuel = (p.fuel - 1) + 1 := by
  have := depth_pos e
  omega

/-! ## The agreement: one fiber, any outer stack -/

/-- A plain program compiled at an address of the root, run by the local machine from any
outer stack `K`, reaches within `steps e` steps the fiber that holds its meaning's exit over
its meaning's stores, and continues from there as that fiber would. The count `c` is what
the run actually takes; `steps e` bounds it. -/
theorem localRun_compile (root : NativeEff) :
    ∀ (e : NativeEff) (p : Point) (K : List NCode) (i : Bool) (s : Stores),
      Plain e = true → Node.at_ (Node.eff root) p.path = some (Node.eff e) →
      depth e ≤ p.fuel →
      ∃ c, c ≤ steps e ∧
        Reaches root c (fiberOf (compileEff e p) K i) s
          (fiberOf (Prim.ofExit (meaning e p.env s).1) K i) (meaning e p.env s).2
  | .succeed v, p, K, i, s, _, _, hd => by
    rcases hx : evalTerm p.env v with _ | x
    · rw [compileEff_succeed v (fuel_succ hd), meaning_succeed_none v p.env s hx]
      simp only [hx]
      exact ⟨0, Nat.zero_le _, Reaches.refl root _ s⟩
    · rw [compileEff_succeed v (fuel_succ hd), meaning_succeed_some v p.env s hx]
      simp only [hx]
      exact ⟨0, Nat.zero_le _, Reaches.refl root _ s⟩
  | .fail e, p, K, i, s, _, _, hd => by
    rcases hx : evalTerm p.env e with _ | x
    · rw [compileEff_fail e (fuel_succ hd), meaning_fail_none e p.env s hx]
      simp only [hx]
      exact ⟨0, Nat.zero_le _, Reaches.refl root _ s⟩
    · rw [compileEff_fail e (fuel_succ hd), meaning_fail_some e p.env s hx]
      simp only [hx]
      exact ⟨0, Nat.zero_le _, Reaches.refl root _ s⟩
  | .failCause c, p, K, i, s, _, _, hd => by
    rcases hc : causeOf p.env c with _ | cause
    · rw [compileEff_failCause c (fuel_succ hd), meaning_failCause_none c p.env s hc]
      simp only [hc]
      exact ⟨0, Nat.zero_le _, Reaches.refl root _ s⟩
    · rw [compileEff_failCause c (fuel_succ hd), meaning_failCause_some c p.env s hc]
      simp only [hc]
      exact ⟨0, Nat.zero_le _, Reaches.refl root _ s⟩
  | .yieldError e, p, K, i, s, _, _, hd => by
    rcases hx : evalTerm p.env e with _ | x
    · rw [compileEff_yieldError e (fuel_succ hd), meaning_yieldError_none e p.env s hx]
      simp only [hx]
      exact ⟨0, Nat.zero_le _, Reaches.refl root _ s⟩
    · rw [compileEff_yieldError e (fuel_succ hd), meaning_yieldError_some e p.env s hx]
      simp only [hx]
      exact ⟨1, Nat.le_refl _, Reaches.step (step_yieldableError root (errOf x) K i s)⟩
  | .sync t, p, K, i, s, _, h, hd => by
    rw [compileEff_sync t (fuel_succ hd), meaning_sync]
    have hs := step_sync_pure root p K i s
    rw [syncValueAt_pure h] at hs
    exact ⟨1, Nat.le_refl _, Reaches.step hs⟩
  | .suspend b, p, K, i, s, hpl, h, hd => by
    have hb : Node.at_ (Node.eff root) ({ p with completed := [] }.child 0).path = some (Node.eff b) := at_child h 0
    have hdb : depth b ≤ ({ p with completed := [] }.child 0).fuel := by
      show depth b ≤ p.fuel - 1
      simp only [depth] at hd
      omega
    obtain ⟨c, hc, hr⟩ := localRun_compile root b ({ p with completed := [] }.child 0) K i s (Plain.suspend hpl) hb hdb
    rw [Point.child_env] at hr
    rw [meaning_suspend, compileEff_suspend b (fuel_succ hd)]
    have hs := step_suspend root (EffThunk.body p) K i s
    simp only [interpAt] at hs
    rw [suspendBodyAt_suspend (q := { p with completed := [] }) (fuel_succ hd) h, resolve_of_at hb] at hs
    exact ⟨1 + c, by simp only [steps]; omega, (Reaches.step hs).trans hr⟩
  | .perform op r, p, K, i, s, hpl, _, hd => by
    have hkind := Plain.perform_sync hpl
    rw [compileEff_perform_sync op r (fuel_succ hd) hkind]
    rcases hx : evalTerm p.env r with _ | x
    · rw [meaning_perform_noEval op r p.env s hkind hx]
      exact ⟨0, Nat.zero_le _, Reaches.refl root _ s⟩
    · rcases ho : NativeOp.syncOpOf op x with _ | o
      · rw [meaning_perform_noDecode op r p.env s hkind hx ho]
        simp only [ho]
        exact ⟨0, Nat.zero_le _, Reaches.refl root _ s⟩
      · rw [meaning_perform_sync op r p.env s hkind hx ho]
        simp only [ho]
        have hs := step_sync_op root o K i s
        rcases hstep : syncOpStep o s with _ | ⟨s', v⟩
        · simp only [hstep] at hs
          exact ⟨1, Nat.le_refl _, Reaches.step hs⟩
        · simp only [hstep] at hs
          exact ⟨1, Nat.le_refl _, Reaches.step hs⟩
  | .bind a b, p, K, i, s, hpl, h, hd => by
    obtain ⟨hpa, hpb⟩ := Plain.bind hpl
    have ha : Node.at_ (Node.eff root) (p.child 0).path = some (Node.eff a) := at_child h 0
    have hfa : depth a ≤ (p.child 0).fuel := by
      show depth a ≤ p.fuel - 1
      simp only [depth] at hd
      have := Nat.le_max_left (depth a) (depth b)
      omega
    rw [compileEff_bind a b (fuel_succ hd), meaning_bind]
    obtain ⟨ca, hca, hra⟩ := localRun_compile root a (p.child 0)
      (Prim.onSuccess (compileEff a (p.child 0)) (EffName.cont p) :: K) i s hpa ha hfa
    rw [Point.child_env] at hra
    have hpush := Reaches.step
      (step_push_onSuccess root (compileEff a (p.child 0)) (EffName.cont p) K i s)
    rcases hma : meaning a p.env s with ⟨ex, s'⟩
    rw [hma] at hra
    cases ex with
    | success v =>
      have hb : Node.at_ (Node.eff root) ({ p with completed := [] }.childWith 1 v).path = some (Node.eff b) :=
        at_childWith h 1 v
      have hfb : depth b ≤ ({ p with completed := [] }.childWith 1 v).fuel := by
        show depth b ≤ p.fuel - 1
        simp only [depth] at hd
        have := Nat.le_max_right (depth a) (depth b)
        omega
      obtain ⟨cb, hcb, hrb⟩ := localRun_compile root b ({ p with completed := [] }.childWith 1 v) K i s' hpb hb hfb
      rw [Point.childWith_env] at hrb
      have hpop := Reaches.step
        (step_success_onSuccess root v (compileEff a (p.child 0)) (EffName.cont p) K i s')
      simp only [interpAt] at hpop
      rw [contAOf_cont, resolve_of_at hb] at hpop
      exact ⟨1 + ca + 1 + cb, by simp only [steps]; omega,
        ((hpush.trans hra).trans hpop).trans hrb⟩
    | failure c =>
      have hpass := Reaches.same s' (fun s =>
        step_failure_pass_onSuccess root c (compileEff a (p.child 0)) (EffName.cont p) K i s)
      exact ⟨1 + ca + 0, by simp only [steps]; omega, (hpush.trans hra).trans hpass⟩
  | .branch t a b, p, K, i, s, hpl, h, hd => by
    obtain ⟨hpa, hpb⟩ := Plain.branch hpl
    have ha : Node.at_ (Node.eff root) ({ p with completed := [] }.child 0).path = some (Node.eff a) := at_child h 0
    have hb : Node.at_ (Node.eff root) ({ p with completed := [] }.child 1).path = some (Node.eff b) := at_child h 1
    have hfa : depth a ≤ ({ p with completed := [] }.child 0).fuel := by
      show depth a ≤ p.fuel - 1
      simp only [depth] at hd
      have := Nat.le_max_left (depth a) (depth b)
      omega
    have hfb : depth b ≤ ({ p with completed := [] }.child 1).fuel := by
      show depth b ≤ p.fuel - 1
      simp only [depth] at hd
      have := Nat.le_max_right (depth a) (depth b)
      omega
    rw [compileEff_branch t a b (fuel_succ hd)]
    have hs := step_suspend root (EffThunk.body p) K i s
    simp only [interpAt] at hs
    rcases hbo : boolOf (evalTerm p.env t) with _ | flag
    · have hbad := boolOf_none hbo
      rw [suspendBodyAt_branch_bad (q := { p with completed := [] }) (fuel_succ hd) h hbad] at hs
      rw [meaning_branch_bad t a b p.env s hbad]
      exact ⟨1, by simp only [steps]; omega, Reaches.step hs⟩
    · have ht := boolOf_some hbo
      cases flag
      · obtain ⟨c, hc, hr⟩ := localRun_compile root b ({ p with completed := [] }.child 1) K i s hpb hb hfb
        rw [Point.child_env] at hr
        rw [suspendBodyAt_branch_false (q := { p with completed := [] }) (fuel_succ hd) h ht, resolve_of_at hb] at hs
        rw [meaning_branch_false t a b p.env s ht]
        exact ⟨1 + c, by simp only [steps]; omega, (Reaches.step hs).trans hr⟩
      · obtain ⟨c, hc, hr⟩ := localRun_compile root a ({ p with completed := [] }.child 0) K i s hpa ha hfa
        rw [Point.child_env] at hr
        rw [suspendBodyAt_branch_true (q := { p with completed := [] }) (fuel_succ hd) h ht, resolve_of_at ha] at hs
        rw [meaning_branch_true t a b p.env s ht]
        exact ⟨1 + c, by simp only [steps]; omega, (Reaches.step hs).trans hr⟩
  | .exit b, p, K, i, s, hpl, h, hd => by
    have hb : Node.at_ (Node.eff root) (p.child 0).path = some (Node.eff b) := at_child h 0
    have hfb : depth b ≤ (p.child 0).fuel := by
      show depth b ≤ p.fuel - 1
      simp only [depth] at hd
      omega
    rcases hx : (compileEff b (p.child 0)).asExit? with _ | ex
    · rw [compileEff_exit_frame b (fuel_succ hd) hx, meaning_exit]
      obtain ⟨cb, hcb, hrb⟩ := localRun_compile root b (p.child 0)
        (Prim.exitFrame (compileEff b (p.child 0)) :: K) i s (Plain.exit hpl) hb hfb
      rw [Point.child_env] at hrb
      have hpush := Reaches.step (step_push_exitFrame root (compileEff b (p.child 0)) K i s)
      rcases hmb : meaning b p.env s with ⟨ex, s'⟩
      rw [hmb] at hrb
      have hpop := Reaches.step (step_ofExit_exitFrame root ex (compileEff b (p.child 0)) K i s')
      exact ⟨1 + cb + 1, by simp only [steps]; omega, (hpush.trans hrb).trans hpop⟩
    · -- the fold: the compiled program already is the meaning's exit (row D1)
      have hmb := meaning_of_asExit b (p.child 0) s (Plain.exit hpl) hx
      rw [Point.child_env] at hmb
      rw [compileEff_exit_fold b (fuel_succ hd) hx, meaning_exit, hmb]
      exact ⟨0, Nat.zero_le _, Reaches.refl root _ s⟩
  | .catchCause b hh, p, K, i, s, hpl, h, hd => by
    obtain ⟨hpb, hph⟩ := Plain.catchCause hpl
    have hb : Node.at_ (Node.eff root) (p.child 0).path = some (Node.eff b) := at_child h 0
    have hfb : depth b ≤ (p.child 0).fuel := by
      show depth b ≤ p.fuel - 1
      simp only [depth] at hd
      have := Nat.le_max_left (depth b) (depth hh)
      omega
    rw [compileEff_catchCause b hh (fuel_succ hd), meaning_catchCause]
    obtain ⟨cb, hcb, hrb⟩ := localRun_compile root b (p.child 0)
      (Prim.onFailure (compileEff b (p.child 0)) (EffName.caught p) :: K) i s hpb hb hfb
    rw [Point.child_env] at hrb
    have hpush := Reaches.step
      (step_push_onFailure root (compileEff b (p.child 0)) (EffName.caught p) K i s)
    rcases hmb : meaning b p.env s with ⟨ex, s'⟩
    rw [hmb] at hrb
    cases ex with
    | success v =>
      have hpass := Reaches.same s' (fun s =>
        step_success_pass_onFailure root v (compileEff b (p.child 0)) (EffName.caught p) K i s)
      exact ⟨1 + cb + 0, by simp only [steps]; omega, (hpush.trans hrb).trans hpass⟩
    | failure c =>
      have hh' : Node.at_ (Node.eff root) ({ p with completed := [] }.childWith 1 (Val.exitErr c)).path =
          some (Node.eff hh) := at_childWith h 1 (Val.exitErr c)
      have hfh : depth hh ≤ ({ p with completed := [] }.childWith 1 (Val.exitErr c)).fuel := by
        show depth hh ≤ p.fuel - 1
        simp only [depth] at hd
        have := Nat.le_max_right (depth b) (depth hh)
        omega
      obtain ⟨ch, hch, hrh⟩ :=
        localRun_compile root hh ({ p with completed := [] }.childWith 1 (Val.exitErr c)) K i s' hph hh' hfh
      rw [Point.childWith_env] at hrh
      have hpop := Reaches.step
        (step_failure_onFailure root c (compileEff b (p.child 0)) (EffName.caught p) K i s')
      simp only [interpAt] at hpop
      rw [contEOf_caught, resolve_of_at hh'] at hpop
      exact ⟨1 + cb + 1 + ch, by simp only [steps]; omega,
        ((hpush.trans hrb).trans hpop).trans hrh⟩
  | .matchCause b v c, p, K, i, s, hpl, h, hd => by
    obtain ⟨hpb, hpv, hpc⟩ := Plain.matchCause hpl
    have hb : Node.at_ (Node.eff root) (p.child 0).path = some (Node.eff b) := at_child h 0
    have hfb : depth b ≤ (p.child 0).fuel := by
      show depth b ≤ p.fuel - 1
      simp only [depth] at hd
      have := Nat.le_max_left (depth b) (max (depth v) (depth c))
      omega
    rw [compileEff_matchCause b v c (fuel_succ hd), meaning_matchCause]
    obtain ⟨cb, hcb, hrb⟩ := localRun_compile root b (p.child 0)
      (Prim.onSuccessAndFailure (compileEff b (p.child 0)) (EffName.onValue p)
        (EffName.onCause p) :: K) i s hpb hb hfb
    rw [Point.child_env] at hrb
    have hpush := Reaches.step (step_push_onSuccessAndFailure root (compileEff b (p.child 0))
      (EffName.onValue p) (EffName.onCause p) K i s)
    rcases hmb : meaning b p.env s with ⟨ex, s'⟩
    rw [hmb] at hrb
    cases ex with
    | success x =>
      have hv' : Node.at_ (Node.eff root) ({ p with completed := [] }.childWith 1 x).path = some (Node.eff v) :=
        at_childWith h 1 x
      have hfv : depth v ≤ ({ p with completed := [] }.childWith 1 x).fuel := by
        show depth v ≤ p.fuel - 1
        simp only [depth] at hd
        have h₁ := Nat.le_max_right (depth b) (max (depth v) (depth c))
        have h₂ := Nat.le_max_left (depth v) (depth c)
        omega
      obtain ⟨cv, hcv, hrv⟩ := localRun_compile root v ({ p with completed := [] }.childWith 1 x) K i s' hpv hv' hfv
      rw [Point.childWith_env] at hrv
      have hpop := Reaches.step (step_success_onSuccessAndFailure root x
        (compileEff b (p.child 0)) (EffName.onValue p) (EffName.onCause p) K i s')
      simp only [interpAt] at hpop
      rw [contAOf_onValue, resolve_of_at hv'] at hpop
      exact ⟨1 + cb + 1 + cv, by simp only [steps]; omega,
        ((hpush.trans hrb).trans hpop).trans hrv⟩
    | failure cause =>
      have hc' : Node.at_ (Node.eff root) ({ p with completed := [] }.childWith 2 (Val.exitErr cause)).path =
          some (Node.eff c) := at_childWith h 2 (Val.exitErr cause)
      have hfc : depth c ≤ ({ p with completed := [] }.childWith 2 (Val.exitErr cause)).fuel := by
        show depth c ≤ p.fuel - 1
        simp only [depth] at hd
        have h₁ := Nat.le_max_right (depth b) (max (depth v) (depth c))
        have h₂ := Nat.le_max_right (depth v) (depth c)
        omega
      obtain ⟨cc, hcc, hrc⟩ :=
        localRun_compile root c ({ p with completed := [] }.childWith 2 (Val.exitErr cause)) K i s' hpc hc' hfc
      rw [Point.childWith_env] at hrc
      have hpop := Reaches.step (step_failure_onSuccessAndFailure root cause
        (compileEff b (p.child 0)) (EffName.onValue p) (EffName.onCause p) K i s')
      simp only [interpAt] at hpop
      rw [contEOf_onCause, resolve_of_at hc'] at hpop
      exact ⟨1 + cb + 1 + cc, by simp only [steps]; omega,
        ((hpush.trans hrb).trans hpop).trans hrc⟩
  | .onExit b f, p, K, i, s, hpl, h, hd => by
    obtain ⟨hpb, hpf⟩ := Plain.onExit hpl
    have hb : Node.at_ (Node.eff root) (p.child 0).path = some (Node.eff b) := at_child h 0
    have hfb : depth b ≤ (p.child 0).fuel := by
      show depth b ≤ p.fuel - 1
      simp only [depth] at hd
      have := Nat.le_max_left (depth b) (depth f)
      omega
    rw [compileEff_onExit b f (fuel_succ hd), meaning_onExit]
    obtain ⟨cb, hcb, hrb⟩ := localRun_compile root b (p.child 0)
      (Prim.onExit (compileEff b (p.child 0)) (EffName.fin p) false :: K) i s hpb hb hfb
    rw [Point.child_env] at hrb
    have hpush := Reaches.step
      (step_push_onExit root (compileEff b (p.child 0)) (EffName.fin p) false K i s)
    rcases hmb : meaning b p.env s with ⟨ex, s'⟩
    rw [hmb] at hrb
    dsimp only
    -- the body's exit meets the frame: the finalizer runs under the mask
    have hf' : Node.at_ (Node.eff root) ({ p with completed := [] }.childWith 1 (reifyExitVal ex)).path =
        some (Node.eff f) := at_childWith h 1 (reifyExitVal ex)
    have hff : depth f ≤ ({ p with completed := [] }.childWith 1 (reifyExitVal ex)).fuel := by
      show depth f ≤ p.fuel - 1
      simp only [depth] at hd
      have := Nat.le_max_right (depth b) (depth f)
      omega
    have hmeet := Reaches.step (step_ofExit_onExit root ex (compileEff b (p.child 0)) p K i s')
    rw [resolve_of_at hf'] at hmeet
    have hunmask (result : ExitV) (state : Stores) : Reaches root 0
        (fiberOf (Prim.ofExit result) (maskStack i K) false) state
        (fiberOf (Prim.ofExit result) K i) state := by
      cases i
      · exact Reaches.refl root _ state
      · exact Reaches.same state (fun s => step_ofExit_pass_setInterruptible root _ K false s)
    cases ex with
    | success value =>
      let program := compileEff f ({ p with completed := [] }.childWith 1
        (reifyExitVal (.success value)))
      let restore := EffName.restore (.success value)
      have hpush₂ := Reaches.step
        (step_push_onSuccess root program restore (maskStack i K) false s')
      obtain ⟨cf, hcf, hrf⟩ := localRun_compile root f
        ({ p with completed := [] }.childWith 1 (reifyExitVal (.success value)))
        (Prim.onSuccess program restore :: maskStack i K) false s' hpf hf' hff
      rw [Point.childWith_env] at hrf
      rcases hmf : meaning f (p.env ++ [reifyExitVal (.success value)]) s' with ⟨fex, s''⟩
      rw [hmf] at hrf
      cases fex with
      | success finValue =>
        have hfin := Reaches.step
          (step_success_onSuccess root finValue program restore (maskStack i K) false s'')
        change Reaches root 1 _ s'' (fiberOf (Prim.success value) (maskStack i K) false) s'' at hfin
        exact ⟨1 + cb + 1 + 1 + cf + 1 + 0, by simp only [steps]; omega,
          (((((hpush.trans hrb).trans hmeet).trans hpush₂).trans hrf).trans hfin).trans
            (hunmask (.success value) s'')⟩
      | failure finCause =>
        -- There is no failure continuation after a successful body.
        have hpass := Reaches.same s'' (fun s =>
          step_failure_pass_onSuccess root finCause program restore (maskStack i K) false s)
        exact ⟨1 + cb + 1 + 1 + cf + 0 + 0, by simp only [steps]; omega,
          (((((hpush.trans hrb).trans hmeet).trans hpush₂).trans hrf).trans hpass).trans
            (hunmask (.failure finCause) s'')⟩
    | failure cause =>
      let program := compileEff f ({ p with completed := [] }.childWith 1
        (reifyExitVal (.failure cause)))
      let restore := EffName.restore (.failure cause)
      let merge := EffName.merge (.failure cause)
      let outer := Prim.onSuccess (Prim.onFailure program merge) restore
      have hpush₂ := Reaches.step
        (step_push_onSuccess root (Prim.onFailure program merge) restore (maskStack i K) false s')
      have hpush₃ := Reaches.step
        (step_push_onFailure root program merge (outer :: maskStack i K) false s')
      obtain ⟨cf, hcf, hrf⟩ := localRun_compile root f
        ({ p with completed := [] }.childWith 1 (reifyExitVal (.failure cause)))
        (Prim.onFailure program merge :: outer :: maskStack i K) false s' hpf hf' hff
      rw [Point.childWith_env] at hrf
      rcases hmf : meaning f (p.env ++ [reifyExitVal (.failure cause)]) s' with ⟨fex, s''⟩
      rw [hmf] at hrf
      cases fex with
      | success finValue =>
        have hpass := Reaches.same s'' (fun s =>
          step_success_pass_onFailure root finValue program merge (outer :: maskStack i K) false s)
        have hfin := Reaches.step (step_success_onSuccess root finValue
          (Prim.onFailure program merge) restore (maskStack i K) false s'')
        change Reaches root 1 _ s'' (fiberOf (Prim.failure cause) (maskStack i K) false) s'' at hfin
        exact ⟨1 + cb + 1 + 1 + 1 + cf + 0 + 1 + 0, by simp only [steps]; omega,
          (((((((hpush.trans hrb).trans hmeet).trans hpush₂).trans hpush₃).trans hrf).trans hpass).trans hfin).trans
            (hunmask (.failure cause) s'')⟩
      | failure finCause =>
        have hmerge := Reaches.step
          (step_failure_onFailure root finCause program merge (outer :: maskStack i K) false s'')
        change Reaches root 1 _ s''
          (fiberOf (Prim.failure (Cause.combine cause finCause)) (outer :: maskStack i K) false) s'' at hmerge
        have hpass := Reaches.same s'' (fun s => step_failure_pass_onSuccess root
          (Cause.combine cause finCause) (Prim.onFailure program merge) restore (maskStack i K) false s)
        exact ⟨1 + cb + 1 + 1 + 1 + cf + 1 + 0 + 0, by simp only [steps]; omega,
          (((((((hpush.trans hrb).trans hmeet).trans hpush₂).trans hpush₃).trans hrf).trans hmerge).trans hpass).trans
            (hunmask (.failure (Cause.combine cause finCause)) s'')⟩
  | .gen _, _, _, _, _, hpl, _, _
  | .uninterruptible _, _, _, _, _, hpl, _, _
  | .interruptible _, _, _, _, _, hpl, _, _
  | .whileLoop _ _ _ _, _, _, _, _, hpl, _, _
  | .yieldNow _, _, _, _, _, hpl, _, _
  | .callback _ _, _, _, _, _, hpl, _, _
  | .awaitFiber _ _, _, _, _, _, hpl, _, _
  | .withFiber _, _, _, _, _, hpl, _, _
  | .scoped _, _, _, _, _, hpl, _, _
  | .acquireRelease _ _, _, _, _, _, hpl, _, _
  | .choose _ _ _, _, _, _, _, hpl, _, _
  | .provideLayer _ _ _, _, _, _, _, hpl, _, _
  | .service _, _, _, _, _, hpl, _, _
  | .provideService _ _ _, _, _, _, _, hpl, _, _
  | .catchIf _ _ _, _, _, _, _, hpl, _, _ => by simp [Plain] at hpl

/-- At the root, on the empty stack, from the empty stores: the local run finishes with the
meaning inside `steps e + 1` steps (the last one is the exit leaving the empty stack). -/
theorem localRun_root (e : NativeEff) (fuel : Nat) (hpl : Plain e = true)
    (hd : depth e ≤ fuel) :
    localRun e (steps e + 1) (fiberOf (compile e fuel) []) Stores.empty =
      some (meaning e [] Stores.empty) := by
  obtain ⟨c, hc, hr⟩ :=
    localRun_compile e e (rootPoint fuel []) [] true Stores.empty hpl rfl hd
  have hsplit : steps e + 1 = (steps e - c + 1) + c := by omega
  have h₁ := hr (steps e - c + 1)
  have h₂ := localRun_finished (step_exit_empty e (meaning e [] Stores.empty).1 true
    (meaning e [] Stores.empty).2) (steps e - c)
  rw [hsplit]
  exact h₁.trans h₂

end Effect4.Program.Agreement
