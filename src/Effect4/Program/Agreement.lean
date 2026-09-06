import Effect4.Program.Denote

/-!
# Program.Agreement — the compile agrees with the denotation, one fiber at a time

Packet: `Test/contracts/program-denotation.contract.md`; plan
`docs/research/2026-09-05-slice-1-compile-ground.md` §9. This module is the frame half of
the packet's theorem: a compiled program of the plain fragment, run by the frame machine
over the stores from *any* outer stack `K`, reaches the exit and the stores its meaning
predicts, and continues from there exactly as the run from that exit would. The machine's
command loop over one fiber is related to this local run in `Program/Agreement/Machine.lean`.

`Plain` is `Denote.Straight` without `onExit`: the `onExit` frame's finalizer runs under a
mask whose restoring frame the pop leaves on the stack (`Frames.lean`, `ensure`), which the
local run of this module does not yet model; it is the first row owed after this landing.

The local step is the machine's `evaluatePrim` on a fiber of the fragment: a `sync` thunk
answers through the store (`Fibers.lean:831-843`), and every other plain primitive is the
frame machine's `step` (`Fibers.lean:848`, `stepFrame`). Names get their meaning from
`interpOf root` (`Compile.lean:625`).
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
  | .awaitFiber _ _ | .withFiber _ | .scoped _ | .acquireRelease _ _ | .choose _ _ _ => rfl

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
  | .onExit b f => steps b + steps f + 4
  | _ => 0

theorem depth_pos (e : NativeEff) : 1 ≤ depth e := by
  cases e <;> simp [depth]

/-! ## The local step and the local run -/

abbrev NFiber := FrameFiber EffName EffThunk Val Err Defect FiberId Ann
abbrev NInterp := PrimInterp EffName EffThunk Val Err Defect FiberId Ann

/-- The frame machine's interp of a root program: `interpOf` forgets its store half. -/
def primOf (root : NativeEff) : NInterp := (interpOf root).toPrimInterp

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

/-- What an exit does with its pop, as the machine's `finalizerOr` does it
(`Fibers.lean:859-878`): an `onExit` frame whose finalizer is a program runs that program
under the frame's mask, with the restoring and merging continuations; anything else is the
frame machine's own answer. -/
def exitFrom (root : NativeEff) (ex : ExitV) (pop : NPop) (s : Stores) : LocalStep :=
  match pop.answer with
  | ContAnswer.frame (Prim.onExit _ fin _) =>
    match (interpOf root).finalizerProgram fin ex with
    | some program =>
      .running { pop.fiber with
        current := Prim.onSuccessAndFailure program (EffName.restore ex) (EffName.merge ex) } s
    | none => ofFrameStep (resumeOf root ex pop) s
  | _ => ofFrameStep (resumeOf root ex pop) s

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
      .running (fiberOf (suspendBodyAt root thunk) K i) s := rfl

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
      .running (fiberOf (contAOf root n v) K i) s := by
  cases i <;> rfl

/-- A value meets its `OnSuccessAndFailure` frame: the value arm. -/
theorem step_success_onSuccessAndFailure (v : Val) (body : NCode) (n₁ n₂ : EffName)
    (K : List NCode) (i : Bool) (s : Stores) :
    localStep root (fiberOf (Prim.success v) (Prim.onSuccessAndFailure body n₁ n₂ :: K) i) s =
      .running (fiberOf (contAOf root n₁ v) K i) s := by
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
      .running (fiberOf (contEOf root n c) K i) s := by
  cases i <;> rfl

/-- A cause meets its `OnSuccessAndFailure` frame: the cause arm. -/
theorem step_failure_onSuccessAndFailure (c : CauseV) (body : NCode) (n₁ n₂ : EffName)
    (K : List NCode) (i : Bool) (s : Stores) :
    localStep root (fiberOf (Prim.failure c) (Prim.onSuccessAndFailure body n₁ n₂ :: K) i) s =
      .running (fiberOf (contEOf root n₂ c) K i) s := by
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

/-- An exit meets an `onExit` frame whose finalizer is a program: the frame is popped, the
mask set, and the finalizer runs with the restoring and merging continuations
(`Fibers.lean:867-875`, `Compile.lean:695`). -/
theorem step_ofExit_onExit (ex : ExitV) (body : NCode) (p : Point) (K : List NCode) (i : Bool)
    (s : Stores) :
    localStep root (fiberOf (Prim.ofExit ex) (Prim.onExit body (EffName.fin p) false :: K) i) s =
      .running (fiberOf (Prim.onSuccessAndFailure
          (resolve root (p.childWith 1 (reifyExitVal ex))) (EffName.restore ex) (EffName.merge ex))
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

theorem Node.at_append (n : Node) : ∀ (path : List Nat) (i : Nat),
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
    compileEff (.suspend b) p = Prim.suspend (EffThunk.body (p.child 0)) := by
  simp [compileEff, hf]

theorem compileEff_perform_sync (op : NativeOp) (r : Term) (hf : p.fuel = k + 1)
    (hkind : (NativeOp.row op).kind = .sync) :
    compileEff (.perform op r) p =
      (match evalTerm p.env r with
       | some val =>
         match NativeOp.syncOpOf op val with
         | some operation => Prim.sync (EffThunk.op operation)
         | none => badShape
       | none => badShape) := by
  simp [compileEff, hf, hkind]; rfl

theorem compileEff_bind (a b : NativeEff) (hf : p.fuel = k + 1) :
    compileEff (.bind a b) p =
      Prim.onSuccess (compileEff a (p.child 0)) (EffName.cont p) := by
  simp [compileEff, hf]

theorem compileEff_branch (t : Term) (a b : NativeEff) (hf : p.fuel = k + 1) :
    compileEff (.branch t a b) p = Prim.suspend (EffThunk.body p) := by
  simp [compileEff, hf]

theorem compileEff_exit (b : NativeEff) (hf : p.fuel = k + 1) :
    compileEff (.exit b) p = Prim.exitFrame (compileEff b (p.child 0)) := by
  simp [compileEff, hf]

theorem compileEff_catchCause (b h : NativeEff) (hf : p.fuel = k + 1) :
    compileEff (.catchCause b h) p =
      Prim.onFailure (compileEff b (p.child 0)) (EffName.caught p) := by
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

theorem suspendBodyAt_of_at {root : NativeEff} {q : Point} {k : Nat} {e : NativeEff}
    (hf : q.fuel = k + 1) (h : Node.at_ (Node.eff root) q.path = some (Node.eff e))
    (hnb : ∀ t a b, e ≠ .branch t a b) :
    suspendBodyAt root (EffThunk.body q) = compileEff e q := by
  cases e <;> first
    | exact absurd rfl (hnb _ _ _)
    | simp [suspendBodyAt, hf, h]

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
    have hb : Node.at_ (Node.eff root) (p.child 0).path = some (Node.eff b) := at_child h 0
    have hdb : depth b ≤ (p.child 0).fuel := by
      show depth b ≤ p.fuel - 1
      simp only [depth] at hd
      omega
    obtain ⟨c, hc, hr⟩ := localRun_compile root b (p.child 0) K i s (Plain.suspend hpl) hb hdb
    rw [Point.child_env] at hr
    rw [meaning_suspend, compileEff_suspend b (fuel_succ hd)]
    cases hbr : isBranch b
    · have hs := step_suspend root (EffThunk.body (p.child 0)) K i s
      rw [suspendBodyAt_of_at (fuel_succ hdb) hb (not_branch_of_isBranch_false hbr)] at hs
      exact ⟨1 + c, by simp only [steps]; omega, (Reaches.step hs).trans hr⟩
    · obtain ⟨t, a, b', rfl⟩ := eq_branch_of_isBranch hbr
      rw [compileEff_branch t a b' (fuel_succ hdb)] at hr
      exact ⟨c, by simp only [steps] at hc ⊢; omega, hr⟩
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
      have hb : Node.at_ (Node.eff root) (p.childWith 1 v).path = some (Node.eff b) :=
        at_childWith h 1 v
      have hfb : depth b ≤ (p.childWith 1 v).fuel := by
        show depth b ≤ p.fuel - 1
        simp only [depth] at hd
        have := Nat.le_max_right (depth a) (depth b)
        omega
      obtain ⟨cb, hcb, hrb⟩ := localRun_compile root b (p.childWith 1 v) K i s' hpb hb hfb
      rw [Point.childWith_env] at hrb
      have hpop := Reaches.step
        (step_success_onSuccess root v (compileEff a (p.child 0)) (EffName.cont p) K i s')
      rw [contAOf_cont, resolve_of_at hb] at hpop
      exact ⟨1 + ca + 1 + cb, by simp only [steps]; omega,
        ((hpush.trans hra).trans hpop).trans hrb⟩
    | failure c =>
      have hpass := Reaches.same s' (fun s =>
        step_failure_pass_onSuccess root c (compileEff a (p.child 0)) (EffName.cont p) K i s)
      exact ⟨1 + ca + 0, by simp only [steps]; omega, (hpush.trans hra).trans hpass⟩
  | .branch t a b, p, K, i, s, hpl, h, hd => by
    obtain ⟨hpa, hpb⟩ := Plain.branch hpl
    have ha : Node.at_ (Node.eff root) (p.child 0).path = some (Node.eff a) := at_child h 0
    have hb : Node.at_ (Node.eff root) (p.child 1).path = some (Node.eff b) := at_child h 1
    have hfa : depth a ≤ (p.child 0).fuel := by
      show depth a ≤ p.fuel - 1
      simp only [depth] at hd
      have := Nat.le_max_left (depth a) (depth b)
      omega
    have hfb : depth b ≤ (p.child 1).fuel := by
      show depth b ≤ p.fuel - 1
      simp only [depth] at hd
      have := Nat.le_max_right (depth a) (depth b)
      omega
    rw [compileEff_branch t a b (fuel_succ hd)]
    have hs := step_suspend root (EffThunk.body p) K i s
    rcases hbo : boolOf (evalTerm p.env t) with _ | flag
    · have hbad := boolOf_none hbo
      rw [suspendBodyAt_branch_bad (fuel_succ hd) h hbad] at hs
      rw [meaning_branch_bad t a b p.env s hbad]
      exact ⟨1, by simp only [steps]; omega, Reaches.step hs⟩
    · have ht := boolOf_some hbo
      cases flag
      · obtain ⟨c, hc, hr⟩ := localRun_compile root b (p.child 1) K i s hpb hb hfb
        rw [Point.child_env] at hr
        rw [suspendBodyAt_branch_false (fuel_succ hd) h ht, resolve_of_at hb] at hs
        rw [meaning_branch_false t a b p.env s ht]
        exact ⟨1 + c, by simp only [steps]; omega, (Reaches.step hs).trans hr⟩
      · obtain ⟨c, hc, hr⟩ := localRun_compile root a (p.child 0) K i s hpa ha hfa
        rw [Point.child_env] at hr
        rw [suspendBodyAt_branch_true (fuel_succ hd) h ht, resolve_of_at ha] at hs
        rw [meaning_branch_true t a b p.env s ht]
        exact ⟨1 + c, by simp only [steps]; omega, (Reaches.step hs).trans hr⟩
  | .exit b, p, K, i, s, hpl, h, hd => by
    have hb : Node.at_ (Node.eff root) (p.child 0).path = some (Node.eff b) := at_child h 0
    have hfb : depth b ≤ (p.child 0).fuel := by
      show depth b ≤ p.fuel - 1
      simp only [depth] at hd
      omega
    rw [compileEff_exit b (fuel_succ hd), meaning_exit]
    obtain ⟨cb, hcb, hrb⟩ := localRun_compile root b (p.child 0)
      (Prim.exitFrame (compileEff b (p.child 0)) :: K) i s (Plain.exit hpl) hb hfb
    rw [Point.child_env] at hrb
    have hpush := Reaches.step (step_push_exitFrame root (compileEff b (p.child 0)) K i s)
    rcases hmb : meaning b p.env s with ⟨ex, s'⟩
    rw [hmb] at hrb
    have hpop := Reaches.step (step_ofExit_exitFrame root ex (compileEff b (p.child 0)) K i s')
    exact ⟨1 + cb + 1, by simp only [steps]; omega, (hpush.trans hrb).trans hpop⟩
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
      have hh' : Node.at_ (Node.eff root) (p.childWith 1 (Val.exitErr c)).path =
          some (Node.eff hh) := at_childWith h 1 _
      have hfh : depth hh ≤ (p.childWith 1 (Val.exitErr c)).fuel := by
        show depth hh ≤ p.fuel - 1
        simp only [depth] at hd
        have := Nat.le_max_right (depth b) (depth hh)
        omega
      obtain ⟨ch, hch, hrh⟩ :=
        localRun_compile root hh (p.childWith 1 (Val.exitErr c)) K i s' hph hh' hfh
      rw [Point.childWith_env] at hrh
      have hpop := Reaches.step
        (step_failure_onFailure root c (compileEff b (p.child 0)) (EffName.caught p) K i s')
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
      have hv' : Node.at_ (Node.eff root) (p.childWith 1 x).path = some (Node.eff v) :=
        at_childWith h 1 x
      have hfv : depth v ≤ (p.childWith 1 x).fuel := by
        show depth v ≤ p.fuel - 1
        simp only [depth] at hd
        have h₁ := Nat.le_max_right (depth b) (max (depth v) (depth c))
        have h₂ := Nat.le_max_left (depth v) (depth c)
        omega
      obtain ⟨cv, hcv, hrv⟩ := localRun_compile root v (p.childWith 1 x) K i s' hpv hv' hfv
      rw [Point.childWith_env] at hrv
      have hpop := Reaches.step (step_success_onSuccessAndFailure root x
        (compileEff b (p.child 0)) (EffName.onValue p) (EffName.onCause p) K i s')
      rw [contAOf_onValue, resolve_of_at hv'] at hpop
      exact ⟨1 + cb + 1 + cv, by simp only [steps]; omega,
        ((hpush.trans hrb).trans hpop).trans hrv⟩
    | failure cause =>
      have hc' : Node.at_ (Node.eff root) (p.childWith 2 (Val.exitErr cause)).path =
          some (Node.eff c) := at_childWith h 2 _
      have hfc : depth c ≤ (p.childWith 2 (Val.exitErr cause)).fuel := by
        show depth c ≤ p.fuel - 1
        simp only [depth] at hd
        have h₁ := Nat.le_max_right (depth b) (max (depth v) (depth c))
        have h₂ := Nat.le_max_right (depth v) (depth c)
        omega
      obtain ⟨cc, hcc, hrc⟩ :=
        localRun_compile root c (p.childWith 2 (Val.exitErr cause)) K i s' hpc hc' hfc
      rw [Point.childWith_env] at hrc
      have hpop := Reaches.step (step_failure_onSuccessAndFailure root cause
        (compileEff b (p.child 0)) (EffName.onValue p) (EffName.onCause p) K i s')
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
    have hf' : Node.at_ (Node.eff root) (p.childWith 1 (reifyExitVal ex)).path =
        some (Node.eff f) := at_childWith h 1 _
    have hff : depth f ≤ (p.childWith 1 (reifyExitVal ex)).fuel := by
      show depth f ≤ p.fuel - 1
      simp only [depth] at hd
      have := Nat.le_max_right (depth b) (depth f)
      omega
    have hmeet := Reaches.step (step_ofExit_onExit root ex (compileEff b (p.child 0)) p K i s')
    rw [resolve_of_at hf'] at hmeet
    have hpush₂ := Reaches.step (step_push_onSuccessAndFailure root
      (compileEff f (p.childWith 1 (reifyExitVal ex))) (EffName.restore ex) (EffName.merge ex)
      (maskStack i K) false s')
    obtain ⟨cf, hcf, hrf⟩ := localRun_compile root f (p.childWith 1 (reifyExitVal ex))
      (Prim.onSuccessAndFailure (compileEff f (p.childWith 1 (reifyExitVal ex)))
        (EffName.restore ex) (EffName.merge ex) :: maskStack i K) false s' hpf hf' hff
    rw [Point.childWith_env] at hrf
    rcases hmf : meaning f (p.env ++ [reifyExitVal ex]) s' with ⟨fex, s''⟩
    rw [hmf] at hrf
    -- the finalizer's exit meets its frame, then the mask lifts
    have hfin := Reaches.step (step_ofExit_finalizer root ex fex
      (compileEff f (p.childWith 1 (reifyExitVal ex))) (maskStack i K) false s'')
    have hunmask : Reaches root 0
        (fiberOf (Prim.ofExit (Exit.restoreAfterFinalizer ex (finVoid fex))) (maskStack i K)
          false) s''
        (fiberOf (Prim.ofExit (Exit.restoreAfterFinalizer ex (finVoid fex))) K i) s'' := by
      cases i
      · exact Reaches.refl root _ s''
      · exact Reaches.same s'' (fun s => step_ofExit_pass_setInterruptible root _ K false s)
    exact ⟨1 + cb + 1 + 1 + cf + 1 + 0, by simp only [steps]; omega,
      (((((hpush.trans hrb).trans hmeet).trans hpush₂).trans hrf).trans hfin).trans hunmask⟩
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
  | .choose _ _ _, _, _, _, _, hpl, _, _ => by simp [Plain] at hpl

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
