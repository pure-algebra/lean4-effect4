import Effect4.Laws.Program.Typed.Scheduler

/-!
# Laws.Program.Typed.HostWalk — the saved-stack walk over a host stack

Concept 4 (the configuration invariant); questions `loop_preserves` and `deliver_preserves`,
whose `unguard`/`finishFinalizer`/bare-exit arms deliver an exit through the fiber's saved stack
(`deliverR`, `popR`). The stack a live fiber holds is a `HostStack` (decisions row 188 (b)): ordinary
frames and registration arrows in any order. This module types the walk over it, reusing the
ordinary walk (`popR_typed`) for each ordinary frame, through one operational equation: a walk
over `slot :: rest` is the walk over `[slot]`, then, if that completed, the walk over `rest` from
the frame it returned (`popR_cons`). Codex's theorem-reuse review (2026-10-02,
`path-review.md` §3) proposed the equation; it is proved here for every interpreter.

Not established: the hook laws of the machine's interpreter (`HookLawsAt` is a premise; G2), the
typing of the scoped exit's cleanup (`prepareScopedExitR`), the whole evaluation step, progress.
-/

set_option autoImplicit false
namespace Effect4.Program.Typed
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Sched Effect4.Program.Denote
open Contracts

/-! ## Operational facts about the walk -/

/-- The walk ignores the stack field of the frame it is handed: it walks the explicit list. -/
theorem popR_stack (interp : RInterp) (ex : ExitV) (s : List ScopeFrame) (frame : RSaved)
    (x : List ScopeFrame) : popR interp ex s { frame with stack := x } = popR interp ex s frame := by
  cases s <;> rfl

/-- The walk never touches the recorded interrupt or the deferred flag. -/
theorem popR_interrupts (interp : RInterp) (ex : ExitV) (s : List ScopeFrame) (frame : RSaved) :
    (popR interp ex s frame).1.interruptedCause = frame.interruptedCause ∧
      (popR interp ex s frame).1.deferredInterrupt = frame.deferredInterrupt := by
  fun_induction popR interp ex s frame <;> aesop

/-- The walk normalised to an empty stack field, what `popR_stack` rewrites to. -/
theorem popR_mk (interp : RInterp) (ex : ExitV) (s : List ScopeFrame) (c : RProgram)
    (x : List ScopeFrame) (b : Bool) (ic : Option CauseV) (d : Bool) :
    popR interp ex s ⟨c, x, b, ic, d⟩ = popR interp ex s ⟨c, [], b, ic, d⟩ := by
  cases s <;> rfl

/-- **The walk splits at its first slot** (Codex's `path-review.md` §3, the singleton prefix): walk
`[slot]`; if it stopped to install code, keep the returned frame (its current code, masks and the
slots it pushed) with `rest` appended below; if it completed, walk `rest` with the returned exit
from the returned frame. The returned exit and frame, never the original ones: an answer slot
changes the exit, a mask slot the frame. -/
theorem popR_cons (interp : RInterp) (ex : ExitV) (slot : ScopeFrame) (rest : List ScopeFrame)
    (frame : RSaved) :
    popR interp ex (slot :: rest) frame =
      match popR interp ex [slot] frame with
      | (f, none) => ({ f with stack := f.stack ++ rest }, none)
      | (f, some ex') => popR interp ex' rest f := by
  obtain ⟨c, x, b, ic, d⟩ := frame
  cases slot with
  | restoreMask flag =>
    cases ic <;> cases flag <;> cases ex <;>
      simp only [popR, popR_mk, List.nil_append, Bool.false_and, Bool.true_and, Bool.not_false,
        Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  | finalizerMask flag =>
    cases ic <;> cases flag <;> cases ex <;>
      simp only [popR, popR_mk, List.nil_append, Bool.false_and, Bool.true_and, Bool.not_false,
        Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  | resume kind next =>
    cases kind with
    | onExit fin =>
      cases fin <;> cases ex <;> cases b <;> cases ic <;>
      simp only [popR, popR_mk, List.nil_append, List.cons_append, GuardKind.hasExitArm,
        Option.isSome, Bool.and_false, Bool.and_true, Bool.not_false, Bool.not_true,
        Bool.false_eq_true, ↓reduceIte]
    | onSuccess | onFailure | all =>
      cases ex <;> cases b <;> cases ic <;>
      simp only [popR, popR_mk, List.nil_append, GuardKind.hasExitArm, Option.isSome,
        Bool.and_false, Bool.and_true, Bool.not_false, Bool.not_true, Bool.false_eq_true,
        ↓reduceIte]
  | answer next =>
    simp only [popR]
    cases hn : next ex with
    | pure e => simp only [popR_mk]
    | vis op k =>
      cases op with
      | inl _ => simp only [List.nil_append]
      | inr fop => cases fop <;> simp only [popR_mk, List.nil_append]
  | asyncFinalizer name =>
    cases ex <;> cases b <;> cases ic <;>
      simp only [popR, popR_mk, List.nil_append, List.cons_append, Option.isSome,
        Bool.and_false, Bool.and_true, Bool.false_eq_true, ↓reduceIte, RSaved.pendingCause]
  | iter generator =>
    cases ex with
    | failure cause => simp only [popR, popR_mk]
    | success v =>
      simp only [popR]
      cases hs : (interp.iterNext generator v).2 <;> simp only [List.nil_append, List.cons_append]
  | loop name cursor =>
    cases ex with
    | failure cause => simp only [popR, popR_mk]
    | success v =>
      simp only [popR]
      cases hs : interp.loopResume name cursor v <;> simp only [List.nil_append, List.cons_append]

/-! ## The walk over a host stack -/

/-- The walk stopped at a `scoped` guard's slot (decisions row 188 (a)) over a host stack: the
current code is that scope's exit callback, its exit typed at the remaining stack's input type.
`CallbackSaved` with a `HostStack` tail. -/
def HostCallback (root : ProgramSource) (w : World) (m : RState) (host : FiberId) (tout : EffTy)
    (x : RSaved) : Prop :=
  ∃ ty prev sc ex, scopeExitCallback? x.current = some (prev, sc, ex) ∧ ExitOk w ty ex ∧
    (frameProtocols root).scopeExit w prev sc ∧ HostStack root w m host ty tout x.stack ∧
    InterruptProvenance x

/-- The walk delivered a success into a registration arrow (decisions row 188 (b)): the current
code is the race's registration marker, over the remaining stack at the race token's type, with
the correlation `RegistrationState` reads (the race exists, this fiber hosts it). -/
def HostMarker (root : ProgramSource) (w : World) (m : RState) (host : FiberId) (tout : EffTy)
    (x : RSaved) : Prop :=
  ∃ raceId race resultTy, raceRegistrationR x.current = some raceId ∧ m.race? raceId = some race ∧
    race.host = host ∧ w.Θ race.host race.token = some resultTy ∧
    HostStack root w m host resultTy tout x.stack ∧ InterruptProvenance x

/-- The outcomes of the walk over a host stack, at its final type: typed code over the remaining
host stack, a scope's exit callback over it, a race registration marker over it, or the exit the
whole stack delivered. `WalkTyped` with host-stack tails and the marker outcome. -/
def HostWalkTyped (root : ProgramSource) (w : World) (m : RState) (host : FiberId) (tout : EffTy) :
    RSaved × Option ExitV → Prop
  | (frame, none) => CodeOk root w m host tout frame ∨ HostCallback root w m host tout frame ∨
      HostMarker root w m host tout frame
  | (_, some ex) => ExitOk w tout ex

/-- **The walk over a host stack is typed.** Delivering a typed exit to a host stack installs typed
code, a scope's exit callback or a race's registration marker over a typed remaining host stack, or
completes with an exit typed at the stack's final type. An ordinary frame is the ordinary walk on
the singleton stack (`popR_typed`), its remaining stack appended to the host tail; a registration
arrow installs its race's marker on a success and passes a failure at the race token's type
(`RegistrationArrow.skip`). The hook laws are needed at the walk's own world only. -/
theorem popR_hostTyped (root : ProgramSource) (interp : RInterp) (w : World) (m : RState)
    (host : FiberId) (laws : HookLawsAt root interp (frameProtocols root) w) {tin tout : EffTy}
    {stack : List ScopeFrame} (hstack : HostStack root w m host tin tout stack) :
    ∀ (ex : ExitV) (frame : RSaved), ExitOk w tin ex → InterruptProvenance frame →
      HostWalkTyped root w m host tout (popR interp ex stack frame) := by
  induction hstack with
  | nil ty =>
    intro ex frame hex _
    exact hex
  | @cons a b c slot rest edge tail ih =>
    intro ex frame hex hp
    rw [popR_cons]
    rcases edge with ordinary | arrow
    · have walk := popR_typed root interp (frameProtocols root) w laws [slot] a b ex frame
        (.cons ordinary (.nil b)) hex hp
      have kept : InterruptProvenance (popR interp ex [slot] frame).1 := by
        obtain ⟨cause, deferred⟩ := popR_interrupts interp ex [slot] frame
        exact ⟨fun c' h => hp.recorded c' (cause ▸ h), fun h => cause ▸ hp.deferred (deferred ▸ h)⟩
      revert walk kept
      generalize popR interp ex [slot] frame = r
      obtain ⟨f, o⟩ := r
      intro walk kept
      cases o with
      | none =>
        rcases walk with ⟨tin', code, st, prov⟩ | ⟨ty, prev, sc, ex', cb, exOk, hook, st, prov⟩
        · exact .inl ⟨tin', code, FramePath.append (hostStack_of_stackAccepts st) tail,
            ⟨prov.recorded, prov.deferred⟩⟩
        · exact .inr (.inl ⟨ty, prev, sc, ex', cb, exOk, hook,
            FramePath.append (hostStack_of_stackAccepts st) tail, ⟨prov.recorded, prov.deferred⟩⟩)
      | some ex' => exact ih ex' f walk kept
    · cases arrow with
      | mk marker skip found hosted token =>
        cases ex with
        | success v =>
          exact .inr (.inr ⟨_, _, _, marker v, found, hosted, token, tail,
            ⟨hp.recorded, hp.deferred⟩⟩)
        | failure cause =>
          obtain ⟨c0, x, i, ic, d⟩ := frame
          cases ic <;> exact ih _ _ (skip w (leHost_refl w) cause hex) ⟨hp.recorded, hp.deferred⟩

/-! ## A delivery to a fiber -/

/-- The walk's exit, read back from a delivery's outcome: `none` while code is installed. -/
def walkExit : Outcome EffName EffThunk Val Err Defect FiberId Ann → Option ExitV
  | .finished exit => some exit
  | _ => none

/-- The iteration a delivery's walk leaves (`deliverR`'s second branch). -/
def walkIter (interp : RInterp) (m : RState) (f : RFiber) (yielding : Bool) (ex : ExitV) : RIter :=
  let (frame, done) := popR interp ex f.frame.stack { f.frame with deferredInterrupt := false }
  ⟨m, { f with frame }, yielding, outcomeOfWalk done, []⟩

/-- The iteration a success with a deferred interrupt leaves (`deliverR`'s first branch). -/
def deferredIter (m : RState) (f : RFiber) (yielding : Bool) : RIter :=
  ⟨m, { f with frame := { f.frame with
    current := .pure (.failure f.frame.pendingCause)
    deferredInterrupt := false } }, yielding, .continue_, []⟩

/-- `deliverR` is one of its two branches. -/
theorem deliverR_cases (interp : RInterp) (m : RState) (f : RFiber) (yielding : Bool) (ex : ExitV) :
    deliverR interp m f yielding ex = walkIter interp m f yielding ex ∨
      deliverR interp m f yielding ex = deferredIter m f yielding := by
  unfold deliverR
  cases ex with
  | success v =>
    dsimp only
    split
    · exact .inr rfl
    · exact .inl rfl
  | failure c => exact .inl rfl

/-- A delivery (`deliverR`) changes only the fiber's frame, nests nothing, keeps the machine and
the yield latch, and ends `continue_` or `finished` with the walk's exit. -/
theorem deliverR_shape (interp : RInterp) (m : RState) (f : RFiber) (yielding : Bool) (ex : ExitV) :
    (deliverR interp m f yielding ex).machine = m ∧ (deliverR interp m f yielding ex).nested = [] ∧
      (deliverR interp m f yielding ex).yielding = yielding ∧
      (deliverR interp m f yielding ex).fiber =
        { f with frame := (deliverR interp m f yielding ex).fiber.frame } ∧
      (deliverR interp m f yielding ex).outcome =
        outcomeOfWalk (walkExit (deliverR interp m f yielding ex).outcome) := by
  rcases deliverR_cases interp m f yielding ex with h | h <;> rw [h]
  · unfold walkIter
    generalize popR interp ex f.frame.stack { f.frame with deferredInterrupt := false } = r
    obtain ⟨frame, o⟩ := r
    cases o <;> exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  · exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- **A delivery through a host stack is typed** (`deliverR`): a success with a deferred interrupt
installs the recorded pending cause as typed code over the unchanged stack; otherwise the walk
from the frame with the deferred flag cleared (`popR_hostTyped`). -/
theorem deliverR_hostTyped (root : ProgramSource) (interp : RInterp) (w : World) (m : RState)
    (laws : HookLawsAt root interp (frameProtocols root) w) (f : RFiber) (yielding : Bool)
    (ex : ExitV) {tin tout : EffTy} (stack : HostStack root w m f.id tin tout f.frame.stack)
    (hex : ExitOk w tin ex) (hp : InterruptProvenance f.frame) :
    HostWalkTyped root w m f.id tout ((deliverR interp m f yielding ex).fiber.frame,
      walkExit (deliverR interp m f yielding ex).outcome) := by
  rcases deliverR_cases interp m f yielding ex with h | h <;> rw [h]
  · have walk := popR_hostTyped root interp w m f.id laws stack ex
      { f.frame with deferredInterrupt := false } hex ⟨hp.recorded, fun h => nomatch h⟩
    unfold walkIter
    revert walk
    generalize popR interp ex f.frame.stack { f.frame with deferredInterrupt := false } = r
    obtain ⟨frame, o⟩ := r
    cases o <;> exact id
  · exact .inl ⟨tin, TypedProg.pure (strongExit_of_clean w tin _ (pendingCause_clean hp)
      (pendingCause_noShapeDefect tin hp)), stack, ⟨hp.recorded, fun h => nomatch h⟩⟩

end Effect4.Program.Typed
