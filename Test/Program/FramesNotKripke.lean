import Effect4.Laws.Program.Typed.Assembly
import Effect4.Laws.Machine.StoresLaws

/-!
# Test.Program.FramesNotKripke — saved frames typed at one world (`E4-TYPED-CE-012`)

The saved-stack judgment typed a frame's continuation only on exits that fit at the one world
the stack was checked at. A step that allocates moves the typed state to a later world, and an
exit that names the new handle then reaches a continuation nobody typed. Formal pass
2026-10-01: seat ALGEBRA's `P2KripkeTyping.lean` (the judgment), its verifier's
`verify-StepLoop.lean` (the step) and `verify-WrapWalk.lean` (wrapping), ported to the merged
tree (`docs/research/2026-10-01-landing/ports-at-dceae006/`). Repaired by decisions row 135:
`Contracts.FrameAccepts` and the hook protocols are closed under later worlds.

The refutations are historical controls over `Old`, a local copy of the one-world frame
clauses (`FrameAccepts`, `StackAccepts`, `SavedOk`, `HookLaws`) and of the typed state's two
saved-stack clauses built on them. Everything else in `Old.TypedState` is the current
judgment (H1's scheduler and observer facts, H2's `ExitOk`, `CodeInert`): this retains the
one-world omission, not a complete pre-amendment model; the original statement is checked at
`eb3ab9a9` and in the research ports.

1. `stackAccepts_not_mono` (historical): the frame `.answer badNext`, whose continuation
   answers `"x"` on every success, is accepted at the initial world (no success fits
   `refOf nat` there) and refused at the later world `w1` that declares cell 0 at `nat`.
2. `step_loop_refuted` (historical): the loaded `Ref.make(5)` with that frame under the running
   root is an `Old` typed state with `[loop root]` queued; one `loop` allocates cell 0 and no
   world types the result.
3. `evaluate_keeps` (historical control): `evaluate` allocates nothing; on the same idle
   machine it keeps the `Old` typed state at the same world. The breaking command is `loop`.
4. The repair: the closed judgment refuses the bad frame at the initial world
   (`bad_not_kripke_initial`), transports along the host order (`stackAccepts_mono`, landed
   in `Contracts`), and gives the one-world judgment at the current world
   (`stackAccepts_now`), so nothing proved over the one-world judgment is lost.
5. `step_loop_good` (green, current judgment): with a frame typed into `unit` on every success,
   the same `loop` keeps the typed configuration (row 134's `I`: `good_config` before,
   `afterGood_config` after) at the world that declares the new cell.
6. Wrapping does not survive the walk (red): under hooks whose iterator protocol picks its
   input type per world, the one-world hook laws hold (`hookLawsX_old`) and the one-world walk
   types the output (`output_typed_one_world`), but no world-closed typing of the output exists
   (`output_not_kripke`), and the current `HookLaws`, which hand a resumed protocol back at
   every later world, refuse these hooks (`hookLawsX_refused`).
-/

set_option autoImplicit false
set_option maxRecDepth 8192

namespace Test.Program.FramesNotKripke
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Sched Effect4.Program.Denote
open Effect4.Program.Typed Effect4.Laws.Effects Contracts

abbrev W := Effect4.Program.Typed.World

def refProg : NativeEff := .perform .refMake (.lit (.nat 5))

/-- Answers `"x"` (not a `unit`) on every success; passes failures on. -/
def badNext : ExitV → RProgram
  | .success _ => .pure (.success (Val.str "x"))
  | .failure c => .pure (.failure c)

/-- Answers `unit` on every success; passes failures on. -/
def goodNext : ExitV → RProgram
  | .success _ => .pure (.success Val.unit)
  | .failure c => .pure (.failure c)

abbrev tin : EffTy := EffTy.pure (.refOf .nat)
abbrev unitTy : EffTy := EffTy.pure .unit
abbrev world : W := initialWorld unitTy

/-- The initial world with cell 0 allocated at `nat` (not claimed valid for any machine). -/
def s1 : Stores := { Stores.empty with refs := [Val.nat 0] }

def w1 : W := { world with state := s1, Ρ := fun k => if k = ⟨0⟩ then some .nat else none }

theorem w0_le_w1 : world.leHost w1 := by
  have hst : Stores.le world.state w1.state :=
    ⟨Nat.zero_le _, Nat.le_refl _, fun _ h => h, Nat.le_refl _, fun _ h => h, Nat.le_refl _⟩
  have hrho : TableExtends world.Ρ w1.Ρ := fun _ _ h => by cases h
  have hcells : CellCompatible world w1 := by
    unfold CellCompatible
    refine ⟨fun _ _ h => ?_, fun _ _ h => ?_⟩
    · unfold HeapTypedAt at h
      cases h.1
    · unfold PromiseTypedAt at h
      cases h.1
  exact ⟨⟨⟨fun _ h => h, hst⟩, fun _ _ h => h, fun _ _ h => h, hrho, hcells,
    fun _ _ _ h => h, rfl⟩, fun _ _ h => h⟩

theorem cell0_ok_w1 : ExitOk w1 tin (.success (Val.cell ⟨0⟩)) := by
  refine ⟨?_, trivial⟩
  rw [fitsExit_success_iff]
  change Typed.Fits w1 (Val.cell ⟨0⟩) (.refOf .nat)
  simp only [Typed.Fits]
  exact ⟨.nat, by simp only [w1, if_pos], Ty.sub_refl _, Ty.sub_refl _⟩

/-! ## The one-world judgment, kept local -/

namespace Old

section
variable (TypedProg : W → EffTy → RProgram → Prop) (Exits : W → EffTy → ExitV → Prop)
  (hooks : FrameProtocols)

/-- `Contracts.FrameAccepts` before row 135: every clause read at the one world `w`. -/
inductive FrameAccepts (w : W) : EffTy → EffTy → ScopeFrame → Prop
  | resume {tin tout : EffTy} (kind : GuardKind) (next : ExitV → RProgram)
      (run : ∀ ex, Exits w tin ex → kind.hasExitArm ex = true → TypedProg w tout (next ex))
      (skip : ∀ ex, Exits w tin ex → kind.hasExitArm ex = false → Exits w tout ex) :
      FrameAccepts w tin tout (.resume kind next)
  | answer {tin tout : EffTy} (next : ExitV → RProgram)
      (run : ∀ ex, Exits w tin ex → TypedProg w tout (next ex)) :
      FrameAccepts w tin tout (.answer next)
  | restoreMask (ty : EffTy) (flag : Bool) : FrameAccepts w ty ty (.restoreMask flag)
  | asyncFinalizer {tin tout : EffTy} (name : EffName)
      (protocol : hooks.asyncFinalizer w tin tout name) :
      FrameAccepts w tin tout (.asyncFinalizer name)
  | finalizerMask (ty : EffTy) (flag : Bool) : FrameAccepts w ty ty (.finalizerMask flag)
  | iter {tin tout : EffTy} (name : EffName) (protocol : hooks.iterator w tin tout name) :
      FrameAccepts w tin tout (.iter name)
  | loop {tin tout : EffTy} (name : EffName) (cursor : Val)
      (protocol : hooks.loop w tin tout name cursor) : FrameAccepts w tin tout (.loop name cursor)

inductive StackAccepts (w : W) : EffTy → EffTy → List ScopeFrame → Prop
  | nil (ty : EffTy) : StackAccepts w ty ty []
  | cons {tin middle tout : EffTy} {frame : ScopeFrame} {rest : List ScopeFrame}
      (head : FrameAccepts TypedProg Exits hooks w tin middle frame)
      (tail : StackAccepts w middle tout rest) : StackAccepts w tin tout (frame :: rest)

def SavedOk (w : W) (final : EffTy) (x : RSaved) : Prop :=
  ∃ tin, TypedProg w tin x.current ∧ StackAccepts TypedProg Exits hooks w tin final x.stack ∧
    InterruptProvenance x

end

/-- The one-world hook laws: a resumed protocol at the one world only. -/
structure HookLaws (root : ProgramSource) (interp : RInterp) (hooks : FrameProtocols) : Prop where
  asyncFinalizer : ∀ w tin tout name, hooks.asyncFinalizer w tin tout name →
    tin = tout ∧ ∀ cause, ExitOk w tin (.failure cause) → cause.hasInterrupts = true →
      TypedProg root w tout (interp.cancelThenFail name cause)
  iterator : ∀ w tin tout name, hooks.iterator w tin tout name →
    tin.error = tout.error ∧ ∀ v, Fits w v tin.answer →
      match (interp.iterNext name v).2 with
      | .done result => ExitOk w tout (.success result)
      | .halt cause => ExitOk w tout (.failure cause)
      | .resume code name' => ∃ tin', TypedProg root w tin' code ∧ hooks.iterator w tin' tout name'
  loop : ∀ w tin tout name cursor, hooks.loop w tin tout name cursor →
    tin.error = tout.error ∧ ∀ v, Fits w v tin.answer →
      match interp.loopResume name cursor v with
      | .continue cursor' body => ∃ tin', TypedProg root w tin' body ∧
          hooks.loop w tin' tout name cursor'
      | .finish code => TypedProg root w tout code

/-- `TerminalFiber`, `TerminalPosition` and `CodeInert` as of `bb269fde` (H1's halt extension
included), kept local so this historical copy does not follow later restatements. -/
def TerminalFiber (m : RState) (commands : List RCmd) (id : FiberId) : Prop :=
  (∃ exit, .finish id exit ∈ commands) ∨ ∃ fiber ∈ m.fibers, fiber.id = id ∧ fiber.exit.isSome = true

def TerminalPosition (m : RState) (commands : List RCmd) : Expect → Prop
  | .root => TerminalFiber m commands Api.root
  | .fiber id => TerminalFiber m commands id
  | .hook _ => False

def CodeInert (m : RState) (commands : List RCmd) (position : Expect) : Prop :=
  m.stuck.isSome = true ∨ TerminalPosition m commands position

/-- The typed state's saved position over the one-world stack. -/
def SavedPosition (root : ProgramSource) (w : W) (m : RState) (commands : List RCmd)
    (position : Expect) (final : EffTy) (saved : RSaved) : Prop :=
  ∃ tin, (¬ Old.CodeInert m commands position → TypedProg root w tin saved.current) ∧
    StackAccepts (TypedProg root) ExitOk (frameProtocols root) w tin final saved.stack ∧
    InterruptProvenance saved

def statePreds (root : ProgramSource) (m : RState) (commands : List RCmd) : Preds W :=
  { preds root with
    SavedOk := fun w position saved => ∀ ty, expectOf w position = some ty →
      SavedPosition root w m commands position ty saved }

def ActiveDelivery (root : ProgramSource) (w : W) (m : RState) : Prop :=
  ∀ f ∈ m.fibers, ∀ token, f.parked = .withGuard token →
    ∃ tin final, w.Θ f.id token = some tin ∧ w.Γ f.id = some final ∧
      StackAccepts (TypedProg root) ExitOk (frameProtocols root) w tin final f.frame.stack ∧
      InterruptProvenance f.frame

def TypedState (root : ProgramSource) (rootTy : EffTy) (w : W) (m : RState)
    (commands : List RCmd := []) : Prop :=
  WorldValid rootTy w m ∧ RStateOk (statePreds root m commands) w m ∧
    ActiveDelivery root w m ∧ SchedulerState m ∧ ObserverState root w m ∧ RegistrationState root w m

def StepPreserves (root : ProgramSource) (rootTy : EffTy) (cmd : RCmd) : Prop :=
  ∀ w m rest, m.stuck = none → TypedState root rootTy w m (cmd :: rest) →
    QueueOk root w m (cmd :: rest) →
    let r := (letI := termEvaluatorFor root.program
              driveStep (interpR root.program) m cmd rest)
    ∃ w', w.leHost w' ∧ TypedState root rootTy w' r.1 r.2 ∧ QueueOk root w' r.1 r.2

end Old

/-! ## 1. The one-world judgment is not world-monotone -/

/-- At the initial world no cell is declared, so no success fits `refOf nat` and the bad frame
is accepted vacuously; its failure arm passes the failure on. -/
theorem stack_ok :
    Old.StackAccepts (TypedProg (refProg : ProgramSource)) ExitOk (frameProtocols refProg) world
      tin unitTy [.answer badNext] := by
  refine .cons (.answer badNext fun ex hex => ?_) (.nil unitTy)
  cases ex with
  | success v =>
    exfalso
    have hf := hex.1
    rw [fitsExit_success_iff] at hf
    change Typed.Fits world v (.refOf .nat) at hf
    simp only [Typed.Fits] at hf
    split at hf
    · obtain ⟨t', ht, _⟩ := hf
      cases ht
    · exact hf
  | failure c =>
    refine .pure ⟨?_, hex.2⟩
    have hf := hex.1
    rw [fitsExit_failure_iff] at hf ⊢
    exact hf

theorem bad_refused_at_w1 :
    ¬ Old.StackAccepts (TypedProg (refProg : ProgramSource)) ExitOk (frameProtocols refProg) w1 tin
      unitTy [.answer badNext] := by
  intro h
  cases h with
  | cons head tail =>
    cases tail
    cases head with
    | answer next run =>
      have hp := (TypedProg.pure_inv (run (.success (Val.cell ⟨0⟩)) cell0_ok_w1)).1
      rw [fitsExit_success_iff] at hp
      change Typed.Fits w1 (Val.str "x") .unit at hp
      simp only [Typed.Fits] at hp

/-- **World weakening fails for the one-world saved-stack judgment** (`E4-TYPED-CE-012`, the
judgment; historical). -/
theorem stackAccepts_not_mono :
    ∃ (w w' : W) (a b : EffTy) (s : List ScopeFrame), w.leHost w' ∧
      Old.StackAccepts (TypedProg (refProg : ProgramSource)) ExitOk (frameProtocols refProg) w a b s ∧
      ¬ Old.StackAccepts (TypedProg (refProg : ProgramSource)) ExitOk (frameProtocols refProg)
        w' a b s :=
  ⟨world, w1, tin, unitTy, [.answer badNext], w0_le_w1, stack_ok, bad_refused_at_w1⟩

/-! ## 2. The step: one allocating `loop` leaves a machine no world types -/

def current : RProgram := denoteR refProg refProg (rootPoint 20)

/-- The root fiber running `Ref.make(5)` over the stack `s`. -/
def rootFiber (s : List ScopeFrame) (running : Bool) : RFiber :=
  { RunFiber.make Api.root current true (stores.budgetOf emptyCtx) emptyCtx with
    running := running
    frame := { current := current
               stack := s
               interruptible := true
               interruptedCause := none
               deferredInterrupt := false } }

/-- A one-fiber machine over the loaded program; the trace is a parameter so the machine
`evaluate` leaves (one more event) is one of the family. -/
def machineOf (s : List ScopeFrame) (running : Bool)
    (trace := (loadR refProg 20 20).trace) : RState :=
  { loadR refProg 20 20 with fibers := [rootFiber s running], trace := trace }

/-- The bad machine: the running root over `.answer badNext`. -/
abbrev machine : RState := machineOf [.answer badNext] true

theorem valid_of (s : List ScopeFrame) (running : Bool) (trace := (loadR refProg 20 20).trace) :
    WorldValid unitTy world (machineOf s running trace) := by
  have old := initial_world_valid unitTy refProg 20 20 ⟨rfl, rfl⟩
  refine {
    ids := old.ids, fibers := old.fibers, heap := old.heap, promises := old.promises,
    tokens := ?_, tokenBound := old.tokenBound, tokenTargets := old.tokenTargets,
    state := old.state, wf := old.wf, cells := old.cells, fiberClosed := old.fiberClosed,
    heapClosed := old.heapClosed, promiseClosed := old.promiseClosed,
    tokenClosed := old.tokenClosed, root := old.root,
    timers := WakeTyped.empty _ _, waiters := fun _ _ h => by cases h }
  intro f hf token hp
  change f ∈ [rootFiber s running] at hf
  rw [List.mem_singleton] at hf
  subst f
  cases hp

theorem no_requests_of (s : List ScopeFrame) (running : Bool) (trace := (loadR refProg 20 20).trace)
    (id : FiberId) (token : Nat) : requestOfR (machineOf s running trace) id token = none := by
  unfold requestOfR
  cases hf : (machineOf s running trace).fiber? id with
  | none => rfl
  | some found =>
    have member := List.mem_of_find?_eq_some hf
    change found ∈ [rootFiber s running] at member
    rw [List.mem_singleton] at member
    subst found
    rfl

theorem scheduler_of (s : List ScopeFrame) (running : Bool) (trace := (loadR refProg 20 20).trace) :
    SchedulerState (machineOf s running trace) := by
  constructor
  · exact List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩
  · intro f hf
    change f ∈ [rootFiber s running] at hf
    rw [List.mem_singleton] at hf
    subst f
    exact Nat.zero_lt_succ 0
  · exact List.nodup_nil
  · intro race member; cases member
  · intro race member; cases member
  · intro key member; cases member
  · intro id token request hr
    rw [no_requests_of s running trace] at hr
    cases hr
  · intro id token request hr
    rw [no_requests_of s running trace] at hr
    cases hr
  · intro f hf
    change f ∈ [rootFiber s running] at hf
    rw [List.mem_singleton] at hf
    subst f
    rfl
  · intro f hf hp
    change f ∈ [rootFiber s running] at hf
    rw [List.mem_singleton] at hf
    subst f
    exact False.elim (hp rfl)
  · intro f hf token hp
    change f ∈ [rootFiber s running] at hf
    rw [List.mem_singleton] at hf
    subst f
    cases hp
  · intro f hf hx
    change f ∈ [rootFiber s running] at hf
    rw [List.mem_singleton] at hf
    subst f
    cases hx
  · intro f hf hx
    change f ∈ [rootFiber s running] at hf
    rw [List.mem_singleton] at hf
    subst f
    cases hx
  · intro f hf hd
    change f ∈ [rootFiber s running] at hf
    rw [List.mem_singleton] at hf
    subst f
    cases hd
  · intro raceId race hr; cases hr
  · intro raceId race hr; cases hr
  · intro f hf p hp
    change f ∈ [rootFiber s running] at hf
    rw [List.mem_singleton] at hf
    subst f
    cases hp
  · intro f hf o ho
    change f ∈ [rootFiber s running] at hf
    rw [List.mem_singleton] at hf
    subst f
    cases ho

theorem observers_of (s : List ScopeFrame) (running : Bool) (trace := (loadR refProg 20 20).trace) :
    ObserverState (refProg : ProgramSource) world (machineOf s running trace) := by
  constructor
  · intro f hf p hp
    change f ∈ [rootFiber s running] at hf
    rw [List.mem_singleton] at hf
    subst f
    cases hp
  · intro f hf o ho
    change f ∈ [rootFiber s running] at hf
    rw [List.mem_singleton] at hf
    subst f
    cases ho

theorem registration_of (s : List ScopeFrame) (running : Bool) (trace := (loadR refProg 20 20).trace) :
    RegistrationState (refProg : ProgramSource) world (machineOf s running trace) := by
  intro f hf id marker
  change f ∈ [rootFiber s running] at hf
  rw [List.mem_singleton] at hf
  subst f
  change none = some id at marker
  cases marker

theorem code_typed (w : W) :
    TypedProg (refProg : ProgramSource) w tin current := by
  refine TypedProg.store (cert := Ty.nat) ⟨rfl, trivial⟩ ?_
  intro w' _ ans hpost
  obtain ⟨key, rfl, hs⟩ := hpost
  refine TypedProg.pure ⟨?_, trivial⟩
  rw [fitsExit_success_iff]
  change Typed.Fits w' (Val.cell key) (.refOf .nat)
  simp only [Typed.Fits]
  exact ⟨.nat, hs, Ty.sub_refl _, Ty.sub_refl _⟩

/-- A one-fiber machine whose root's saved frame is typed is a typed state (row 134's
`TypedState` reads no queue; the code is `LiveCode`'s or `ReadCode`'s, below). -/
theorem typed_of (s : List ScopeFrame) (running : Bool)
    (saved : SavedOk (TypedProg (refProg : ProgramSource)) ExitOk
      (frameProtocols (refProg : ProgramSource)) world unitTy (rootFiber s running).frame)
    (trace := (loadR refProg 20 20).trace) :
    TypedState (refProg : ProgramSource) unitTy world (machineOf s running trace) := by
  refine ⟨valid_of s running trace, ⟨?_, ?_, ?_⟩, ?_, scheduler_of s running trace,
    observers_of s running trace, registration_of s running trace⟩
  · intro f hf
    change f ∈ [rootFiber s running] at hf
    rw [List.mem_singleton] at hf
    subst f
    refine ⟨⟨?_⟩, ?_, ?_, ?_, ⟨?_⟩, ?_⟩
    · intro ty declared
      change world.Γ Api.root = some ty at declared
      rw [(valid_of s running trace).root] at declared
      cases declared
      exact savedPosition_of_saved _ _ _ _ saved
    · intro p hp; cases hp
    · intro v hv; cases hv
    · intro v hv; cases hv
    · intro v hv; cases hv
    · intro key value ty lookup
      change (Env.Context.empty : Env.Ctx).getV key = some value at lookup
      rw [Env.Context.getV_empty] at lookup
      cases lookup
  · intro race member; cases member
  · refine ⟨⟨(fun o ho => nomatch ho), (fun _ hp => nomatch hp)⟩, (fun i v h => nomatch h), ⟨(fun i v h => nomatch h)⟩,
      ⟨(fun v hv => nomatch hv)⟩, (fun v hv => nomatch hv), trivial⟩
  · intro f hf token hp
    change f ∈ [rootFiber s running] at hf
    rw [List.mem_singleton] at hf
    subst f
    cases hp

/-- The same over the one-world judgment. -/
theorem old_typed_of (s : List ScopeFrame) (running : Bool) (commands : List RCmd)
    (saved : Old.SavedOk (TypedProg (refProg : ProgramSource)) ExitOk
      (frameProtocols (refProg : ProgramSource)) world unitTy (rootFiber s running).frame)
    (trace := (loadR refProg 20 20).trace) :
    Old.TypedState (refProg : ProgramSource) unitTy world (machineOf s running trace) commands := by
  refine ⟨valid_of s running trace, ⟨?_, ?_, ?_⟩, ?_, scheduler_of s running trace,
    observers_of s running trace, registration_of s running trace⟩
  · intro f hf
    change f ∈ [rootFiber s running] at hf
    rw [List.mem_singleton] at hf
    subst f
    refine ⟨⟨?_⟩, ?_, ?_, ?_, ⟨?_⟩, ?_⟩
    · intro ty declared
      change world.Γ Api.root = some ty at declared
      rw [(valid_of s running trace).root] at declared
      cases declared
      obtain ⟨tin, code, stack, provenance⟩ := saved
      exact ⟨tin, fun _ => code, stack, provenance⟩
    · intro p hp; cases hp
    · intro v hv; cases hv
    · intro v hv; cases hv
    · intro v hv; cases hv
    · intro key value ty lookup
      change (Env.Context.empty : Env.Ctx).getV key = some value at lookup
      rw [Env.Context.getV_empty] at lookup
      cases lookup
  · intro race member; cases member
  · refine ⟨⟨(fun o ho => nomatch ho), (fun _ hp => nomatch hp)⟩, (fun i v h => nomatch h), ⟨(fun i v h => nomatch h)⟩,
      ⟨(fun v hv => nomatch hv)⟩, (fun v hv => nomatch hv), trivial⟩
  · intro f hf token hp
    change f ∈ [rootFiber s running] at hf
    rw [List.mem_singleton] at hf
    subst f
    cases hp

theorem saved_typed (running : Bool) : Old.SavedOk (TypedProg (refProg : ProgramSource)) ExitOk
    (frameProtocols (refProg : ProgramSource)) world unitTy (rootFiber [.answer badNext] running).frame :=
  ⟨tin, code_typed world, stack_ok, ⟨(fun _ h => nomatch h), (fun h => nomatch h)⟩⟩

def command : RCmd := .loop Api.root false

theorem typed : Old.TypedState (refProg : ProgramSource) unitTy world machine [command] :=
  old_typed_of _ _ _ (saved_typed true)

/-- A queue of one `loop` (or `deliver`) of the running root is admitted. -/
theorem queue_of (s : List ScopeFrame) (c : RCmd)
    (hc : c = .loop Api.root false ∨ c = .deliver Api.root false)
    (trace := (loadR refProg 20 20).trace) :
    QueueOk (refProg : ProgramSource) world (machineOf s true trace) [c] := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ⟨?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  · intro c' hc'
    rw [List.mem_singleton] at hc'
    subst c'
    rcases hc with rfl | rfl <;> trivial
  · intro c' hc'
    rw [List.mem_singleton] at hc'
    subst c'
    rcases hc with rfl | rfl <;> exact ⟨rootFiber s true, rfl, rfl, rfl⟩
  · intro c' hc'
    rw [List.mem_singleton] at hc'
    subst c'
    rcases hc with rfl | rfl <;> trivial
  · rcases hc with rfl | rfl <;> exact List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩
  · rcases hc with rfl | rfl <;> exact ⟨trivial, trivial⟩
  · intro key member
    rcases hc with rfl | rfl <;> cases member
  · intro id token request hr
    rw [no_requests_of s true trace] at hr
    cases hr
  · intro source exit observer member
    rw [List.mem_singleton] at member
    rcases hc with rfl | rfl <;> cases member
  · intro race child member
    rw [List.mem_singleton] at member
    rcases hc with rfl | rfl <;> cases member
  · intro host yielding race member
    rw [List.mem_singleton] at member
    rcases hc with rfl | rfl <;> cases member
  -- row 139's `links`: vacuous, the queue holds no `link`
  · intro mode scope target interruptor extra member
    rw [List.mem_singleton] at member
    rcases hc with rfl | rfl <;> cases member
  -- row 134 (d)'s queued observers: vacuous, the queue holds no `observe`
  · intro source exit observer member
    rw [List.mem_singleton] at member
    rcases hc with rfl | rfl <;> cases member

theorem queue : QueueOk (refProg : ProgramSource) world machine [command] :=
  queue_of _ _ (Or.inl rfl)

theorem stuck_none : machine.stuck = none := rfl

/-- The machine and queue after one `loop` of the root, exactly as `StepPreserves` names them. -/
def result : RState × List RCmd :=
  letI := termEvaluatorFor (refProg : ProgramSource).program
  driveStep (interpR (refProg : ProgramSource).program) machine command []

def isFinishOf (id : FiberId) : RCmd → Bool
  | .finish target _ => target == id
  | _ => false

theorem result_fiber : ∃ f ∈ result.1.fibers, f.id = Api.root ∧ f.exit = none ∧
    f.frame.current = .pure (.success (Val.cell ⟨0⟩)) ∧ f.frame.stack = [.answer badNext] :=
  ⟨_, List.Mem.head _, rfl, rfl, rfl, rfl⟩

theorem result_stuck : result.1.stuck = none := rfl

theorem result_no_finish : result.2.all (fun c => !isFinishOf Api.root c) = true := by
  decide +kernel

theorem result_only_root : ∀ f ∈ result.1.fibers, f.id = Api.root ∧ f.exit = none := by
  intro f hf
  change f ∈ [_] at hf
  rw [List.mem_singleton] at hf
  subst hf
  exact ⟨rfl, rfl⟩

theorem result_not_inert : ¬ Old.CodeInert result.1 result.2 (.fiber Api.root) := by
  intro h
  rcases h with hs | hterm
  · rw [result_stuck] at hs
    exact Bool.noConfusion hs
  · rcases hterm with ⟨ex, hmem⟩ | ⟨fb, hfb, _, hex⟩
    · have hall := List.all_eq_true.mp result_no_finish _ hmem
      have hit : isFinishOf Api.root (.finish Api.root ex) = true := beq_self_eq_true _
      rw [hit] at hall
      exact Bool.noConfusion hall
    · rw [(result_only_root fb hfb).2] at hex
      exact Bool.noConfusion hex

/-- **No world types the machine after the allocating `loop`** (one-world judgment). -/
theorem post_untyped (w : W) :
    ¬ Old.TypedState (refProg : ProgramSource) unitTy w result.1 result.2 := by
  intro h
  obtain ⟨f, hf, hid, _, hcur, hst⟩ := result_fiber
  have hroot : expectOf w (.fiber f.id) = some unitTy := by
    rw [hid]
    exact h.1.root
  obtain ⟨tin', hprog0, hstack, _⟩ := (h.2.1.c0 f hf).c0.c0 _ hroot
  have hni : ¬ Old.CodeInert result.1 result.2 (.fiber f.id) := by
    rw [hid]
    exact result_not_inert
  have hprog := hprog0 hni
  rw [hcur] at hprog
  rw [hst] at hstack
  have hex := TypedProg.pure_inv hprog
  cases hstack with
  | cons head tail =>
    cases tail
    cases head with
    | answer next run =>
      have hp := (TypedProg.pure_inv (run _ hex)).1
      rw [fitsExit_success_iff] at hp
      change Typed.Fits w (Val.str "x") .unit at hp
      simp only [Typed.Fits] at hp

/-- **The declared `M6Ledger.step_loop` proposition, over the one-world judgment, is false at
this instance** (`E4-TYPED-CE-012`, the step; historical). -/
theorem step_loop_refuted :
    ¬ Old.StepPreserves (refProg : ProgramSource) unitTy (.loop Api.root false) := by
  intro h
  obtain ⟨w', _, ht, _⟩ := h world machine [] stuck_none typed queue
  exact post_untyped w' ht

/-! ## 3. Control: `evaluate` allocates nothing and keeps the bad machine typed -/

/-- The bad machine before the root starts. -/
abbrev idle : RState := machineOf [.answer badNext] false

def evaluateCmd : RCmd := .evaluate Api.root

theorem idle_typed : Old.TypedState (refProg : ProgramSource) unitTy world idle [evaluateCmd] :=
  old_typed_of _ _ _ (saved_typed false)

def afterEval : RState × List RCmd :=
  letI := termEvaluatorFor (refProg : ProgramSource).program
  driveStep (interpR (refProg : ProgramSource).program) idle evaluateCmd []

/-- `evaluate` marks the root running and queues its `loop` (`Machine/Fibers.lean:1849-1856`). -/
theorem afterEval_queue : afterEval.2 = [.loop Api.root false] := rfl

/-- The started machine is the running member of the family, with one more trace event. -/
theorem afterEval_machine : afterEval.1 = machineOf [.answer badNext] true afterEval.1.trace := rfl

theorem afterEval_typed :
    Old.TypedState (refProg : ProgramSource) unitTy world afterEval.1 afterEval.2 := by
  rw [afterEval_queue, afterEval_machine]
  exact old_typed_of _ _ _ (saved_typed true) _

theorem afterEval_queueOk :
    QueueOk (refProg : ProgramSource) world afterEval.1 afterEval.2 := by
  rw [afterEval_queue, afterEval_machine]
  exact queue_of _ _ (Or.inl rfl) _

/-- **Control: on the same bad machine, `evaluate` keeps the one-world typed state, at the same
world.** The allocation is `loop`'s (`EvaluateR.lean:297-305`), so ALG-01's example command
(`step_evaluate`) was the wrong one (historical). -/
theorem evaluate_keeps :
    ∃ w', world.leHost w' ∧
      Old.TypedState (refProg : ProgramSource) unitTy w' afterEval.1 afterEval.2 ∧
      QueueOk (refProg : ProgramSource) w' afterEval.1 afterEval.2 :=
  ⟨world, leHost_refl world, afterEval_typed, afterEval_queueOk⟩

/-! ## 4. Green control: the same `loop` with a frame typed into `unit` keeps the state typed -/

theorem stack_good (w : W) :
    StackAccepts (TypedProg (refProg : ProgramSource)) ExitOk (frameProtocols refProg) w tin unitTy
      [.answer goodNext] := by
  refine .cons (.answer goodNext fun _ _ ex hex => ?_) (.nil unitTy)
  cases ex with
  | success v => exact .pure ⟨trivial, trivial⟩
  | failure c =>
    refine .pure ⟨?_, hex.2⟩
    have hf := hex.1
    rw [fitsExit_failure_iff] at hf ⊢
    exact hf

abbrev good : RState := machineOf [.answer goodNext] true

theorem good_saved (w : W) : SavedOk (TypedProg (refProg : ProgramSource)) ExitOk
    (frameProtocols (refProg : ProgramSource)) w unitTy (rootFiber [.answer goodNext] true).frame :=
  ⟨tin, code_typed w, stack_good w, ⟨(fun _ h => nomatch h), (fun h => nomatch h)⟩⟩

theorem good_typed : TypedState (refProg : ProgramSource) unitTy world good :=
  typed_of _ _ (good_saved world)

theorem good_queue : QueueOk (refProg : ProgramSource) world good [command] :=
  queue_of _ _ (Or.inl rfl)

/-- The input of the green control in the typed configuration (row 134's `I`): the running
root's code, which the queued `loop` reads, is typed with its stack (`ReadCode`). Before the
split this was the code clause of `TypedState … [command]`. -/
theorem good_config : ConfigTyped (refProg : ProgramSource) unitTy world good [command] := by
  refine ⟨⟨good_typed, rfl, ?_, machineLive_of_quiet _ rfl rfl⟩, ?_, good_queue⟩
  · intro f hf _ idle
    change f ∈ [rootFiber [.answer goodNext] true] at hf
    rw [List.mem_singleton] at hf
    subst f
    cases idle
  · intro f hf _ _ _ ty declared
    change f ∈ [rootFiber [.answer goodNext] true] at hf
    rw [List.mem_singleton] at hf
    subst f
    change world.Γ Api.root = some ty at declared
    rw [(valid_of [.answer goodNext] true).root] at declared
    cases declared
    exact good_saved world

def afterGood : RState × List RCmd :=
  letI := termEvaluatorFor (refProg : ProgramSource).program
  driveStep (interpR (refProg : ProgramSource).program) good command []

/-- `loop` ran the store operation and left the root's delivery queued after the due drain. -/
theorem afterGood_queue : afterGood.2 = [.drainDue, .deliver Api.root false] := rfl

theorem afterGood_step :
    syncOpStep (.refMake (Val.nat 5)) Stores.empty = some (afterGood.1.state, Val.cell ⟨0⟩) := rfl

/-- The world after the allocation: cell 0 declared at `nat` over the machine's new stores. -/
def w1g : W := world.addRef afterGood.1.state ⟨0⟩ .nat

theorem rho_w1g (key : RefKey) :
    w1g.Ρ key = if key = ⟨0⟩ then some Ty.nat else none := rfl

theorem w0_le_w1g : world.leHost w1g := by
  have hst : Stores.le world.state w1g.state :=
    ⟨Nat.zero_le _, Nat.le_refl _, fun _ h => h, Nat.le_refl _, fun _ h => h, Nat.le_refl _⟩
  have hrho : TableExtends world.Ρ w1g.Ρ := insert_extends _ _ _ rfl
  have hcells : CellCompatible world w1g := by
    unfold CellCompatible
    refine ⟨fun _ _ h => ?_, fun _ _ h => ?_⟩
    · unfold HeapTypedAt at h
      cases h.1
    · unfold PromiseTypedAt at h
      cases h.1
  exact ⟨⟨⟨fun _ h => h, hst⟩, fun _ _ h => h, fun _ _ h => h, hrho, hcells,
    fun _ _ _ h => h, rfl⟩, fun _ _ h => h⟩

theorem valid_w1g : WorldValid unitTy w1g afterGood.1 := by
  have v0 := initial_world_valid unitTy refProg 20 20 ⟨rfl, rfl⟩
  have hids : afterGood.1.fibers.map (·.id) = (loadR refProg 20 20).fibers.map (·.id) := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl, ?_, ⟨?_, ?_⟩, v0.fiberClosed, ?_, v0.promiseClosed,
    v0.tokenClosed, v0.root, WakeTyped.empty _ _, fun _ _ h => by cases h⟩
  · rw [hids]
    exact v0.ids
  · intro id
    rw [hids]
    exact v0.fibers id
  · intro key
    rw [rho_w1g]
    change _ ↔ key.index < 1
    by_cases hk : key = ⟨0⟩
    · rw [if_pos hk, hk]
      exact ⟨fun _ => Nat.zero_lt_one, fun _ => rfl⟩
    · rw [if_neg hk]
      refine ⟨fun h => Bool.noConfusion h, fun hlt => ?_⟩
      exfalso
      apply hk
      cases key with
      | mk i =>
        change i < 1 at hlt
        have hi : i = 0 := by omega
        rw [hi]
  · intro key
    change false = true ↔ key.index < 0
    exact ⟨fun h => Bool.noConfusion h, fun h => False.elim (Nat.not_lt_zero _ h)⟩
  · intro f hf token hp
    change f ∈ [_] at hf
    rw [List.mem_singleton] at hf
    subst hf
    cases hp
  · intro id token ty h
    cases h
  · intro id token ty h
    cases h
  · exact syncOpStep_wf _ _ _ _ Stores.empty_wf rfl afterGood_step
  · intro i v hv
    intro ty hty
    cases i with
    | zero =>
      change some (Val.nat 5) = some v at hv
      cases hv
      rw [rho_w1g, if_pos rfl] at hty
      cases hty
      rfl
    | succ j =>
      change none = some v at hv
      cases hv
  · intro i v hv
    cases hv
  · intro key ty h
    rw [rho_w1g] at h
    by_cases hk : key = ⟨0⟩
    · rw [if_pos hk] at h
      cases h
      rfl
    · rw [if_neg hk] at h
      cases h

theorem cell0_ok_w1g : ExitOk w1g tin (.success (Val.cell ⟨0⟩)) := by
  refine ⟨?_, trivial⟩
  rw [fitsExit_success_iff]
  change Typed.Fits w1g (Val.cell ⟨0⟩) (.refOf .nat)
  simp only [Typed.Fits]
  exact ⟨.nat, by rw [rho_w1g, if_pos rfl], Ty.sub_refl _, Ty.sub_refl _⟩

theorem afterGood_no_requests (id : FiberId) (token : Nat) :
    requestOfR afterGood.1 id token = none := by
  unfold requestOfR
  cases hf : afterGood.1.fiber? id with
  | none => rfl
  | some found =>
    have member := List.mem_of_find?_eq_some hf
    change found ∈ [_] at member
    rw [List.mem_singleton] at member
    subst found
    rfl

/-- The root's frame after the allocation, code included, at the world that declares cell 0. -/
theorem afterGood_saved : ∀ f ∈ afterGood.1.fibers, SavedOk (TypedProg (refProg : ProgramSource))
    ExitOk (frameProtocols (refProg : ProgramSource)) w1g unitTy f.frame := by
  intro f hf
  change f ∈ [_] at hf
  rw [List.mem_singleton] at hf
  subst hf
  exact ⟨tin, TypedProg.pure cell0_ok_w1g, stack_good w1g,
    ⟨(fun _ h => nomatch h), (fun h => nomatch h)⟩⟩

theorem afterGood_typed :
    TypedState (refProg : ProgramSource) unitTy w1g afterGood.1 := by
  refine ⟨valid_w1g, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · intro f hf
    have saved := afterGood_saved f hf
    change f ∈ [_] at hf
    rw [List.mem_singleton] at hf
    subst hf
    refine ⟨⟨?_⟩, ?_, ?_, ?_, ⟨?_⟩, ?_⟩
    · intro ty declared
      change w1g.Γ Api.root = some ty at declared
      rw [valid_w1g.root] at declared
      cases declared
      exact savedPosition_of_saved _ _ _ _ saved
    · intro p hp; cases hp
    · intro v hv; cases hv
    · intro v hv; cases hv
    · intro v hv; cases hv
    · intro key value ty lookup
      change (Env.Context.empty : Env.Ctx).getV key = some value at lookup
      rw [Env.Context.getV_empty] at lookup
      cases lookup
  · intro race member; cases member
  · refine ⟨⟨(fun o ho => nomatch ho), (fun _ hp => nomatch hp)⟩, ?_, ⟨(fun i v h => nomatch h)⟩,
      ⟨(fun v hv => nomatch hv)⟩, (fun v hv => nomatch hv), trivial⟩
    intro i v hv ty hty
    cases i with
    | zero =>
      change some (Val.nat 5) = some v at hv
      cases hv
      rw [rho_w1g, if_pos rfl] at hty
      cases hty
      exact trivial
    | succ j =>
      change none = some v at hv
      cases hv
  · intro f hf token hp
    change f ∈ [_] at hf
    rw [List.mem_singleton] at hf
    subst hf
    cases hp
  · constructor
    · exact List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩
    · intro f hf
      change f ∈ [_] at hf
      rw [List.mem_singleton] at hf
      subst f
      decide
    · exact List.nodup_nil
    · intro race member; cases member
    · intro race member; cases member
    · intro key member; cases member
    · intro id token request hr
      rw [afterGood_no_requests] at hr
      cases hr
    · intro id token request hr
      rw [afterGood_no_requests] at hr
      cases hr
    · intro f hf
      change f ∈ [_] at hf
      rw [List.mem_singleton] at hf
      subst f
      rfl
    · intro f hf hp
      change f ∈ [_] at hf
      rw [List.mem_singleton] at hf
      subst f
      exact False.elim (hp rfl)
    · intro f hf token hp
      change f ∈ [_] at hf
      rw [List.mem_singleton] at hf
      subst f
      cases hp
    · intro f hf hx
      change f ∈ [_] at hf
      rw [List.mem_singleton] at hf
      subst f
      cases hx
    · intro f hf hx
      change f ∈ [_] at hf
      rw [List.mem_singleton] at hf
      subst f
      cases hx
    · intro f hf hd
      change f ∈ [_] at hf
      rw [List.mem_singleton] at hf
      subst f
      cases hd
    · intro raceId race hr; cases hr
    · intro raceId race hr; cases hr
    · intro f hf p hp
      change f ∈ [_] at hf
      rw [List.mem_singleton] at hf
      subst f
      cases hp
    · intro f hf o ho
      change f ∈ [_] at hf
      rw [List.mem_singleton] at hf
      subst f
      cases ho
  · constructor
    · intro f hf p hp
      change f ∈ [_] at hf
      rw [List.mem_singleton] at hf
      subst f
      cases hp
    · intro f hf o ho
      change f ∈ [_] at hf
      rw [List.mem_singleton] at hf
      subst f
      cases ho
  · intro f hf id marker
    change f ∈ [_] at hf
    rw [List.mem_singleton] at hf
    subst f
    change none = some id at marker
    cases marker

theorem afterGood_queueOk :
    QueueOk (refProg : ProgramSource) w1g afterGood.1 afterGood.2 := by
  rw [afterGood_queue]
  refine ⟨?_, ?_, ?_, ?_, ⟨trivial, trivial, trivial⟩, ⟨?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  · intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl <;> trivial
  · intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · trivial
    · exact ⟨_, rfl, rfl, rfl⟩
  · intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl <;> trivial
  · decide
  · intro key member
    cases member
  · intro id token request hr
    rw [afterGood_no_requests] at hr
    cases hr
  · intro source exit observer member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with h | h <;> cases h
  · intro race child member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with h | h <;> cases h
  · intro host yielding race member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with h | h <;> cases h
  -- row 139's `links`: vacuous, the queue holds no `link`
  · intro mode scope target interruptor extra member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with h | h <;> cases h
  -- row 134 (d)'s queued observers: vacuous, the queue holds no `observe`
  · intro source exit observer member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with h | h <;> cases h

/-- The output in the typed configuration (row 134's `I`): the root's code, which the queued
`deliver` reads, is typed with its stack at the world that declares cell 0. -/
theorem afterGood_config :
    ConfigTyped (refProg : ProgramSource) unitTy w1g afterGood.1 afterGood.2 := by
  refine ⟨⟨afterGood_typed, rfl, ?_, machineLive_of_quiet _ rfl rfl⟩, ?_,
    afterGood_queueOk⟩
  · intro f hf _ _ _ ty declared
    have saved := afterGood_saved f hf
    change f ∈ [_] at hf
    rw [List.mem_singleton] at hf
    subst hf
    change w1g.Γ Api.root = some ty at declared
    rw [valid_w1g.root] at declared
    cases declared
    exact saved
  · intro f hf _ _ _ ty declared
    have saved := afterGood_saved f hf
    change f ∈ [_] at hf
    rw [List.mem_singleton] at hf
    subst hf
    change w1g.Γ Api.root = some ty at declared
    rw [valid_w1g.root] at declared
    cases declared
    exact saved

/-- **Green control: with a frame typed into `unit` on every success, the same `loop` keeps
the typed configuration** (`good_config` to `afterGood_config`), at the world that declares the
new cell. So `step_loop_refuted` is the frame's doing, not the step's. Restated over row 134's
`I` (seat I): the queue-relative `TypedState … afterGood.2` of seat B's statement typed the
root's current code, which under the split is `ReadCode`'s, so the faithful restatement is
`ConfigTyped`, which also carries `QueueOk`. -/
theorem step_loop_good :
    ∃ w', world.leHost w' ∧ ConfigTyped (refProg : ProgramSource) unitTy w' afterGood.1 afterGood.2 :=
  ⟨w1g, w0_le_w1g, afterGood_config⟩

/-! ## 5. The repair: the closed judgment refuses the bad frame and loses nothing -/

/-- **Control: the Kripke-closed judgment refuses the counterexample's frame at the initial
world**, so the typed state built on it excludes the bad machine from the start. -/
theorem bad_not_kripke_initial :
    ¬ StackAccepts (TypedProg (refProg : ProgramSource)) ExitOk (frameProtocols refProg)
      world tin unitTy [.answer badNext] := by
  intro h
  cases h with
  | cons head tail =>
    cases tail
    cases head with
    | answer next run =>
      have hp := (TypedProg.pure_inv (run w1 w0_le_w1 (.success (Val.cell ⟨0⟩)) cell0_ok_w1)).1
      rw [fitsExit_success_iff] at hp
      change Typed.Fits w1 (Val.str "x") .unit at hp
      simp only [Typed.Fits] at hp

-- Red fixture: the one-world acceptance script (`stack_ok`'s, verbatim) against the closed
-- judgment. The answer clause now begins with a later world, so the script's split on the exit
-- has nothing to split; the repair is in force where the bad frame was admitted.
/--
error: Invalid alternative name `success`: Expected `mk`
---
error: Invalid alternative name `failure`: Expected `mk`
---
error: Alternative `mk` has not been provided
-/
#guard_msgs (error) in
example :
    StackAccepts (TypedProg (refProg : ProgramSource)) ExitOk (frameProtocols refProg) world tin unitTy
      [.answer badNext] := by
  refine .cons (.answer badNext fun ex hex => ?_) (.nil unitTy)
  cases ex with
  | success v =>
    exfalso
    have hf := hex.1
    rw [fitsExit_success_iff] at hf
    change Typed.Fits world v (.refOf .nat) at hf
    simp only [Typed.Fits] at hf
    split at hf
    · obtain ⟨t', ht, _⟩ := hf
      cases ht
    · exact hf
  | failure c =>
    refine .pure ⟨?_, hex.2⟩
    have hf := hex.1
    rw [fitsExit_failure_iff] at hf ⊢
    exact hf

/-- The closed judgment gives the one-world judgment at the current world: every frame clause
read at `w` by reflexivity. Nothing proved over the one-world judgment is lost. -/
theorem frameAccepts_now {TP : W → EffTy → RProgram → Prop} {Ex : W → EffTy → ExitV → Prop}
    {hooks : FrameProtocols} {w : W} {a b : EffTy} {f : ScopeFrame}
    (h : FrameAccepts TP Ex hooks w a b f) : Old.FrameAccepts TP Ex hooks w a b f := by
  cases h with
  | resume kind next run skip =>
    exact .resume kind next (run w (leHost_refl w)) (skip w (leHost_refl w))
  | answer next run => exact .answer next (run w (leHost_refl w))
  | restoreMask flag => exact .restoreMask _ flag
  | asyncFinalizer name protocol => exact .asyncFinalizer name (protocol w (leHost_refl w))
  | finalizerMask flag => exact .finalizerMask _ flag
  | iter name protocol => exact .iter name (protocol w (leHost_refl w))
  | loop name cursor protocol => exact .loop name cursor (protocol w (leHost_refl w))

theorem stackAccepts_now {TP : W → EffTy → RProgram → Prop} {Ex : W → EffTy → ExitV → Prop}
    {hooks : FrameProtocols} {w : W} {a b : EffTy} {s : List ScopeFrame}
    (h : StackAccepts TP Ex hooks w a b s) : Old.StackAccepts TP Ex hooks w a b s := by
  induction h with
  | nil ty => exact .nil ty
  | cons head _ ih => exact .cons (frameAccepts_now head) ih

/-- The flip of `stackAccepts_not_mono`: the closed judgment transports every stack it accepts to
every later world, so the good frame accepted at the initial world is accepted at `w1`. -/
theorem good_stack_transports :
    StackAccepts (TypedProg (refProg : ProgramSource)) ExitOk (frameProtocols refProg) w1 tin unitTy
      [.answer goodNext] :=
  Contracts.stackAccepts_mono w0_le_w1 (stack_good world)

/-- For seat C's ledger (row 87, "monotonicity of every owner predicate of `preds`"): the typed
state's `SavedOk` owner predicate transports along the host order at a position the world
already declares; an undeclared position may become declared later, which is why the premise is
needed. Proved beside its ledger line (`Effect4.Program.Typed.preds_savedOk_mono`, scope
`M3bWorld`, `Laws/Program/Typed/Assembly.lean`); this is its use here. -/
theorem preds_savedOk_mono (root : ProgramSource) (w w' : W) (e : Expect) (x : RSaved)
    (ord : w.leHost w') (declared : (expectOf w e).isSome = true)
    (h : (preds root).SavedOk w e x) : (preds root).SavedOk w' e x :=
  Effect4.Program.Typed.preds_savedOk_mono root w w' e x ord declared h

/-- The refusal also follows from the landed transport: the closed judgment at the initial world
would transport to `w1`, where even the one-world judgment refuses the frame. -/
theorem bad_not_kripke_by_transport :
    ¬ StackAccepts (TypedProg (refProg : ProgramSource)) ExitOk (frameProtocols refProg)
      world tin unitTy [.answer badNext] :=
  fun h => bad_refused_at_w1 (stackAccepts_now (Contracts.stackAccepts_mono w0_le_w1 h))

/-! ### Wrapping the hook premises at the frame does not survive the walk

Verifier's `verify-WrapWalk.lean`: an interpreter whose generator `n1` resumes under `n2`, and
hooks whose iterator protocol for `n2` reads the world (`midOf`). These hooks meet the one-world
hook laws, and the one-world walk types its output; the output `[.iter n2]` has no closed typing,
because `n2`'s input type is `A` at the initial world and `B` once cell 0 is declared. So the
protocols are closed in their own definitions, and the current `HookLaws` refuse these hooks. -/

abbrev A : EffTy := EffTy.pure .unit
abbrev B : EffTy := EffTy.pure (.union .unit .unit)
abbrev T : EffTy := EffTy.pure .unit

/-- The resumed protocol's input type reads the world: `A` while cell 0 is undeclared, `B` after. -/
def midOf (w : W) : EffTy :=
  match w.Ρ ⟨0⟩ with
  | none => A
  | some _ => B

def n1 : EffName := .abort
def n2 : EffName := .restore (.success Val.unit)

/-- An interpreter whose generator `n1` resumes with `unit` code under the name `n2`, and whose
`n2` is done with `unit`. -/
def interpX : RInterp :=
  { interpR refProg with
    iterNext := fun name _ => match name with
      | .abort => ([], .resume (.pure (.success Val.unit)) n2)
      | _ => ([], .done Val.unit) }

/-- Hooks: `n1` at `A → T` at every world; `n2` at `midOf w → T`. -/
def hooksX : FrameProtocols where
  asyncFinalizer _ _ _ _ := False
  iterator w tin tout name := match name with
    | .abort => tin = A ∧ tout = T
    | .restore _ => tin = midOf w ∧ tout = T
    | _ => False
  loop _ _ _ _ _ := False

theorem unit_fits_mid (w : W) : ExitOk w (midOf w) (.success Val.unit) := by
  refine ⟨?_, trivial⟩
  unfold midOf
  split
  · rw [fitsExit_success_iff]
    exact trivial
  · rw [fitsExit_success_iff]
    change Typed.Fits w Val.unit (.union .unit .unit)
    exact Or.inl trivial

/-- The one-world hook laws hold for this interpreter and these hooks. -/
theorem hookLawsX_old : Old.HookLaws (refProg : ProgramSource) interpX hooksX where
  asyncFinalizer _ _ _ _ h := h.elim
  iterator w tin tout name h := by
    cases name with
    | abort =>
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨rfl, fun v _ => ?_⟩
      exact ⟨midOf w, TypedProg.pure (unit_fits_mid w), rfl, rfl⟩
    | restore e =>
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨?_, fun v _ => ?_⟩
      · unfold midOf
        split <;> rfl
      · show ExitOk w T (.success Val.unit)
        exact ⟨by rw [fitsExit_success_iff]; exact trivial, trivial⟩
    | _ => exact h.elim
  loop _ _ _ _ _ h := h.elim

theorem mid_w0 : midOf world = A := rfl

theorem mid_w1 : midOf w1 = B := by
  unfold midOf
  rw [show w1.Ρ ⟨0⟩ = some .nat by simp only [w1, if_pos]]

/-- **The current `HookLaws` refuse these hooks**: a resumed protocol must hold at every later
world with one intermediate type, and `n2`'s is `A` at the initial world and `B` at `w1`. -/
theorem hookLawsX_refused : ¬ HookLaws (refProg : ProgramSource) interpX hooksX := by
  intro laws
  obtain ⟨_, step⟩ := laws.iterator world A T n1 ⟨rfl, rfl⟩
  obtain ⟨tin', _, tail⟩ := step Val.unit trivial
  have h0 : tin' = midOf world ∧ T = T := tail world (leHost_refl world)
  have h1 : tin' = midOf w1 ∧ T = T := tail w1 w0_le_w1
  rw [mid_w0] at h0
  rw [mid_w1, h0.1] at h1
  cases h1.1

def frame0 : RSaved :=
  { current := .pure (.success Val.unit), stack := [.iter n1], interruptible := true,
    interruptedCause := none, deferredInterrupt := false }

/-- The input frame is accepted in the closed form: `n1`'s protocol does not read the world. -/
theorem input_kripke :
    StackAccepts (TypedProg (refProg : ProgramSource)) ExitOk hooksX world A T [.iter n1] :=
  .cons (.iter n1 (fun _ _ => ⟨rfl, rfl⟩)) (.nil T)

theorem input_exit : ExitOk world A (.success Val.unit) :=
  ⟨by rw [fitsExit_success_iff]; exact trivial, trivial⟩

/-- The walk pushes `n2`'s frame over the resumed code. -/
theorem walk_output :
    popR interpX (.success Val.unit) [.iter n1] frame0 =
      ({ frame0 with current := .pure (.success Val.unit), stack := [.iter n2] }, none) := rfl

/-- The one-world judgment types the walk's output at the initial world (what the one-world
walk concluded, `eb3ab9a9`'s `walk_typed_one_world`). -/
theorem output_typed_one_world :
    Old.SavedOk (TypedProg (refProg : ProgramSource)) ExitOk hooksX world T
      (popR interpX (.success Val.unit) [.iter n1] frame0).1 := by
  rw [walk_output]
  exact ⟨midOf world, TypedProg.pure (unit_fits_mid world),
    .cons (.iter n2 ⟨rfl, rfl⟩) (.nil T), ⟨(fun _ h => nomatch h), (fun h => nomatch h)⟩⟩

/-- **Red control: the walk's output has no closed typing under these hooks.** Whatever
intermediate type the resumed code is given, `n2`'s frame would need it to be `midOf w'` at
every later world, which is `A` at the initial world and `B` at `w1`. -/
theorem output_not_kripke :
    ¬ ∃ tin', StackAccepts (TypedProg (refProg : ProgramSource)) ExitOk hooksX world tin' T
      [.iter n2] := by
  rintro ⟨tin', h⟩
  cases h with
  | cons head tail =>
    cases tail
    cases head with
    | iter name protocol =>
      have h0 : tin' = midOf world ∧ T = T := protocol world (leHost_refl world)
      have h1 : tin' = midOf w1 ∧ T = T := protocol w1 w0_le_w1
      rw [mid_w0] at h0
      rw [mid_w1, h0.1] at h1
      cases h1.1

end Test.Program.FramesNotKripke

open Test.Program.FramesNotKripke in
#print axioms stackAccepts_not_mono
open Test.Program.FramesNotKripke in
#print axioms typed
open Test.Program.FramesNotKripke in
#print axioms queue
open Test.Program.FramesNotKripke in
#print axioms post_untyped
open Test.Program.FramesNotKripke in
#print axioms step_loop_refuted
open Test.Program.FramesNotKripke in
#print axioms evaluate_keeps
open Test.Program.FramesNotKripke in
#print axioms bad_not_kripke_initial
open Test.Program.FramesNotKripke in
#print axioms frameAccepts_now
open Test.Program.FramesNotKripke in
#print axioms stackAccepts_now
open Test.Program.FramesNotKripke in
#print axioms bad_not_kripke_by_transport
open Test.Program.FramesNotKripke in
#print axioms good_stack_transports
open Test.Program.FramesNotKripke in
#print axioms preds_savedOk_mono
open Test.Program.FramesNotKripke in
#print axioms good_config
open Test.Program.FramesNotKripke in
#print axioms afterGood_config
open Test.Program.FramesNotKripke in
#print axioms step_loop_good
open Test.Program.FramesNotKripke in
#print axioms hookLawsX_old
open Test.Program.FramesNotKripke in
#print axioms hookLawsX_refused
open Test.Program.FramesNotKripke in
#print axioms output_typed_one_world
open Test.Program.FramesNotKripke in
#print axioms output_not_kripke
