import Effect4.Laws.Program.Typed.Assembly
import Effect4.Laws.Machine.StoresLaws

/-!
# Synthesis seat, formal pass (2026-10-01): ALG-01 at the merged head

Port of the ALGEBRA verifier's `verify-StepLoop.lean` (red part and Kripke control) to the tree
after the merge of `codex/slice6-fixes` (`0c534f06`), whose `StepPreserves` adds the dispatch
premise `m.stuck = none`, a queue argument to `TypedState`, H1's scheduler, observer and
registration conjuncts, and the nine-field `QueueOk`; and whose exit judgment is H2's `ExitOk`.
The machine is built the way the tree's own `M6Capstone.H1TerminalAmendment` controls build
theirs: one running root fiber, its code the denoted `Ref.make(5)`, its stack the seat's
`.answer badNext` frame, at the initial world, with `[loop root]` queued.

* `typed`, `queue`, `stuck_none`: the step obligation's premises hold at this state.
* `step_loop_refuted` (red): one `loop` allocates cell 0 and no world types the result, so the
  merged `M6Ledger.step_loop` proposition is false.
* `bad_not_kripke_initial` (control): the Kripke-closed frame judgment refuses the bad frame at
  the initial world (the seat's `FrameAcceptsK`, with the merged `ExitOk`).
-/

set_option autoImplicit false
set_option maxRecDepth 8192

namespace Research.Synthesis.HeadStepLoop

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Sched Effect4.Program.Denote
open Effect4.Program.Typed Effect4.Laws.Effects Contracts

abbrev W := Effect4.Program.Typed.World

def refProg : NativeEff := .perform .refMake (.lit (.nat 5))

def badNext : ExitV → RProgram
  | .success _ => .pure (.success (Val.str "x"))
  | .failure c => .pure (.failure c)

abbrev tin : EffTy := EffTy.pure (.refOf .nat)
abbrev unitTy : EffTy := EffTy.pure .unit
abbrev world : W := initialWorld unitTy

def current : RProgram := denoteR refProg refProg (rootPoint 20)

def fiber : RFiber :=
  { RunFiber.make Api.root current true (stores.budgetOf emptyCtx) emptyCtx with
    running := true
    frame := { current := current
               stack := [.answer badNext]
               interruptible := true
               interruptedCause := none
               deferredInterrupt := false } }

def machine : RState := { loadR refProg 20 20 with fibers := [fiber] }

theorem valid : WorldValid unitTy world machine := by
  have old := initial_world_valid unitTy refProg 20 20 ⟨rfl, rfl⟩
  refine {
    ids := old.ids, fibers := old.fibers, heap := old.heap, promises := old.promises,
    tokens := ?_, tokenBound := old.tokenBound, tokenTargets := old.tokenTargets,
    state := old.state, wf := old.wf, cells := old.cells, fiberClosed := old.fiberClosed,
    heapClosed := old.heapClosed, promiseClosed := old.promiseClosed,
    tokenClosed := old.tokenClosed, root := old.root }
  intro f hf token hp
  change f ∈ [fiber] at hf
  rw [List.mem_singleton] at hf
  subst f
  cases hp

theorem no_requests (id : FiberId) (token : Nat) : requestOfR machine id token = none := by
  unfold requestOfR
  cases hf : machine.fiber? id with
  | none => rfl
  | some found =>
    have member := List.mem_of_find?_eq_some hf
    change found ∈ [fiber] at member
    rw [List.mem_singleton] at member
    subst found
    rfl

theorem scheduler : SchedulerState machine := by
  constructor
  · exact List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩
  · intro f hf
    change f ∈ [fiber] at hf
    rw [List.mem_singleton] at hf
    subst f
    decide
  · exact List.nodup_nil
  · intro race member; cases member
  · intro race member; cases member
  · intro key member; cases member
  · intro id token request hr
    rw [no_requests] at hr
    cases hr
  · intro id token request hr
    rw [no_requests] at hr
    cases hr
  · intro f hf
    change f ∈ [fiber] at hf
    rw [List.mem_singleton] at hf
    subst f
    rfl
  · intro f hf hp
    change f ∈ [fiber] at hf
    rw [List.mem_singleton] at hf
    subst f
    exact False.elim (hp rfl)
  · intro f hf token hp
    change f ∈ [fiber] at hf
    rw [List.mem_singleton] at hf
    subst f
    cases hp
  · intro f hf hx
    change f ∈ [fiber] at hf
    rw [List.mem_singleton] at hf
    subst f
    cases hx
  · intro f hf hd
    change f ∈ [fiber] at hf
    rw [List.mem_singleton] at hf
    subst f
    cases hd

theorem observers : ObserverState (refProg : ProgramSource) world machine := by
  constructor
  · intro f hf p hp
    change f ∈ [fiber] at hf
    rw [List.mem_singleton] at hf
    subst f
    cases hp
  · intro f hf o ho
    change f ∈ [fiber] at hf
    rw [List.mem_singleton] at hf
    subst f
    cases ho

theorem registration : RegistrationState (refProg : ProgramSource) world machine := by
  intro f hf id marker
  change f ∈ [fiber] at hf
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

/-- At the initial world no cell is declared, so no success fits `refOf nat` and the bad frame
is accepted vacuously; its failure arm passes the failure on. -/
theorem stack_ok :
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

theorem saved_typed : SavedOk (TypedProg (refProg : ProgramSource)) ExitOk
    (frameProtocols (refProg : ProgramSource)) world unitTy fiber.frame :=
  ⟨tin, code_typed world, stack_ok, ⟨(fun _ h => nomatch h), (fun h => nomatch h)⟩⟩

def command : RCmd := .loop Api.root false

theorem typed : TypedState (refProg : ProgramSource) unitTy world machine [command] := by
  refine ⟨valid, ⟨?_, ?_, ?_⟩, ?_, scheduler, observers, registration⟩
  · intro f hf
    change f ∈ [fiber] at hf
    rw [List.mem_singleton] at hf
    subst f
    refine ⟨⟨?_⟩, ?_, ?_, ?_, ⟨?_⟩, ?_⟩
    · intro ty declared
      change world.Γ Api.root = some ty at declared
      rw [valid.root] at declared
      cases declared
      exact savedPosition_of_saved _ _ _ _ _ _ _ saved_typed
    · intro p hp; cases hp
    · intro v hv; cases hv
    · intro v hv; cases hv
    · intro v hv; cases hv
    · intro key value ty lookup
      change (Env.Context.empty : Env.Ctx).getV key = some value at lookup
      rw [Env.Context.getV_empty] at lookup
      cases lookup
  · intro race member; cases member
  · refine ⟨(fun o ho => nomatch ho), (fun i v h => nomatch h), ⟨(fun i v h => nomatch h)⟩,
      ⟨(fun v hv => nomatch hv)⟩, (fun v hv => nomatch hv), trivial⟩
  · intro f hf token hp
    change f ∈ [fiber] at hf
    rw [List.mem_singleton] at hf
    subst f
    cases hp

theorem queue : QueueOk (refProg : ProgramSource) world machine [command] := by
  refine ⟨?_, ?_, ?_, List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩, ⟨trivial, trivial⟩,
    ⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · intro c hc
    rw [List.mem_singleton] at hc
    subst c
    trivial
  · intro c hc
    rw [List.mem_singleton] at hc
    subst c
    exact ⟨fiber, rfl, rfl, rfl⟩
  · intro c hc
    rw [List.mem_singleton] at hc
    subst c
    trivial
  · intro key member; cases member
  · intro id token request hr
    rw [no_requests] at hr
    cases hr
  · intro source exit observer member
    rw [List.mem_singleton] at member
    cases member
  · intro race child member
    rw [List.mem_singleton] at member
    cases member
  · intro host yielding race member
    rw [List.mem_singleton] at member
    cases member

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

theorem result_not_inert : ¬ CodeInert result.1 result.2 (.fiber Api.root) := by
  intro h
  rcases h with hs | hterm
  · rw [result_stuck] at hs
    exact Bool.noConfusion hs
  · rcases hterm with ⟨ex, hmem⟩ | ⟨fb, hfb, _, hex⟩
    · have hall := List.all_eq_true.mp result_no_finish _ hmem
      simp [isFinishOf] at hall
    · rw [(result_only_root fb hfb).2] at hex
      exact Bool.noConfusion hex

/-- **No world types the machine after the allocating `loop`.** -/
theorem post_untyped (w : W) :
    ¬ TypedState (refProg : ProgramSource) unitTy w result.1 result.2 := by
  intro h
  obtain ⟨f, hf, hid, _, hcur, hst⟩ := result_fiber
  have hroot : expectOf w (.fiber f.id) = some unitTy := by
    rw [hid]
    exact h.1.root
  obtain ⟨tin', hprog0, hstack, _⟩ := (h.2.1.c0 f hf).c0.c0 _ hroot
  have hni : ¬ CodeInert result.1 result.2 (.fiber f.id) := by rw [hid]; exact result_not_inert
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

/-- **The merged `M6Ledger.step_loop` proposition is false at this instance.** -/
theorem step_loop_refuted :
    ¬ StepPreserves (refProg : ProgramSource) unitTy (.loop Api.root false) := by
  intro h
  obtain ⟨w', _, ht, _⟩ := h world machine [] stuck_none typed queue
  exact post_untyped w' ht

/-! ## Control: the Kripke-closed frame judgment refuses the bad frame at the initial world -/

section Kripke

variable (TP : W → EffTy → RProgram → Prop) (Ex : W → EffTy → ExitV → Prop)

inductive FrameAcceptsAnswerK (w : W) : EffTy → EffTy → ScopeFrame → Prop
  | answer {tin tout : EffTy} (next : ExitV → RProgram)
      (run : ∀ w', w.leHost w' → ∀ ex, Ex w' tin ex → TP w' tout (next ex)) :
      FrameAcceptsAnswerK w tin tout (.answer next)

end Kripke

def s1 : Stores := { Stores.empty with refs := [Val.nat 0] }

def w1 : W :=
  { world with state := s1, Ρ := fun k => if k = ⟨0⟩ then some .nat else none }

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
    fun _ _ _ h => h⟩, fun _ _ h => h⟩

theorem cell0_ok_w1 : ExitOk w1 tin (.success (Val.cell ⟨0⟩)) := by
  refine ⟨?_, trivial⟩
  rw [fitsExit_success_iff]
  change Typed.Fits w1 (Val.cell ⟨0⟩) (.refOf .nat)
  simp only [Typed.Fits]
  exact ⟨.nat, by simp only [w1, if_pos], Ty.sub_refl _, Ty.sub_refl _⟩

theorem bad_not_kripke_initial :
    ¬ FrameAcceptsAnswerK (TypedProg (refProg : ProgramSource)) ExitOk world tin unitTy
      (.answer badNext) := by
  intro h
  cases h with
  | answer next run =>
    have hp := (TypedProg.pure_inv (run w1 w0_le_w1 (.success (Val.cell ⟨0⟩)) cell0_ok_w1)).1
    rw [fitsExit_success_iff] at hp
    change Typed.Fits w1 (Val.str "x") .unit at hp
    simp only [Typed.Fits] at hp

end Research.Synthesis.HeadStepLoop

open Research.Synthesis.HeadStepLoop in
#print axioms typed
open Research.Synthesis.HeadStepLoop in
#print axioms queue
open Research.Synthesis.HeadStepLoop in
#print axioms result_not_inert
open Research.Synthesis.HeadStepLoop in
#print axioms post_untyped
open Research.Synthesis.HeadStepLoop in
#print axioms step_loop_refuted
open Research.Synthesis.HeadStepLoop in
#print axioms bad_not_kripke_initial
