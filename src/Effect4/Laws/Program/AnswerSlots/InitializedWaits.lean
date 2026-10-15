import Effect4.Laws.Program.AnswerSlots.InitializedNativeParks
import Effect4.Laws.Program.AnswerSlots.InitializedOtherRows
import Effect4.Laws.Program.ParkedShape

/-!
Concept: store-typing R4 and scope-lifetime-finalization R11.
Question: both crew log histories retain the answer class of each parked saved suffix.
Reach: initialized direct programs without races, including delayed reference-read completions.
A forced yield ignores its returned value and retains only its allocation counts.
Consumer: the existing command flow and source-owned resume queue, then CrewLogs.history.
This certificate supplies no progress or host implementation agreement.
-/
set_option autoImplicit false
namespace Effect4.Program.AnswerSlots.Initialized
open Effect4 Effect4.Machine Effect4.Program

/-- A park either awaits a broad stable answer or ignores an answer during initialization. -/
inductive Demand (spec : Spec) (world : World) : Kind → Prop
  | stable (ready : Ready spec world) : Demand spec world (.stable .root)
  | yielded (phase : Phase spec world) (pending : ¬ Ready spec world) :
      Demand spec world (.yielded world.state.refs.length world.state.deferreds.cells.length)

/-- The current parked token retains the ordered saved suffix that its reply will consume. -/
def Waits (spec : Spec) (state : Stores) (fiber : SourceScope.SourceFiber) : Prop :=
  fiber.parked ≠ .notParked → ∃ input output,
    Demand spec ⟨fiber.id, state⟩ input ∧
      Effect4.Contracts.Path (Edge spec [] ⟨fiber.id, state⟩) input output fiber.frame.stack

/-- Source ownership rules out a race-cleanup payload in a crew without a race. -/
theorem terminal_no_race (spec : Spec) (raceFree : SourceScope.RaceFreeSource spec.root)
    (race : Nat) (exit : ExitV)
    (source : SourceScope.CodeAt spec.root
      (.onSuccess (.withFiber (.store (.act (.setInterruptible (.cancelRace race) false))))
        (.store (.restore exit)))) : False :=
  raceFree.not_race source.1

/-- Every actual source-owned reply fits the parked demand, including a delayed read.
The existing queue invariant supplies both premises; no new scheduler assertion is needed. -/
theorem Demand.reply (spec : Spec) (raceFree : SourceScope.RaceFreeSource spec.root)
    (world : World) (kind : Kind) (demand : Demand spec world kind) (code : NCode)
    (source : SourceScope.CodeAt spec.root code) (terminal : SourceScope.TerminalReply code) :
    CodeAt spec world kind code := by
  cases terminal with
  | success value =>
    cases demand with
    | stable ready => exact .success ⟨ready, trivial⟩
    | yielded phase pending => exact .success ⟨phase, rfl, rfl, pending⟩
  | failure cause =>
    cases demand with
    | stable ready => exact .failure (.inr ready)
    | yielded phase pending => exact .failure phase
  | refGet cell =>
    cases demand with
    | stable ready => exact .stable ready (completion_code spec (.ofRefGet cell))
    | yielded phase pending => exact .reading phase rfl rfl pending
  | raceCleanup race exit => exact (terminal_no_race spec raceFree race exit source).elim

/-- A parked current head determines its reply demand from the existing answer class. -/
theorem Demand.of_head (spec : Spec) (fragment : SourceScope.Fragment spec.root)
    (world : World) (kind : Kind) (program : NCode) (owned : CodeAt spec world kind program)
    (shape : ParkedShape.Head program) : Demand spec world kind := by
  cases shape with
  | yielded =>
    have good := success_value spec fragment [] world kind .unit owned
    cases kind with
    | stable kind =>
      cases kind with
      | root => exact .stable good.1
      | connection identity => cases good.2
    | allocated index => cases good.2.1
    | gate => cases good.1
    | yielded refs deferred =>
      rw [← good.2.1, ← good.2.2.1]
      exact .yielded good.1 good.2.2.2
  | async register signal cancel =>
    obtain ⟨rfl, ready⟩ := async_shape spec world kind register signal cancel owned
    exact .stable ready
  | action thunk =>
    obtain ⟨rfl, ready, _⟩ := action_shape spec world kind thunk owned
    exact .stable ready
  | park parkKind =>
    obtain ⟨rfl, ready⟩ := park_shape spec [] world kind _ owned (by intro wrong; cases wrong)
    exact .stable ready
  | storedPark parkKind =>
    obtain ⟨rfl, ready⟩ := park_shape spec [] world kind _ owned (by intro wrong; cases wrong)
    exact .stable ready

/-- Current-code ownership and the existing path supply the reply suffix at each parked cut. -/
theorem Waits.of_frame (spec : Spec) (fragment : SourceScope.Fragment spec.root)
    (state : Stores) (fiber : SourceScope.SourceFiber) (input output : Kind)
    (owned : CodeAt spec ⟨fiber.id, state⟩ input fiber.frame.current)
    (saved : Effect4.Contracts.Path (Edge spec [] ⟨fiber.id, state⟩) input output fiber.frame.stack)
    (shape : ParkedShape.Held fiber) : Waits spec state fiber := by
  intro parked
  exact ⟨input, output, Demand.of_head spec fragment _ input _ owned (shape parked), saved⟩

/-- The matching resume installs its existing payload at the recorded parked answer class. -/
theorem Waits.resume (spec : Spec) (raceFree : SourceScope.RaceFreeSource spec.root)
    (state : Stores) (fiber : SourceScope.SourceFiber) (code : NCode)
    (waits : Waits spec state fiber) (parked : fiber.parked ≠ .notParked)
    (source : SourceScope.CodeAt spec.root code) (terminal : SourceScope.TerminalReply code) :
    ∃ output, AnswerFlow.FamilyResult (model spec []) (Edge spec []) ⟨fiber.id, state⟩
      output code fiber.frame.stack := by
  obtain ⟨input, output, demand, saved⟩ := waits parked
  exact ⟨output, input, demand.reply spec raceFree _ input code source terminal, saved⟩

/-- A metadata write retains the parked suffix whenever its owner, park and stack stay the same. -/
theorem Waits.fields {spec : Spec} {state : Stores} {first last : SourceScope.SourceFiber}
    (held : Waits spec state first) (owner : last.id = first.id)
    (parked : last.parked = first.parked) (stack : last.frame.stack = first.frame.stack) :
    Waits spec state last := by
  intro pending
  rw [owner, stack]
  exact held (fun empty => pending (parked.trans empty))

/-- A fiber without a park owes no reply demand. -/
theorem Waits.unparked (spec : Spec) (state : Stores) (fiber : SourceScope.SourceFiber)
    (active : fiber.parked = .notParked) : Waits spec state fiber :=
  fun parked => False.elim (parked active)

/-- Equal allocation counts retain either parked demand at the new actual store. -/
theorem Demand.rebase (spec : Spec) (first last : World) (future : Future first last)
    (refs : first.state.refs.length = last.state.refs.length)
    (deferred : first.state.deferreds.cells.length = last.state.deferreds.cells.length)
    (kind : Kind) (demand : Demand spec first kind) : Demand spec last kind := by
  cases demand with
  | stable ready => exact .stable (ready_future spec first last future ready)
  | yielded phase pending =>
    rw [refs, deferred]
    exact .yielded (phase_future spec first last future phase)
      (fun ready => pending ⟨by rw [refs]; exact ready.1, by rw [deferred]; exact ready.2⟩)

/-- Ready stores transport every parked demand through monotone allocation growth. -/
theorem Demand.future (spec : Spec) (first last : World) (future : Future first last)
    (ready : Ready spec first) (kind : Kind) (demand : Demand spec first kind) : Demand spec last kind := by
  cases demand with
  | stable before => exact .stable (ready_future spec first last future before)
  | yielded phase pending => exact (pending ready).elim

/-- Store administration keeps a parked suffix through equal counts or prior readiness. -/
theorem Waits.state (spec : Spec) (first last : Stores) (fiber : SourceScope.SourceFiber)
    (held : Waits spec first fiber)
    (future : Future ⟨fiber.id, first⟩ ⟨fiber.id, last⟩)
    (carry : Ready spec ⟨fiber.id, first⟩ ∨
      (first.refs.length = last.refs.length ∧ first.deferreds.cells.length = last.deferreds.cells.length)) :
    Waits spec last fiber := by
  intro parked
  obtain ⟨input, output, demand, saved⟩ := held parked
  refine ⟨input, output, ?_, path_future spec [] _ _ future input output _ saved⟩
  rcases carry with ready | ⟨refs, deferred⟩
  · exact demand.future spec _ _ future ready input
  · exact demand.rebase spec _ _ future refs deferred input
end Effect4.Program.AnswerSlots.Initialized
