import Effect4.Laws.Program.FinalizerEvaluation
import Effect4.Laws.Program.CodeClosure.NativeFunding
import Effect4.Laws.Program.PlaceFunding.Primitive

/-!
Concept: scope-lifetime-finalization R11.
Question: native frame accounting serves once_placed_outside_census.
Consumer: the full source primitive evaluator and its command invariant.
The shared connector retains the actual race and detached program places.
Its source annotation and complete history remain separate obligations.
-/
set_option autoImplicit false
namespace Effect4.Program.FinalizerSource
open Effect4 Effect4.Machine Effect4.Program

/-- Actual native delegation receives the frame proof's consumed and returned reservations. -/
theorem step_frame_debit (root : NativeEff) (q : List Nat) (view) (table : RowTable)
    (placed : OncePlaced (.eff root) q = true) (machine : NativeMachine)
    (fiber : RunFiber EffName EffThunk Val Err Defect FiberId Ann Ctx) (yielding : Bool)
    (held : FrameAt q fiber.frame) :
    (ledger root q).IterDebit machine fiber
      (evaluatePrim.stepFrame (interpAt root view table) machine fiber yielding) := by
  have bounded := CodeClosure.Funding.step_frame_bound (frameModel root q) (consumedFrame q) (producedFrame q)
    (interpAt root view table) machine fiber yielding (step_bound root q view table placed fiber.frame held)
    (by
      intro exit events finished
      rw [consumed_slots]
      exact CodeClosure.Events.finished_events_zero (successPush q) (exitPush q)
        (interpAt root view table).toPrimInterp fiber.frame exit events finished)
  have fields := CodeClosure.Funding.step_frame_fields (interpAt root view table) machine fiber yielding
  apply PlaceFunding.local_debit machine fiber _ fields.2.1 fields.2.2.1
    (by rw [fields.2.2.2.2]; rfl)
  exact bounded

/-- The actual finalizer pop retains its ordinary callback annotation. -/
theorem pop_finalizer_at (root : NativeEff) (q : List Nat) (view : List (FiberId × ExitV)) (table : RowTable)
    (placed : OncePlaced (.eff root) q = true) (fiber : SourceFrame) (exit : ExitV)
    (body : NCode) (callback : EffName) (flag : Bool) (held : FrameAt q fiber)
    (selected : (WriterWeights.popFor fiber exit).answer = .frame (.onExit body callback flag)) :
    OrdinaryNameAt q callback := by
  cases exit with
  | success value =>
    exact (CodeClosure.Family.value_selected root table (OrdinaryNameAt q) (NameAt q) (ThunkAt q)
      (hooks root q table placed) view fiber value _ held.2 selected).2
  | failure cause =>
    exact (CodeClosure.Family.cause_selected root table (OrdinaryNameAt q) (NameAt q) (ThunkAt q)
      (hooks root q table placed) view fiber cause _ held.2 selected).2

/-- Actual native finalizer dispatch spends only the selected saved reservation. -/
theorem finalizer_debit (root : NativeEff) (q : List Nat) (view) (table : RowTable)
    (placed : OncePlaced (.eff root) q = true) (machine : NativeMachine)
    (fiber : RunFiber EffName EffThunk Val Err Defect FiberId Ann Ctx) (yielding : Bool)
    (exit : ExitV) (held : FrameAt q fiber.frame) :
    (ledger root q).IterDebit machine fiber
      (evaluatePrim.finalizerOr (interpAt root view table) machine fiber yielding exit) := by
  have delegated := CodeClosure.Funding.step_frame_bound (frameModel root q) (consumedFrame q) (producedFrame q)
    (interpAt root view table) machine fiber yielding (step_bound root q view table placed fiber.frame held)
    (by
      intro exit events finished
      rw [consumed_slots]
      exact CodeClosure.Events.finished_events_zero (successPush q) (exitPush q)
        (interpAt root view table).toPrimInterp fiber.frame exit events finished)
  rw [consumed_slots] at delegated
  have bounded := CodeClosure.Funding.finalizer_bound (frameModel root q) (successPush q) (exitPush q)
    (producedFrame q) (interpAt root view table) machine fiber yielding exit (by
      intro body callback flag program selected produced
      have owned := pop_finalizer_at root q view table placed fiber.frame exit body callback flag held selected
      have result := interp_finalizer root q view table callback _ program (ordinary_name q callback owned) produced
      change current root q (finalizerCode _ _ program) ≤ name q callback
      rw [(finalizer_code root q view table _ program result.1).2]
      exact result.2) delegated
  have fields := CodeClosure.Funding.finalizer_fields (interpAt root view table) machine fiber yielding exit
  apply PlaceFunding.local_debit machine fiber _ fields.2.1 fields.2.2.1
    (by rw [fields.2.2.2.2]; rfl)
  rw [← consumed_slots] at bounded
  exact bounded

end Effect4.Program.FinalizerSource
