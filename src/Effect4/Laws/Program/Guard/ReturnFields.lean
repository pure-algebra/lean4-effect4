import Effect4.Laws.Program.Parking
import Effect4.Laws.Program.Guard.Core
import Effect4.Laws.Program.Guard.Interruption
import Effect4.Laws.Program.Guard.DeferredCause
import Effect4.Laws.Program.Guard.FrameOwned

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 800000
namespace Effect4.Program.Guard.ReturnFields
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Guard
abbrev NInterp := RunInterp EffName EffThunk Val Err Defect FiberId Ann Ctx Stores
abbrev NAction := WithFiberAction EffName EffThunk Val Err Defect FiberId Ann Ctx
theorem stepFrame_running (interp : NInterp) (m : NativeMachine)
    (f : NFiber) (yielding : Bool) :
    (evaluatePrim.stepFrame interp m f yielding).fiber.running =
      f.running :=
  (Moves.stepFrame_footprint interp m f yielding).running

theorem finalizerOr_running (interp : NInterp) (m : NativeMachine)
    (f : NFiber) (yielding : Bool) (exit : ExitV) :
    (evaluatePrim.finalizerOr interp m f yielding exit).fiber.running =
      f.running :=
  (Moves.finalizerOr_footprint interp m f yielding exit).running

theorem withFiber_running (interp : NInterp) (m : NativeMachine)
    (f : NFiber) (yielding : Bool) (action : NAction) :
    (evaluatePrim.withFiber interp m f yielding action).fiber.running =
      f.running :=
  (Moves.withFiber_footprint interp m f yielding action).running

theorem evaluatePrim_running (interp : NInterp) (m : NativeMachine)
    (f : NFiber) (yielding : Bool) :
    (evaluatePrim interp m f yielding).fiber.running =
      f.running :=
  (Moves.evaluatePrim_footprint interp m f yielding).running

theorem exitScoped_running (p : NativeEff) (m : NativeMachine)
    (f : NFiber) (yielding : Bool) (exit : ExitV) :
    (exitScoped p m f yielding exit).fiber.running =
      f.running :=
  (Moves.exitScoped_footprint p m f yielding exit).running

theorem evaluateNative_running (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (f : NFiber) (yielding : Bool) :
    (evaluateNative p m f yielding table).fiber.running =
      f.running :=
  (Moves.evaluateNative_footprint p table m f yielding).running

theorem runloopTop_running (f : NFiber) :
    (runloopTop f).running = f.running := by
  unfold runloopTop
  split <;> rfl

theorem injectYield_running (m : NativeMachine) (f : NFiber) (yielding : Bool)
    (it : Iter EffName EffThunk Val Err Defect FiberId Ann Ctx Stores)
    (h : injectYield m f yielding = some it) :
    it.fiber.running = f.running := by
  unfold injectYield at h
  split at h
  · injection h with h'; subst h'; rfl
  · cases h

theorem iteration_running (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (f : NFiber) (yielding : Bool) :
    letI := evaluatorFor p table
    (iteration (interpOf p table) m f yielding).fiber.running =
      f.running :=
  (Moves.iteration_footprint p table (interpOf p table) m f yielding).running

theorem pendingShape_of_unparked (f : NFiber) (park : f.parked = .notParked)
    (pending : f.pending = []) : PendingShape f := by
  simp only [PendingShape, park, pending]

theorem pendingShape_park (f : NFiber) (wait : Pending EffName Val Err Defect FiberId Ann)
    (hp : f.pending = []) : PendingShape (f.park wait) := by
  exact ⟨wait, by simp only [RunFiber.park, hp, List.nil_append], rfl⟩

/-- The shared classification retains the existing guard pending judgment.
Consumer: every evaluator-level pending chain below. -/
theorem parking_pending {m : NativeMachine} {f : NFiber} {it : Moves.ParkIter}
    (held : Moves.Parking m f it) (park : f.parked = .notParked) (pending : f.pending = []) :
    PendingShape it.fiber := by
  cases held with
  | kept hp hn _ => simp only [PendingShape, hp, park, hn, pending]
  | installed wait _ _ hp hn _ =>
    simp only [PendingShape, hp]
    exact ⟨wait, hn.trans (by rw [pending]; rfl), rfl⟩

theorem stepFrame_pending (interp : NInterp) (m : NativeMachine)
    (f : NFiber) (yielding : Bool) (park : f.parked = .notParked) (hp : f.pending = []) :
    PendingShape (evaluatePrim.stepFrame interp m f yielding).fiber :=
  parking_pending (Moves.stepFrame_parking interp m f yielding) park hp

theorem finalizerOr_pending (interp : NInterp) (m : NativeMachine)
    (f : NFiber) (yielding : Bool) (exit : ExitV) (park : f.parked = .notParked) (hp : f.pending = []) :
    PendingShape (evaluatePrim.finalizerOr interp m f yielding exit).fiber :=
  parking_pending (Moves.finalizerOr_parking interp m f yielding exit) park hp

theorem withFiber_pending (interp : NInterp) (m : NativeMachine)
    (f : NFiber) (yielding : Bool) (action : NAction) (park : f.parked = .notParked) (hp : f.pending = []) :
    PendingShape (evaluatePrim.withFiber interp m f yielding action).fiber :=
  parking_pending (Moves.withFiber_parking interp m f yielding action) park hp

theorem evaluatePrim_pending (interp : NInterp) (m : NativeMachine)
    (f : NFiber) (yielding : Bool) (park : f.parked = .notParked) (hp : f.pending = []) :
    PendingShape (evaluatePrim interp m f yielding).fiber :=
  parking_pending (Moves.evaluatePrim_parking interp m f yielding) park hp

theorem exitScoped_pending (p : NativeEff) (m : NativeMachine)
    (f : NFiber) (yielding : Bool) (exit : ExitV) (park : f.parked = .notParked) (hp : f.pending = []) :
    PendingShape (exitScoped p m f yielding exit).fiber :=
  parking_pending (Moves.exitScoped_parking p m f yielding exit) park hp

theorem evaluateNative_pending (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (f : NFiber) (yielding : Bool) (park : f.parked = .notParked) (hp : f.pending = []) :
    PendingShape (evaluateNative p m f yielding table).fiber :=
  parking_pending (Moves.evaluateNative_parking p table m f yielding) park hp

theorem runloopTop_parked (f : NFiber) : (runloopTop f).parked = f.parked := by
  unfold runloopTop
  split <;> rfl

theorem runloopTop_pending_eq (f : NFiber) : (runloopTop f).pending = f.pending := by
  unfold runloopTop
  split <;> rfl

theorem injectYield_waitFields (m : NativeMachine) (f : NFiber) (yielding : Bool)
    (it : Iter EffName EffThunk Val Err Defect FiberId Ann Ctx Stores)
    (h : injectYield m f yielding = some it) :
    it.fiber.parked = f.parked ∧ it.fiber.pending = f.pending := by
  unfold injectYield at h
  split at h
  · injection h with h'; subst h'; exact ⟨rfl, rfl⟩
  · cases h

theorem iteration_pending (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (f : NFiber) (yielding : Bool)
    (park : f.parked = .notParked) (pending : f.pending = []) :
    letI := evaluatorFor p table
    PendingShape (iteration (interpOf p table) m f yielding).fiber :=
  parking_pending (Moves.iteration_parking p table (interpOf p table) m f yielding) park pending

abbrev NIter := Iter EffName EffThunk Val Err Defect FiberId Ann Ctx Stores
/-- Only a parked or stuck result may carry a park into `settle`. -/
def ReadyOutcome (it : NIter) : Prop :=
  match it.outcome with
  | .parked | .stuck _ => True
  | _ => it.fiber.parked = .notParked

/-- The installed-park outcome clause discharges the existing ready judgment. -/
theorem parking_ready {m : NativeMachine} {f : NFiber} {it : Moves.ParkIter}
    (held : Moves.Parking m f it) (park : f.parked = .notParked) : ReadyOutcome it := by
  cases held with
  | kept hp _ _ =>
    cases outcome : it.outcome <;> simp only [ReadyOutcome, outcome]
    all_goals exact hp.trans park
  | installed _ _ _ _ _ outcome =>
    rcases outcome with parked | ⟨why, stuck⟩
    · simp only [ReadyOutcome, parked]
    · simp only [ReadyOutcome, stuck]

theorem stepFrame_ready (interp : NInterp) (m : NativeMachine)
    (f : NFiber) (yielding : Bool) (park : f.parked = .notParked) :
    ReadyOutcome (evaluatePrim.stepFrame interp m f yielding) :=
  parking_ready (Moves.stepFrame_parking interp m f yielding) park

theorem finalizerOr_ready (interp : NInterp) (m : NativeMachine)
    (f : NFiber) (yielding : Bool) (exit : ExitV) (park : f.parked = .notParked) :
    ReadyOutcome (evaluatePrim.finalizerOr interp m f yielding exit) :=
  parking_ready (Moves.finalizerOr_parking interp m f yielding exit) park

theorem countdownPark_unparked (interp : NInterp) (m : NativeMachine) (f : NFiber)
    (targets : List FiberId) (resume : Resume EffName) (failFast : Bool)
    (park : f.parked = .notParked)
    (hp : (countdownPark interp m f targets resume failFast).2.2 = false) :
    (countdownPark interp m f targets resume failFast).2.1.parked = .notParked := by
  cases hw : countdownWalk { m with nextToken := m.nextToken + 1 } targets [] with
  | mk exits wait =>
    cases wait with
    | none => simpa only [countdownPark, hw] using park
    | some wait => simp only [countdownPark, hw] at hp; cases hp

theorem countdown_ready (interp : NInterp) (m : NativeMachine) (f : NFiber)
    (yielding : Bool) (targets : List FiberId) (resume : Resume EffName) (failFast : Bool)
    (park : f.parked = .notParked) :
    let r := countdownPark interp m f targets resume failFast
    ReadyOutcome ⟨r.1, r.2.1, yielding, if r.2.2 then .parked else .continue_, []⟩ := by
  cases hp : (countdownPark interp m f targets resume failFast).2.2 with
  | false =>
    simpa only [ReadyOutcome, hp, Bool.false_eq_true, if_false] using
      countdownPark_unparked interp m f targets resume failFast park hp
  | true => simp only [ReadyOutcome, hp, if_true]

theorem countdown_readyOf (interp : NInterp) (m : NativeMachine) (f : NFiber)
    (yielding : Bool) (targets : List FiberId) (resume : Resume EffName) (failFast : Bool)
    (park : f.parked = .notParked) :
    let r := countdownPark interp m f targets resume failFast
    ReadyOutcome ⟨r.1, r.2.1, yielding, FiberAction.outcomeOf r.1 r.2.2, []⟩ := by
  cases hs : (countdownPark interp m f targets resume failFast).1.stuck with
  | none => simpa only [FiberAction.outcomeOf, hs] using
      countdown_ready interp m f yielding targets resume failFast park
  | some why => simp only [FiberAction.outcomeOf, hs, ReadyOutcome]

theorem withFiber_ready (interp : NInterp) (m : NativeMachine)
    (f : NFiber) (yielding : Bool) (action : NAction) (park : f.parked = .notParked) :
    ReadyOutcome (evaluatePrim.withFiber interp m f yielding action) :=
  parking_ready (Moves.withFiber_parking interp m f yielding action) park

theorem evaluatePrim_ready (interp : NInterp) (m : NativeMachine)
    (f : NFiber) (yielding : Bool) (park : f.parked = .notParked) :
    ReadyOutcome (evaluatePrim interp m f yielding) :=
  parking_ready (Moves.evaluatePrim_parking interp m f yielding) park

theorem exitScoped_ready (p : NativeEff) (m : NativeMachine)
    (f : NFiber) (yielding : Bool) (exit : ExitV) (park : f.parked = .notParked) :
    ReadyOutcome (exitScoped p m f yielding exit) :=
  parking_ready (Moves.exitScoped_parking p m f yielding exit) park

theorem evaluateNative_ready (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (f : NFiber) (yielding : Bool) (park : f.parked = .notParked) :
    ReadyOutcome (evaluateNative p m f yielding table) :=
  parking_ready (Moves.evaluateNative_parking p table m f yielding) park

theorem iteration_ready (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (f : NFiber) (yielding : Bool) (park : f.parked = .notParked) :
    letI := evaluatorFor p table
    ReadyOutcome (iteration (interpOf p table) m f yielding) :=
  parking_ready (Moves.iteration_parking p table (interpOf p table) m f yielding) park

/-- A park installed by one evaluation uses exactly the input machine's next token. -/
def FreshPark (m : NativeMachine) (it : NIter) : Prop :=
  ∀ token, it.fiber.parked = .withGuard token →
    token = m.nextToken ∧ token < it.machine.nextToken

theorem freshPark_unparked (m : NativeMachine) (it : NIter)
    (park : it.fiber.parked = .notParked) : FreshPark m it := by
  intro token hp
  rw [park] at hp
  cases hp

theorem freshPark_minted {m : NativeMachine} {it : NIter}
    (park : it.fiber.parked = .withGuard m.nextToken)
    (bound : m.nextToken < it.machine.nextToken) : FreshPark m it := by
  intro token hp
  have ht : m.nextToken = token := Parked.withGuard.inj (park.symm.trans hp)
  exact ⟨ht.symm, ht ▸ bound⟩

/-- The same classification exposes the minted token and its current bound. -/
theorem parking_fresh {m : NativeMachine} {f : NFiber} {it : Moves.ParkIter}
    (held : Moves.Parking m f it) (park : f.parked = .notParked) : FreshPark m it := by
  cases held with
  | kept hp _ _ => exact freshPark_unparked m it (hp.trans park)
  | installed wait token fresh hp _ _ =>
    exact freshPark_minted (hp.trans (congrArg Parked.withGuard token)) fresh

theorem stepFrame_freshPark (interp : NInterp) (m : NativeMachine)
    (f : NFiber) (yielding : Bool) (park : f.parked = .notParked) :
    FreshPark m (evaluatePrim.stepFrame interp m f yielding) :=
  parking_fresh (Moves.stepFrame_parking interp m f yielding) park

theorem finalizerOr_freshPark (interp : NInterp) (m : NativeMachine)
    (f : NFiber) (yielding : Bool) (exit : ExitV) (park : f.parked = .notParked) :
    FreshPark m (evaluatePrim.finalizerOr interp m f yielding exit) :=
  parking_fresh (Moves.finalizerOr_parking interp m f yielding exit) park

theorem countdown_freshPark (interp : NInterp) (m : NativeMachine) (f : NFiber)
    (yielding : Bool) (targets : List FiberId) (resume : Resume EffName) (failFast : Bool)
    (outcome : Effect4.Machine.Outcome EffName EffThunk Val Err Defect FiberId Ann)
    (nested : List NCmd) (park : f.parked = .notParked) :
    let r := countdownPark interp m f targets resume failFast
    FreshPark m ⟨r.1, r.2.1, yielding, outcome, nested⟩ := by
  cases hw : countdownWalk { m with nextToken := m.nextToken + 1 } targets [] with
  | mk exits wait =>
    cases wait with
    | none =>
      simp only [countdownPark, hw]
      exact freshPark_unparked _ _ park
    | some wait =>
      simp only [countdownPark, hw]
      apply freshPark_minted rfl
      simp only [RunMachine.emit, RunMachine.modify]
      split <;> exact Nat.lt_succ_self _

theorem withFiber_freshPark (interp : NInterp) (m : NativeMachine)
    (f : NFiber) (yielding : Bool) (action : NAction) (park : f.parked = .notParked) :
    FreshPark m (evaluatePrim.withFiber interp m f yielding action) :=
  parking_fresh (Moves.withFiber_parking interp m f yielding action) park

theorem evaluatePrim_freshPark (interp : NInterp) (m : NativeMachine)
    (f : NFiber) (yielding : Bool) (park : f.parked = .notParked) :
    FreshPark m (evaluatePrim interp m f yielding) :=
  parking_fresh (Moves.evaluatePrim_parking interp m f yielding) park

theorem exitScoped_freshPark (p : NativeEff) (m : NativeMachine)
    (f : NFiber) (yielding : Bool) (exit : ExitV) (park : f.parked = .notParked) :
    FreshPark m (exitScoped p m f yielding exit) :=
  parking_fresh (Moves.exitScoped_parking p m f yielding exit) park

theorem evaluateNative_freshPark (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (f : NFiber) (yielding : Bool) (park : f.parked = .notParked) :
    FreshPark m (evaluateNative p m f yielding table) :=
  parking_fresh (Moves.evaluateNative_parking p table m f yielding) park

theorem iteration_freshPark (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (f : NFiber) (yielding : Bool) (park : f.parked = .notParked) :
    letI := evaluatorFor p table
    FreshPark m (iteration (interpOf p table) m f yielding) :=
  parking_fresh (Moves.iteration_parking p table (interpOf p table) m f yielding) park

end Effect4.Program.Guard.ReturnFields
