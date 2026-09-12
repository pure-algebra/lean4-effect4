import Effect4.Laws.Program.Guard.NativeState
import Effect4.Laws.Program.Guard.ReturnFields

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1200000
namespace Effect4.Program.Guard.NativeStateExternal
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Guard
open Effect4.Program.Guard.NativeState
abbrev NInterp := RunInterp EffName EffThunk Val Err Defect FiberId Ann Ctx Stores
abbrev NIter := Iter EffName EffThunk Val Err Defect FiberId Ann Ctx Stores

/-- This condition concerns only the new local host guard, before the returned
fiber is installed in the stored machine. -/
def ExternalParkKeys (before : NativeMachine) (it : NIter) : Prop :=
  ∀ token request, it.fiber.parked = .withGuard token →
    externalRequest it.fiber.frame.current = some request →
    internalKeys it.machine ⊆ internalKeys before

theorem ExternalParkKeys.unparked (m : NativeMachine) (it : NIter)
    (park : it.fiber.parked = .notParked) : ExternalParkKeys m it := by
  intro token request hp _
  rw [park] at hp
  cases hp

theorem ExternalParkKeys.noExternal (m : NativeMachine) (it : NIter)
    (code : externalRequest it.fiber.frame.current = none) : ExternalParkKeys m it := by
  intro token request _ hr
  rw [code] at hr
  cases hr

theorem stepFrame_external (interp : NInterp) (m : NativeMachine)
    (f : NFiber) (yielding : Bool) (park : f.parked = .notParked) :
    ExternalParkKeys m (evaluatePrim.stepFrame interp m f yielding) := by
  unfold evaluatePrim.stepFrame
  cases h : f.frame.step interp.toPrimInterp with
  | mk step events => cases step <;> exact .unparked _ _ park

theorem finalizerOr_external (interp : NInterp) (m : NativeMachine)
    (f : NFiber) (yielding : Bool) (exit : ExitV) (park : f.parked = .notParked) :
    ExternalParkKeys m (evaluatePrim.finalizerOr interp m f yielding exit) := by
  unfold evaluatePrim.finalizerOr
  repeat' first
    | exact .unparked _ _ park
    | exact stepFrame_external _ _ _ _ park
    | dsimp only
    | split

theorem countdown_external (interp : NInterp) (m : NativeMachine)
    (f : NFiber) (yielding : Bool) (targets : List FiberId) (resume : Resume EffName)
    (failFast : Bool) (outcome : Effect4.Machine.Outcome EffName EffThunk Val Err Defect FiberId Ann)
    (nested : List NCmd) (park : f.parked = .notParked)
    (code : externalRequest f.frame.current = none) :
    let result := countdownPark interp m f targets resume failFast
    ExternalParkKeys m ⟨result.1, result.2.1, yielding, outcome, nested⟩ := by
  unfold countdownPark
  dsimp only
  split
  · exact .unparked _ _ park
  · exact .noExternal _ _ code

theorem withFiber_external (interp : NInterp) (m : NativeMachine)
    (f : NFiber) (yielding : Bool) (action : NAction)
    (park : f.parked = .notParked) (code : externalRequest f.frame.current = none) :
    ExternalParkKeys m (evaluatePrim.withFiber interp m f yielding action) := by
  cases action <;> simp only [evaluatePrim.withFiber, evaluatePrim.interruptAs,
    spawn, start, beginRace]
  all_goals repeat' first
    | exact countdown_external _ _ _ _ _ _ _ _ _ park code
    | exact .unparked _ _ park
    | exact .noExternal _ _ rfl
    | split
  all_goals simp_all

theorem parkOf_noExternal (p : NativeEff) (table : RowTable) (completed)
    (code : NCode) (kind : Except CauseV ParkKind)
    (h : (interpAt p completed table).parkOf code = some kind) :
    externalRequest code = none := by
  cases code <;> try rfl
  simp only [interpAt, interpOf] at h
  cases h

theorem async_external (p : NativeEff) (table : RowTable) (completed)
    (m : NativeMachine) (f : NFiber) (yielding : Bool) (register : EffName)
    (signal : Bool) (cancel : Option EffName) (hc : f.frame.current = .async register signal cancel)
    (park : f.parked = .notParked) :
    ExternalParkKeys m (evaluatePrim (interpAt p completed table) m f yielding) := by
  simp only [evaluatePrim, hc]
  cases register
  case external op request =>
    have same := registerExternal_internal_state p table op request f.id m.nextToken m.state
    repeat' first
      | solve
        | intro token result hp hr key hk
          simpa only [internalKeys, RunMachine.emit, interpAt, same.1, same.2] using hk
      | dsimp only
      | split
  all_goals repeat' first
    | exact .unparked _ _ park
    | solve
      | apply ExternalParkKeys.noExternal
        simp only [RunFiber.park, hc, externalRequest]
    | dsimp only
    | split

theorem evaluatePrim_external (p : NativeEff) (table : RowTable) (completed)
    (m : NativeMachine) (f : NFiber) (yielding : Bool) (park : f.parked = .notParked) :
    ExternalParkKeys m (evaluatePrim (interpAt p completed table) m f yielding) := by
  cases hc : f.frame.current
  case async register signal cancel => exact async_external p table completed m f yielding register signal cancel hc park
  all_goals simp only [evaluatePrim, hc]
  all_goals repeat' first
    | exact .unparked _ _ park
    | exact .noExternal _ _ rfl
    | solve | apply ExternalParkKeys.noExternal; simp only [hc, externalRequest]
    | exact stepFrame_external _ _ _ _ park
    | exact finalizerOr_external _ _ _ _ _ park
    | exact withFiber_external _ _ _ _ _ park (by simp only [externalRequest, *])
    | solve | apply countdown_external _ _ _ _ _ _ _ _ _ park; simp only [hc, externalRequest]
    | dsimp only
    | split
  all_goals try (simp_all only [registerRace]; contradiction)
  all_goals try (unfold registerRace; split <;> exact .unparked _ _ park)

theorem exitScoped_external (p : NativeEff) (m : NativeMachine)
    (f : NFiber) (yielding : Bool) (exit : ExitV) (park : f.parked = .notParked) :
    ExternalParkKeys m (exitScoped p m f yielding exit) := by
  unfold exitScoped
  repeat' first
    | exact .unparked _ _ park
    | exact evaluatePrim_external _ _ _ _ _ _ park
    | dsimp only
    | split

theorem evaluateNative_external (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (f : NFiber) (yielding : Bool) (park : f.parked = .notParked) :
    ExternalParkKeys m (evaluateNative p m f yielding table) := by
  unfold evaluateNative
  repeat' first
    | exact .unparked _ _ park
    | exact evaluatePrim_external _ _ _ _ _ _ park
    | exact exitScoped_external _ _ _ _ _ park
    | dsimp only
    | split

theorem iteration_external (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (f : NFiber) (yielding : Bool) (park : f.parked = .notParked) :
    letI := evaluatorFor p table
    ExternalParkKeys m (iteration (interpOf p table) m f yielding) := by
  letI := evaluatorFor p table
  have park' : (countOp (runloopTop f)).parked = .notParked :=
    (Effect4.Program.Guard.ReturnFields.runloopTop_parked f).trans park
  unfold iteration
  dsimp only
  cases hy : injectYield m (countOp (runloopTop f)) yielding with
  | none => exact evaluateNative_external p table m _ _ park'
  | some it =>
    unfold injectYield at hy
    split at hy
    · cases hy
      exact evaluateNative_external p table _ _ _ park'
    · cases hy

end Effect4.Program.Guard.NativeStateExternal
