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
      f.running := by
  unfold evaluatePrim.stepFrame
  cases hs : f.frame.step interp.toPrimInterp with
  | mk step events => cases step <;> rfl

theorem finalizerOr_running (interp : NInterp) (m : NativeMachine)
    (f : NFiber) (yielding : Bool) (exit : ExitV) :
    (evaluatePrim.finalizerOr interp m f yielding exit).fiber.running =
      f.running := by
  cases exit <;> unfold evaluatePrim.finalizerOr <;> dsimp only
  all_goals
    split
    · split
      · rfl
      · exact stepFrame_running _ _ _ _
    · exact stepFrame_running _ _ _ _

theorem withFiber_running (interp : NInterp) (m : NativeMachine)
    (f : NFiber) (yielding : Bool) (action : NAction) :
    (evaluatePrim.withFiber interp m f yielding action).fiber.running =
      f.running := by
  cases action <;>
    simp only [evaluatePrim.withFiber,
      evaluatePrim.interruptAs, spawn, start, countdownPark, beginRace,
      RunFiber.park, FrameFiber.uninterruptible, FrameFiber.interruptibleRegion,
      FrameFiber.setFiberInterruptible]
  all_goals repeat' first | rfl | split
  all_goals simp_all

theorem evaluatePrim_running (interp : NInterp) (m : NativeMachine)
    (f : NFiber) (yielding : Bool) :
    (evaluatePrim interp m f yielding).fiber.running =
      f.running := by
  simp only [evaluatePrim, registerRace, countdownPark, RunFiber.park]
  repeat' first
    | exact stepFrame_running _ _ _ _
    | exact finalizerOr_running _ _ _ _ _
    | exact withFiber_running _ _ _ _ _
    | rfl
    | split
  all_goals simp_all
  all_goals repeat' first | rfl | split

theorem exitScoped_running (p : NativeEff) (m : NativeMachine)
    (f : NFiber) (yielding : Bool) (exit : ExitV) :
    (exitScoped p m f yielding exit).fiber.running =
      f.running := by
  cases exit <;> simp only [exitScoped]
  all_goals repeat' first
    | exact evaluatePrim_running _ _ _ _
    | rfl
    | rfl
    | split

theorem evaluateNative_running (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (f : NFiber) (yielding : Bool) :
    (evaluateNative p m f yielding table).fiber.running =
      f.running := by
  simp only [evaluateNative]
  repeat' first
    | exact evaluatePrim_running _ _ _ _
    | exact exitScoped_running _ _ _ _ _
    | rfl
    | split

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
      f.running := by
  letI := evaluatorFor p table
  cases hi : injectYield m (countOp (runloopTop f)) yielding with
  | none =>
    simpa only [iteration, hi] using
      (evaluateNative_running p table m (countOp (runloopTop f)) yielding).trans
        (runloopTop_running f)
  | some it =>
    simpa only [iteration, hi] using
      (evaluateNative_running p table it.machine it.fiber it.yielding).trans
        ((injectYield_running m _ yielding it hi).trans (runloopTop_running f))


theorem pendingShape_of_unparked (f : NFiber) (park : f.parked = .notParked)
    (pending : f.pending = []) : PendingShape f := by
  simp only [PendingShape, park, pending]

theorem pendingShape_park (f : NFiber) (wait : Pending EffName Val Err Defect FiberId Ann)
    (hp : f.pending = []) : PendingShape (f.park wait) := by
  exact ⟨wait, by simp only [RunFiber.park, hp, List.nil_append], rfl⟩

theorem stepFrame_pending (interp : NInterp) (m : NativeMachine)
    (f : NFiber) (yielding : Bool) (park : f.parked = .notParked) (hp : f.pending = []) :
    PendingShape (evaluatePrim.stepFrame interp m f yielding).fiber := by
  unfold evaluatePrim.stepFrame
  cases hs : f.frame.step interp.toPrimInterp with
  | mk step events => cases step <;> exact pendingShape_of_unparked _ park hp

theorem finalizerOr_pending (interp : NInterp) (m : NativeMachine)
    (f : NFiber) (yielding : Bool) (exit : ExitV) (park : f.parked = .notParked) (hp : f.pending = []) :
    PendingShape (evaluatePrim.finalizerOr interp m f yielding exit).fiber := by
  cases exit <;> unfold evaluatePrim.finalizerOr <;> dsimp only
  all_goals repeat' first
    | exact pendingShape_of_unparked _ park hp
    | exact stepFrame_pending _ _ _ _ park hp
    | split

theorem withFiber_pending (interp : NInterp) (m : NativeMachine)
    (f : NFiber) (yielding : Bool) (action : NAction) (park : f.parked = .notParked) (hp : f.pending = []) :
    PendingShape (evaluatePrim.withFiber interp m f yielding action).fiber := by
  cases action <;>
    simp only [evaluatePrim.withFiber,
      evaluatePrim.interruptAs, spawn, start, countdownPark, beginRace]
  all_goals repeat' first
    | exact pendingShape_of_unparked _ park hp
    | exact pendingShape_park _ _ hp
    | split
  all_goals simp_all [PendingShape, RunFiber.park]

theorem evaluatePrim_pending (interp : NInterp) (m : NativeMachine)
    (f : NFiber) (yielding : Bool) (park : f.parked = .notParked) (hp : f.pending = []) :
    PendingShape (evaluatePrim interp m f yielding).fiber := by
  simp only [evaluatePrim, registerRace, countdownPark]
  repeat' first
    | exact stepFrame_pending _ _ _ _ park hp
    | exact finalizerOr_pending _ _ _ _ _ park hp
    | exact withFiber_pending _ _ _ _ _ park hp
    | exact pendingShape_of_unparked _ park hp
    | exact pendingShape_park _ _ hp
    | split
  all_goals simp only [countdownPark]
  all_goals repeat' first | exact pendingShape_of_unparked _ park hp | exact pendingShape_park _ _ hp | split
  all_goals simp_all [PendingShape, RunFiber.park]

theorem exitScoped_pending (p : NativeEff) (m : NativeMachine)
    (f : NFiber) (yielding : Bool) (exit : ExitV) (park : f.parked = .notParked) (hp : f.pending = []) :
    PendingShape (exitScoped p m f yielding exit).fiber := by
  cases exit <;> simp only [exitScoped]
  all_goals repeat' first
    | exact evaluatePrim_pending _ _ _ _ park hp
    | exact pendingShape_of_unparked _ park hp
    | split

theorem evaluateNative_pending (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (f : NFiber) (yielding : Bool) (park : f.parked = .notParked) (hp : f.pending = []) :
    PendingShape (evaluateNative p m f yielding table).fiber := by
  simp only [evaluateNative]
  repeat' first
    | exact evaluatePrim_pending _ _ _ _ park hp
    | exact exitScoped_pending _ _ _ _ _ park hp
    | exact pendingShape_of_unparked _ park hp
    | split

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
    PendingShape (iteration (interpOf p table) m f yielding).fiber := by
  letI := evaluatorFor p table
  have hp : (countOp (runloopTop f)).parked = .notParked := (runloopTop_parked f).trans park
  have hn : (countOp (runloopTop f)).pending = [] := (runloopTop_pending_eq f).trans pending
  cases hi : injectYield m (countOp (runloopTop f)) yielding with
  | none =>
    simpa only [iteration, hi] using evaluateNative_pending p table m _ yielding hp hn
  | some it =>
    have fields := injectYield_waitFields m _ yielding it hi
    simpa only [iteration, hi] using evaluateNative_pending p table it.machine it.fiber it.yielding
      (fields.1.trans hp) (fields.2.trans hn)

abbrev NIter := Iter EffName EffThunk Val Err Defect FiberId Ann Ctx Stores
/-- Only a parked or stuck result may carry a park into `settle`. -/
def ReadyOutcome (it : NIter) : Prop :=
  match it.outcome with
  | .parked | .stuck _ => True
  | _ => it.fiber.parked = .notParked

theorem stepFrame_ready (interp : NInterp) (m : NativeMachine)
    (f : NFiber) (yielding : Bool) (park : f.parked = .notParked) :
    ReadyOutcome (evaluatePrim.stepFrame interp m f yielding) := by
  unfold evaluatePrim.stepFrame
  cases hs : f.frame.step interp.toPrimInterp with
  | mk step events => cases step <;> exact park

theorem finalizerOr_ready (interp : NInterp) (m : NativeMachine)
    (f : NFiber) (yielding : Bool) (exit : ExitV) (park : f.parked = .notParked) :
    ReadyOutcome (evaluatePrim.finalizerOr interp m f yielding exit) := by
  cases exit <;> unfold evaluatePrim.finalizerOr <;> dsimp only
  all_goals repeat' first
    | exact park
    | exact True.intro
    | exact stepFrame_ready _ _ _ _ park
    | split

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
    ReadyOutcome (evaluatePrim.withFiber interp m f yielding action) := by
  cases action <;>
    simp only [evaluatePrim.withFiber,
      evaluatePrim.interruptAs, spawn, start, beginRace]
  all_goals repeat' first
    | exact countdown_ready _ _ _ _ _ _ _ park
    | exact countdown_readyOf _ _ _ _ _ _ _ park
    | exact park
    | exact True.intro
    | split
  all_goals simp_all [ReadyOutcome]

theorem evaluatePrim_ready (interp : NInterp) (m : NativeMachine)
    (f : NFiber) (yielding : Bool) (park : f.parked = .notParked) :
    ReadyOutcome (evaluatePrim interp m f yielding) := by
  simp only [evaluatePrim, registerRace]
  repeat' first
    | exact stepFrame_ready _ _ _ _ park
    | exact finalizerOr_ready _ _ _ _ _ park
    | exact withFiber_ready _ _ _ _ _ park
    | exact countdown_ready _ _ _ _ _ _ _ park
    | exact countdown_readyOf _ _ _ _ _ _ _ park
    | exact park
    | exact True.intro
    | split
  all_goals simp_all [ReadyOutcome]

theorem exitScoped_ready (p : NativeEff) (m : NativeMachine)
    (f : NFiber) (yielding : Bool) (exit : ExitV) (park : f.parked = .notParked) :
    ReadyOutcome (exitScoped p m f yielding exit) := by
  cases exit <;> simp only [exitScoped]
  all_goals repeat' first
    | exact evaluatePrim_ready _ _ _ _ park
    | exact park
    | exact True.intro
    | split

theorem evaluateNative_ready (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (f : NFiber) (yielding : Bool) (park : f.parked = .notParked) :
    ReadyOutcome (evaluateNative p m f yielding table) := by
  simp only [evaluateNative]
  repeat' first
    | exact evaluatePrim_ready _ _ _ _ park
    | exact exitScoped_ready _ _ _ _ _ park
    | exact park
    | exact True.intro
    | split

theorem iteration_ready (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (f : NFiber) (yielding : Bool) (park : f.parked = .notParked) :
    letI := evaluatorFor p table
    ReadyOutcome (iteration (interpOf p table) m f yielding) := by
  letI := evaluatorFor p table
  have hp : (countOp (runloopTop f)).parked = .notParked := (runloopTop_parked f).trans park
  cases hi : injectYield m (countOp (runloopTop f)) yielding with
  | none =>
    simpa only [iteration, hi] using evaluateNative_ready p table m _ yielding hp
  | some it =>
    have fields := injectYield_waitFields m _ yielding it hi
    simpa only [iteration, hi] using evaluateNative_ready p table it.machine it.fiber it.yielding
      (fields.1.trans hp)

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

theorem stepFrame_freshPark (interp : NInterp) (m : NativeMachine)
    (f : NFiber) (yielding : Bool) (park : f.parked = .notParked) :
    FreshPark m (evaluatePrim.stepFrame interp m f yielding) := by
  unfold evaluatePrim.stepFrame
  cases hs : f.frame.step interp.toPrimInterp with
  | mk step events => cases step <;> exact freshPark_unparked _ _ park

theorem finalizerOr_freshPark (interp : NInterp) (m : NativeMachine)
    (f : NFiber) (yielding : Bool) (exit : ExitV) (park : f.parked = .notParked) :
    FreshPark m (evaluatePrim.finalizerOr interp m f yielding exit) := by
  cases exit <;> unfold evaluatePrim.finalizerOr <;> dsimp only
  all_goals repeat' first
    | exact freshPark_unparked _ _ park
    | exact stepFrame_freshPark _ _ _ _ park
    | split

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
    FreshPark m (evaluatePrim.withFiber interp m f yielding action) := by
  cases action <;>
    simp only [evaluatePrim.withFiber,
      evaluatePrim.interruptAs, spawn, start, beginRace]
  all_goals repeat' first
    | exact countdown_freshPark _ _ _ _ _ _ _ _ _ park
    | exact freshPark_unparked _ _ park
    | exact freshPark_minted rfl (Nat.lt_succ_self _)
    | split
  all_goals simp_all

theorem evaluatePrim_freshPark (interp : NInterp) (m : NativeMachine)
    (f : NFiber) (yielding : Bool) (park : f.parked = .notParked) :
    FreshPark m (evaluatePrim interp m f yielding) := by
  simp only [evaluatePrim, registerRace]
  repeat' first
    | exact stepFrame_freshPark _ _ _ _ park
    | exact finalizerOr_freshPark _ _ _ _ _ park
    | exact withFiber_freshPark _ _ _ _ _ park
    | exact countdown_freshPark _ _ _ _ _ _ _ _ _ park
    | exact freshPark_unparked _ _ park
    | exact freshPark_minted rfl (Nat.lt_succ_self _)
    | split
  all_goals simp_all

theorem exitScoped_freshPark (p : NativeEff) (m : NativeMachine)
    (f : NFiber) (yielding : Bool) (exit : ExitV) (park : f.parked = .notParked) :
    FreshPark m (exitScoped p m f yielding exit) := by
  cases exit <;> simp only [exitScoped]
  all_goals repeat' first
    | exact evaluatePrim_freshPark _ _ _ _ park
    | exact freshPark_unparked _ _ park
    | split

theorem evaluateNative_freshPark (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (f : NFiber) (yielding : Bool) (park : f.parked = .notParked) :
    FreshPark m (evaluateNative p m f yielding table) := by
  simp only [evaluateNative]
  repeat' first
    | exact evaluatePrim_freshPark _ _ _ _ park
    | exact exitScoped_freshPark _ _ _ _ _ park
    | exact freshPark_unparked _ _ park
    | split

theorem iteration_freshPark (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (f : NFiber) (yielding : Bool) (park : f.parked = .notParked) :
    letI := evaluatorFor p table
    FreshPark m (iteration (interpOf p table) m f yielding) := by
  letI := evaluatorFor p table
  have hp : (countOp (runloopTop f)).parked = .notParked := (runloopTop_parked f).trans park
  cases hi : injectYield m (countOp (runloopTop f)) yielding with
  | none =>
    simpa only [iteration, hi] using evaluateNative_freshPark p table m _ yielding hp
  | some it =>
    have fields := injectYield_waitFields m _ yielding it hi
    have next : it.machine.nextToken = m.nextToken := by
      unfold injectYield at hi
      split at hi
      · injection hi with h; subst h; rfl
      · cases hi
    have result := evaluateNative_freshPark p table it.machine it.fiber it.yielding
      (fields.1.trans hp)
    intro token hpark
    have out := result token (by simpa only [iteration, hi] using hpark)
    refine ⟨out.1.trans next, ?_⟩
    simpa only [iteration, hi] using out.2


end Effect4.Program.Guard.ReturnFields
