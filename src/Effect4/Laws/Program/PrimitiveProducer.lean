import Effect4.Laws.Program.FrameMoves
import Effect4.Laws.Machine.Eliminators

/-!
Concept: reactive-scheduling R11 and store-typing R4.
Question: evaluation-moves, HeapSites.heap_sites_keep, and Timeout's original numeric goals.
The producer retains actual interpreter lookups and the returned iteration.
Consumers: Footprint, NativeExecutor, NativeHeapExecution, and executed store certificates.
This proof evidence supplies no source admission, phase permission, or progress by itself.
-/
set_option autoImplicit false
namespace Effect4.Program.Moves
open Effect4 Effect4.Machine Effect4.Program

abbrev NIteration := Iter EffName EffThunk Val Err Defect FiberId Ann Ctx Stores

/-- The actual primitive producer, including operations that leave references unchanged.
The constructors describe existing evaluator families; they introduce no executable evaluator. -/
inductive PrimitiveProducer (interp : NInterp) (m : NativeMachine) (f : NFiber)
    (yielding : Bool) : NIteration → Prop where
  | step (unparked : interp.parkOf f.frame.current = none)
      (ordinary : ∀ thunk, f.frame.current = .withFiber thunk → interp.withFiberOf thunk = none)
      (noSync : ∀ thunk, f.frame.current ≠ .sync thunk)
      (noSuccess : ∀ value, f.frame.current ≠ .success value)
      (noFailure : ∀ cause, f.frame.current ≠ .failure cause)
      (noYield : ∀ priority, f.frame.current ≠ .yieldNowWith priority)
      (noAsync : ∀ register signal cancel, f.frame.current ≠ .async register signal cancel) :
      PrimitiveProducer interp m f yielding (evaluatePrim.stepFrame interp m f yielding)
  | finalizer (exit : ExitV) (current : f.frame.current = Prim.ofExit exit) :
      PrimitiveProducer interp m f yielding (evaluatePrim.finalizerOr interp m f yielding exit)
  | action (thunk : EffThunk) (action : NAction)
      (current : f.frame.current = .withFiber thunk)
      (unparked : interp.parkOf f.frame.current = none)
      (found : interp.withFiberOf thunk = some action) :
      PrimitiveProducer interp m f yielding (evaluatePrim.withFiber interp m f yielding action)
  | sync (thunk : EffThunk) (state : Stores) (value : Val)
      (current : f.frame.current = .sync thunk)
      (unparked : interp.parkOf f.frame.current = none)
      (found : interp.syncState thunk m.state = some (state, value)) :
      PrimitiveProducer interp m f yielding
        ⟨{m with state}, {f with frame := {f.frame with current := .success value}},
          yielding, .answered, [.drainDue], []⟩
  | fallback (thunk : EffThunk) (current : f.frame.current = .sync thunk)
      (unparked : interp.parkOf f.frame.current = none)
      (missing : interp.syncState thunk m.state = none) :
      PrimitiveProducer interp m f yielding
        ⟨m, {f with frame := {f.frame with current := .success (interp.syncValue thunk)}},
          yielding, .answered, [], []⟩
  | yieldNow (priority : Nat) (current : f.frame.current = .yieldNowWith priority) :
      PrimitiveProducer interp m f yielding
        (let grown := {m with nextToken := m.nextToken + 1}
         let before := {f with
           frame := {f.frame with current := .success interp.voidValue}
           dispatcher := f.dispatcher.enqueue priority
             (.resume f.id m.nextToken (.success interp.voidValue))}
         let parked := before.park ⟨m.nextToken, [], [], .void, false⟩
         ⟨(grown.arm f.id).emit [.parkedOn f.id m.nextToken], parked, yielding, .parked, [], []⟩)
  | asyncImmediate (register : EffName) (signal : Bool) (cancel : Option EffName)
      (state : Stores) (code : NCode)
      (current : f.frame.current = .async register signal cancel)
      (registered : interp.registerAsync register f.id m.nextToken m.state = (state, some code)) :
      PrimitiveProducer interp m f yielding
        ⟨{m with state, nextToken := m.nextToken + 1},
          {f with frame := {f.frame with current := code}}, yielding, .continue_, [.drainDue], []⟩
  | asyncParked (register : EffName) (signal : Bool) (cancel : Option EffName) (state : Stores)
      (current : f.frame.current = .async register signal cancel)
      (registered : interp.registerAsync register f.id m.nextToken m.state = (state, none)) :
      PrimitiveProducer interp m f yielding
        (let grown := {m with state, nextToken := m.nextToken + 1}
         let before := if signal || cancel.isSome then
           {f with frame := {f.frame with stack := Prim.asyncFinalizer (interp.cancelName (cancel.getD interp.abortName) f.id m.nextToken) :: f.frame.stack}}
           else f
         let parked := before.park ⟨m.nextToken, [], [], .void, false⟩
         ⟨grown.emit [.parkedOn parked.id m.nextToken], parked, yielding, .parked, [], []⟩)
  | rejectedPark (cause : CauseV) (park : interp.parkOf f.frame.current = some (.error cause)) :
      PrimitiveProducer interp m f yielding
        ⟨m, {f with frame := {f.frame with current := .failure cause}}, yielding, .continue_, [], []⟩
  | racePark (race : Nat) (park : interp.parkOf f.frame.current = some (.ok (.race race))) :
      PrimitiveProducer interp m f yielding (registerRace m f yielding race)
  | countdownPark (targets : List FiberId) (next : NativeMachine) (returned : NFiber)
      (parked : Bool) (edits : List (FiberEdit Err Defect FiberId Ann))
      (park : interp.parkOf f.frame.current = some (.ok (.awaitAll targets)))
      (counted : countdownParkEdits interp m f targets .exitsValue false = (next, returned, parked, edits)) :
      PrimitiveProducer interp m f yielding
        ⟨next, returned, yielding, (if parked then .parked else .continue_), [], edits⟩
  | joinMissing (target : FiberId) (mode : Supervision.ObserverMode)
      (park : interp.parkOf f.frame.current = some (.ok (.join target mode)))
      (missing : m.fiber? target = none) :
      PrimitiveProducer interp m f yielding ⟨m, f, yielding, .stuck (.unknownFiber target), [], []⟩
  | joinExited (target : FiberId) (mode : Supervision.ObserverMode) (other : NFiber) (exit : ExitV)
      (park : interp.parkOf f.frame.current = some (.ok (.join target mode)))
      (found : m.fiber? target = some other) (exited : other.exit = some exit) :
      PrimitiveProducer interp m f yielding
        ⟨m, {f with frame := {f.frame with current := interp.exitValue exit mode}}, yielding, .continue_, [], []⟩
  | joinWaiting (target : FiberId) (mode : Supervision.ObserverMode) (other : NFiber)
      (park : interp.parkOf f.frame.current = some (.ok (.join target mode)))
      (found : m.fiber? target = some other) (live : other.exit = none) :
      PrimitiveProducer interp m f yielding
        (let grown := {m with nextToken := m.nextToken + 1}
         let name := interp.cancelName interp.parkCancelName f.id m.nextToken
         let before := {f with frame := {f.frame with stack := Prim.asyncFinalizer name :: f.frame.stack}}
         let parked := before.park ⟨m.nextToken, [], [], .void, false⟩
         ⟨grown.emit [.parkedOn f.id m.nextToken], parked, yielding, .parked, [],
           [.observe target (.resumeAwait f.id m.nextToken mode)]⟩)

/-- The one generated primitive classification retains its actual producer evidence.
Every source, reference, and frame consumer reads this witness instead of reclassifying evaluation. -/
@[semantics "reactive-scheduling" (requirement := R11)]
theorem evaluatePrim_producer (interp : NInterp) (m : NativeMachine) (f : NFiber) (yielding : Bool) :
    PrimitiveProducer interp m f yielding (evaluatePrim interp m f yielding) := by
  fun_cases evaluatePrim interp m f yielding
  case case1 priority current token grown before parked => exact .yieldNow priority current
  case case2 register signal cancel current token state grown code registered =>
    exact .asyncImmediate register signal cancel state code current registered
  case case3 register signal cancel current token state grown before parked registered =>
    exact .asyncParked register signal cancel state current registered
  case case4 cause park noYield noAsync => exact .rejectedPark cause park
  case case5 race park noYield noAsync => exact .racePark race park
  case case6 targets park next returned parked edits counted noYield noAsync =>
    exact .countdownPark targets next returned parked edits park counted
  case case7 target mode park missing noYield noAsync => exact .joinMissing target mode park missing
  case case8 target mode park other found exit exited noYield noAsync =>
    exact .joinExited target mode other exit park found exited
  case case9 target mode park other found live token grown cancel before parked noYield noAsync =>
    exact .joinWaiting target mode other park found live
  case case10 noPark thunk current action found noYield noAsync =>
    exact .action thunk action current noPark found
  case case11 noPark thunk current missing noYield noAsync =>
    refine .step noPark ?_ ?_ ?_ ?_ noYield noAsync
    · intro other same
      rw [current] at same
      cases same
      exact missing
    · intro other same; rw [current] at same; cases same
    · intro value same; rw [current] at same; cases same
    · intro cause same; rw [current] at same; cases same
  case case12 noPark thunk current state value synced noYield noAsync =>
    exact .sync thunk state value current noPark synced
  case case13 noPark thunk current missing noYield noAsync => exact .fallback thunk current noPark missing
  case case14 noPark value current noYield noAsync => exact .finalizer (.success value) current
  case case15 noPark cause current noYield noAsync => exact .finalizer (.failure cause) current
  case case16 noPark noYield noAsync noWithFiber noSync noSuccess noFailure =>
    exact .step noPark (fun thunk same => False.elim (noWithFiber thunk same))
      noSync noSuccess noFailure noYield noAsync

end Effect4.Program.Moves
