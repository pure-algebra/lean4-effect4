import Test.Dogfood.Scenario.Atomic.StageTasks
import Test.Dogfood.Scenario.Atomic.NativeEffects
import Effect4.Laws.Program.ParkedShape

/-!
Concept: reactive-scheduling R11 and store-typing R4.
Consumer: the actual Atomic resumed-answer command and its stage history.
Actual native parks retain a void reply, a timer or an explicit await; action heads stay unparked.
-/
set_option autoImplicit false
namespace Test.Dogfood.Scenario.Atomic.StageConfiguration
open Effect4 Effect4.Machine Effect4.Program
open StageWorld

/-- Actual Atomic parks expose precisely the reply-consuming native heads. -/
inductive WaitHead : NCode → Prop
  | yielded : WaitHead (.success .unit)
  | async (register : EffName) (signal : Bool) (cancel : Option EffName) : WaitHead (.async register signal cancel)
  | park (kind : ParkKind) : WaitHead (.suspend (.park kind))
  | storedPark (kind : ParkKind) : WaitHead (.suspend (.store (.park kind)))

/-- Every actual stored park retains its reply-consuming head. -/
def Waits (machine : NativeMachine) : Prop := ∀ fiber ∈ machine.fibers, ParkedShape.HeldWith WaitHead fiber

/-- Actual native interference transports old waiting rows and initializes fresh rows unparked. -/
theorem Waits.native (root : NativeEff) (table : RowTable) (machine : NativeMachine)
    (fiber : SourceScope.SourceFiber) (yielding : Bool) (held : Waits machine) :
    Waits (evaluateNative root machine fiber yielding table).machine :=
  ParkedShape.interferes_with (Moves.evaluateNative_interferes root table machine fiber yielding) held

/-- Installing the actual actor retains the stored waiting observation. -/
theorem Waits.update (machine : NativeMachine) (fiber : SourceScope.SourceFiber)
    (held : Waits machine) (actor : ParkedShape.HeldWith WaitHead fiber) : Waits (machine.update fiber) := by
  intro row member
  obtain ⟨old, present, equal⟩ := List.mem_map.mp member
  rw [← equal]
  change ParkedShape.HeldWith WaitHead (if old.id = fiber.id then fiber else old)
  split
  · exact actor
  · exact held old present

/-- The actual native actor cannot remain parked on a source action head. -/
theorem native_wait_head (built : Api.Built) (accepted : Api.Author.build (shop .none) = .ok built)
    (world : StageWorld.World) (fresh : Fresh world) (machine : NativeMachine)
    (fiber : SourceScope.SourceFiber) (yielding : Bool)
    (role : StageRoles.FrameAt built.program built.table world fiber.id fiber.frame)
    (metadata : RowAt world fiber) (heap : HeapAt world machine.state) (counter : machine.nextId = world.nextId)
    (active : fiber.parked = .notParked) :
    ParkedShape.HeldWith WaitHead (evaluateNative built.program machine fiber yielding built.table).fiber := by
  rw [role_primitive_eq built accepted world machine fiber yielding role metadata]
  apply ParkedShape.primitive_with WaitHead WaitHead.yielded WaitHead.async WaitHead.park WaitHead.storedPark
    built.program machine.completedExits built.table machine fiber yielding active
  intro thunk action current unparked found
  cases role with
  | root identity owned =>
    obtain ⟨input, code, saved⟩ := owned
    obtain ⟨next, future, freshNext, nextCounter, nextHeap, actor, rows, same, effects, recipients⟩ :=
      RootGraph.action_result built accepted machine.completedExits world fresh machine fiber yielding input thunk action
        (current ▸ code) current heap counter saved found (fun _ => True) (fun _ _ _ => Or.inr True.intro)
    exact ParkedShape.unparked_with (effects.retainedPark.trans active)
  | daemon identity owned =>
    rcases DaemonGraph.action_shape built.program built.table thunk (current ▸ owned.1) with
      ⟨targets, who, equal⟩ | ⟨token, equal⟩
    · cases equal
      change some (.interruptAll targets who) = some action at found
      cases found
      exact ParkedShape.unparked_with active
    · cases equal
      change some (.dropObservers token) = some action at found
      cases found
      exact ParkedShape.unparked_with active
  | request owner member identity owned =>
    obtain ⟨input, code, saved⟩ := owned
    have ordinary := StageGraph.ordinary_shape built.program built.table owner machine.completedExits world input _ code
    exact False.elim (ordinary.2.1 thunk current)

/-- Each actual root wait head accepts the value supplied by an awaited exit. -/
theorem root_wait_values (built : Api.Built) (accepted : Api.Author.build (shop .none) = .ok built)
    (world : StageWorld.World) (input : StageWorld.Kind) (code : NCode)
    (owned : RootGraph.Owns input) (typed : RootGraph.CodeAt built.program built.table world input code)
    (head : WaitHead code) (value : Val) : ValueAt world input value := by
  cases head with
  | yielded =>
    have semantic := RootGraph.head built accepted world input _ typed owned []
    cases semantic with
    | success answer good => exact RootGraph.unit_value world input owned good value
  | async register signal cancel =>
    obtain ⟨millis, same, enabled, cleanup, owns, values⟩ :=
      RootGraph.async_shape built accepted world input register signal cancel typed
    exact values value
  | park kind =>
    exact (RootGraph.park_shape built accepted world [] input _ typed (.ok kind) rfl).2.2 value
  | storedPark kind =>
    exact (RootGraph.park_shape built accepted world [] input _ typed (.ok kind) rfl).2.2 value

/-- Replacing a parked root head by an actual reply retains its source answer and saved suffix. -/
theorem root_reply (built : Api.Built) (accepted : Api.Author.build (shop .none) = .ok built)
    (world : StageWorld.World) (frame : FrameFiber EffName EffThunk Val Err Defect FiberId Ann)
    (typed : RootGraph.FrameAt built.program built.table world frame) (head : WaitHead frame.current)
    (code : NCode) (reply : ReplyAt ⟨0⟩ code) :
    RootGraph.FrameAt built.program built.table world { frame with current := code } := by
  obtain ⟨input, current, saved⟩ := typed
  have owned := RootGraph.path_owned built.program built.table world input .ordinary frame.stack saved True.intro
  have values := root_wait_values built accepted world input frame.current owned current head
  refine ⟨input, ?_, saved⟩
  cases reply with
  | unit => exact .success (values .unit)
  | read cell small => exact .readReply cell owned values
  | exit result small =>
    cases result with
    | success value => exact .success (values value)
    | failure cause => exact .failure

/-- A parked request's actual current head is precisely its scheduler void result. -/
theorem request_wait_unit (root : NativeEff) (table : RowTable) (owner : Nat) (world : StageWorld.World)
    (frame : FrameFiber EffName EffThunk Val Err Defect FiberId Ann)
    (typed : StageGraph.FrameAt root table owner world frame) (head : WaitHead frame.current) :
    frame.current = .success .unit := by
  obtain ⟨input, code, saved⟩ := typed
  have ordinary := StageGraph.ordinary_shape root table owner [] world input frame.current code
  generalize equal : frame.current = program at head
  cases head with
  | yielded => rfl
  | async register signal cancel => exact False.elim (ordinary.2.2 register signal cancel equal)
  | park kind => rw [equal] at ordinary; cases ordinary.1
  | storedPark kind => rw [equal] at ordinary; cases ordinary.1

/-- Replacing a parked request head by its actual void reply retains the entire frame certificate. -/
theorem request_reply (root : NativeEff) (table : RowTable) (owner : Nat) (world : StageWorld.World)
    (frame : FrameFiber EffName EffThunk Val Err Defect FiberId Ann)
    (typed : StageGraph.FrameAt root table owner world frame) (head : WaitHead frame.current)
    (small : 1 ≤ owner) (code : NCode) (reply : ReplyAt ⟨owner + 1⟩ code) :
    StageGraph.FrameAt root table owner world { frame with current := code } := by
  cases reply with
  | unit =>
    have current := request_wait_unit root table owner world frame typed head
    have same : { frame with current := Prim.success Val.unit } = frame := by
      rw [← current]
    exact same.symm ▸ typed
  | read cell impossible =>
    change owner + 1 < 2 at impossible
    exact False.elim (Nat.not_lt_of_ge (Nat.succ_le_succ small) impossible)
  | exit result impossible =>
    change owner + 1 < 2 at impossible
    have lower : 2 ≤ owner + 1 := Nat.succ_le_succ small
    exact False.elim (Nat.not_lt_of_ge lower impossible)

/-- Every actual reply to a parked actor retains that actor's source role. -/
theorem role_reply (built : Api.Built) (accepted : Api.Author.build (shop .none) = .ok built)
    (world : StageWorld.World) (id : FiberId)
    (frame : FrameFiber EffName EffThunk Val Err Defect FiberId Ann)
    (typed : StageRoles.FrameAt built.program built.table world id frame) (head : WaitHead frame.current)
    (code : NCode) (reply : ReplyAt id code) :
    StageRoles.FrameAt built.program built.table world id { frame with current := code } := by
  cases typed with
  | root identity held =>
    subst id
    exact .root rfl (root_reply built accepted world frame held head code reply)
  | daemon identity held =>
    refine .daemon identity ?_
    refine ⟨?_, held.2⟩
    cases reply with
    | unit => exact .success _
    | read cell small => exact .readReply cell
    | exit result small => cases result with
      | success value => exact .success value
      | failure cause => exact .failure cause
  | request owner member identity held =>
    subst id
    have small : 1 ≤ owner := by
      by_cases positive : 1 ≤ owner
      · exact positive
      · have zero : owner = 0 := by omega
        have absent : (0 : Nat) ∉ requests := by decide
        exact False.elim (absent (zero ▸ member))
    exact .request owner member rfl (request_reply built.program built.table owner world frame held head small code reply)

/-- Actual parked rows expose their live role, excluding the inactive-row alternatives. -/
theorem Configuration.parked_role (root : NativeEff) (table : RowTable) (world : StageWorld.World)
    (machine : NativeMachine) (held : Configuration root table world machine) (guard : Guard.GuardState machine)
    (fiber : SourceScope.SourceFiber) (member : fiber ∈ machine.fibers) (parked : fiber.parked ≠ .notParked) :
    StageRoles.FrameAt root table world fiber.id fiber.frame := by
  rcases held.roles fiber member with role | exited | running
  · exact role
  · exact False.elim (parked (guard.exited fiber member exited).1)
  · have idle := guard.parkedIdle fiber member parked
    rw [running] at idle
    cases idle

/-- The actual matching-token resume installs the reply at the same stage world. -/
theorem Configuration.resume_update (built : Api.Built) (accepted : Api.Author.build (shop .none) = .ok built)
    (world : StageWorld.World) (machine : NativeMachine) (held : Configuration built.program built.table world machine)
    (waits : Waits machine) (guard : Guard.GuardState machine)
    (fiber : SourceScope.SourceFiber) (member : fiber ∈ machine.fibers) (token : Nat)
    (parked : fiber.parked = .withGuard token) (code : NCode) (reply : ReplyAt fiber.id code) :
    let resumed := { fiber with parked := Parked.notParked, pending := fiber.pending.filter (fun pending => pending.token ≠ token), frame := { fiber.frame with current := code } }
    Configuration built.program built.table world (machine.update resumed) ∧
      Waits (machine.update resumed) := by
  have notEmpty : fiber.parked ≠ .notParked := by rw [parked]; intro impossible; cases impossible
  have role := held.parked_role built.program built.table world machine guard fiber member notEmpty
  have head := waits fiber member notEmpty
  have actor := role_reply built accepted world fiber.id fiber.frame role head code reply
  have metadata := held.metadata fiber member
  refine ⟨held.update built.program built.table world machine _ (Or.inl actor) ?_, ?_⟩
  · exact ⟨metadata.recorded, metadata.published, metadata.childless, metadata.observers⟩
  · exact waits.update machine _ (ParkedShape.unparked_with rfl)

end Test.Dogfood.Scenario.Atomic.StageConfiguration
