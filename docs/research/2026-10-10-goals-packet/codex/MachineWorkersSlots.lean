import MachineAnswerFlow
import Effect4.Laws.Machine.AnswerFlowFrames
import MachineWorkersWriters
import Effect4.Laws.Program.NativeScope

/-!
Concept: store-typing R4, scope-lifetime-finalization R11.
Question: initialization slots serve the unchanged Workers.Assertions.logs_step.
Reach: actual native initialization binders; the world retains the actual owner and store.
Limit: this probe gives no initial-command exclusivity or whole-history closure.
Consumer: the source's saved root binders consume the post-allocation answer class.
-/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
namespace MachineWorkersSlots
open Effect4 Effect4.Machine Effect4.Program Effect4.Laws.Auto
open Test.Dogfood.Scenario

structure World where
  owner : FiberId
  state : Stores

inductive Kind
  | root | allocated (index : Nat) | gate
  | yielded (refs deferred : Nat)

def bindings : List Val := [.cell ⟨0⟩, .cell ⟨1⟩, .cell ⟨2⟩, .cell ⟨3⟩, .promise ⟨0⟩]

def initialRequest : Nat → Term
  | 0 | 1 => .field .required (.record [("v", false, .list .nat)] ["v"]
      (.cons (.app "nil" .nil) .nil)) "v"
  | 2 => .field .required (.record [("v", false, .list (.prod .nat .nat))] ["v"]
      (.cons (.app "nil" .nil) .nil)) "v"
  | _ => .lit (.nat 0)

def initialValue : Nat → Val
  | 0 | 1 | 2 => .list []
  | _ => .nat 0

def initialTail (total index : Nat) : NativeEff :=
  match Node.at_ (.eff (Programs.workersProgram total)) (List.replicate index 1) with
  | some (.eff (.bind _ tail)) => tail
  | _ => .succeed (.lit .unit)

/-- The actual first four source binders contain precisely these native reference allocations.
Consumer: the root stage's next primitive has the allocation answer class. -/
theorem initializer_head (total index : Nat) (small : index < 4) :
    ∃ tail, Node.at_ (.eff (Programs.workersProgram total)) (List.replicate index 1) =
      some (.eff (.bind (.perform .refMake (initialRequest index)) tail)) := by
  rcases index with _ | index
  · refine ⟨initialTail total 0, ?_⟩
    kernel_rfl
  rcases index with _ | index
  · refine ⟨initialTail total 1, ?_⟩
    kernel_rfl
  rcases index with _ | index
  · refine ⟨initialTail total 2, ?_⟩
    kernel_rfl
  rcases index with _ | index
  · refine ⟨initialTail total 3, ?_⟩
    kernel_rfl
  have impossible : False := by omega
  exact impossible.elim

theorem initial_request_value (index : Nat) (env : List Val) :
    evalTerm env (initialRequest index) = some (initialValue index) := by
  rcases index with _ | index
  · kernel_rfl
  rcases index with _ | index
  · kernel_rfl
  rcases index with _ | index
  · kernel_rfl
  kernel_rfl

/-- A positive source budget exposes the actual initializer bind, retaining its original Point.
The child keeps its own budget, including a source-fuel frontier. -/
theorem initializer_compile (total index : Nat) (point : Point) (fuel : Nat)
    (small : index < 4) (path : point.path = List.replicate index 1)
    (amount : point.fuel = fuel + 1) :
    resolve (Programs.workersProgram total) point =
      .onSuccess (compileEff (.perform .refMake (initialRequest index)) (point.child 0)) (.cont point) := by
  obtain ⟨tail, found⟩ := initializer_head total index small
  rw [← path] at found
  rw [Agreement.resolve_of_at found, Agreement.compileEff_bind _ _ amount]

/-- The source's typed record projection produces the actual initial heap value. -/
theorem initializer_operation (index : Nat) (point : Point) (fuel : Nat)
    (amount : point.fuel = fuel + 1) :
    compileEff (.perform .refMake (initialRequest index)) point =
      .sync (.op (.refMake (initialValue index))) := by
  rw [Agreement.compileEff_perform_sync .refMake _ amount rfl, initial_request_value]
  rfl

/-- Every live answer and current code retains initialization ownership or the stable phase. -/
def Phase (world : World) : Prop :=
  world.owner = ⟨0⟩ ∨ (4 ≤ world.state.refs.length ∧ 1 ≤ world.state.deferreds.cells.length)

/-- The root reaches an initializer with the exact completed binding prefix.
Both transient store lengths belong to the current root position, not to copied saved bodies. -/
def RootStage (world : World) (index : Nat) (point : Point) : Prop :=
  index ≤ 4 ∧ world.owner = ⟨0⟩ ∧ point.path = List.replicate index 1 ∧
    point.env = bindings.take index ∧ world.state.refs.length = index ∧
    world.state.deferreds.cells.length = 0

/-- The successful allocation class describes the post-operation store.
The callback can therefore extend its lexical prefix without guessing the returned key. -/
def ValueAt (world : World) : Kind → Val → Prop
  | .root, _ => Phase world
  | .allocated index, value => Phase world ∧ value = .cell ⟨index⟩ ∧
      world.state.refs.length = index + 1 ∧ world.state.deferreds.cells.length = 0
  | .gate, value => value = .promise ⟨0⟩ ∧
      4 ≤ world.state.refs.length ∧ 1 ≤ world.state.deferreds.cells.length

  | .yielded refs deferred, value => Phase world ∧ value = .unit ∧
      world.state.refs.length = refs ∧ world.state.deferreds.cells.length = deferred

inductive CodeAt (total : Nat) (world : World) : Kind → NCode → Prop
  | success (kind : Kind) (value : Val) (good : ValueAt world kind value) :
      CodeAt total world kind (.success value)
  | failure (kind : Kind) (cause : CauseV) (phase : Phase world) :
      CodeAt total world kind (.failure cause)
  | root (index : Nat) (point : Point) (stage : RootStage world index point) :
      CodeAt total world .root (resolve (Programs.workersProgram total) point)
  | allocating (index : Nat) (point : Point) (initial : Val) (small : index < 4)
      (valueEq : initial = initialValue index) (stage : RootStage world index point) :
      CodeAt total world (.allocated index) (.sync (.op (.refMake initial)))
  | gateAllocating (point : Point) (stage : RootStage world 4 point) :
      CodeAt total world .gate (.sync (.op .deferredMake))
  | stable (point : Point) (ready : 4 ≤ world.state.refs.length ∧ 1 ≤ world.state.deferreds.cells.length)
      (lexical : SourceScope.At (Programs.workersProgram total) point)
      (leading : point.env.take 5 = bindings) :
      CodeAt total world .root (resolve (Programs.workersProgram total) point)

  | yielding (priority refs deferred : Nat) (phase : Phase world)
      (refsEq : world.state.refs.length = refs)
      (deferredEq : world.state.deferreds.cells.length = deferred) :
      CodeAt total world (.yielded refs deferred) (.yieldNowWith priority)

def model (total : Nat) : AnswerFlow.Model (ν := EffName) (σ := EffThunk)
    (β := Val) (ε := Err) (δ := Defect) (ι := FiberId) (α := Ann) World Kind where
  future first last := first.owner = last.owner ∧ first.state.refs.length ≤ last.state.refs.length ∧
    first.state.deferreds.cells.length ≤ last.state.deferreds.cells.length
  future_refl _ := ⟨rfl, Nat.le_refl _, Nat.le_refl _⟩
  future_trans _ _ _ first last :=
    ⟨first.1.trans last.1, Nat.le_trans first.2.1 last.2.1, Nat.le_trans first.2.2 last.2.2⟩
  value := ValueAt
  cause world _ _ := Phase world
  code := CodeAt total
  finalizer _ _ _ := none
  success := fun _ kind value good => .success kind value good
  failure := fun _ kind cause phase => .failure kind cause phase

/-- The initial-stage exclusivity consumer reads the condition from every current code. -/
theorem code_phase {total : Nat} {world : World} {kind : Kind} {code : NCode}
    (held : CodeAt total world kind code) : Phase world := by
  cases held with
  | success kind value good => cases kind with
    | root => exact good
    | allocated _ => exact good.1
    | gate => exact Or.inr good.2
    | yielded _ _ => exact good.1
  | failure _ _ phase => exact phase
  | root _ _ stage => exact Or.inl stage.2.1
  | allocating _ _ _ _ _ stage => exact Or.inl stage.2.1
  | gateAllocating _ stage => exact Or.inl stage.2.1
  | stable _ ready _ _ => exact Or.inr ready
  | yielding _ _ _ phase _ _ => exact phase

/-- Appending the actual allocated key extends the concrete prefix through the fourth reference. -/
theorem prefix_append (index : Nat) (small : index < 4) :
    bindings.take index ++ [Val.cell ⟨index⟩] = bindings.take (index + 1) := by
  rcases index with _ | index
  · kernel_rfl
  rcases index with _ | index
  · kernel_rfl
  rcases index with _ | index
  · kernel_rfl
  rcases index with _ | index
  · kernel_rfl
  omega

/-- A saved initializer consumes the exact key and post-state that its body produces.
This is a real source contA callback at every total, view and compile fuel. -/
theorem initializer_callback (total : Nat) (view : List (FiberId × ExitV)) (table : RowTable)
    (world : World) (index : Nat) (point : Point) (small : index < 4)
    (stage : RootStage world index point) :
    ∀ nextWorld, (model total).future world nextWorld → ∀ value,
      (model total).value nextWorld (.allocated index) value →
      (model total).code nextWorld .root
        ((interpAt (Programs.workersProgram total) view table).contA (.cont point) value) := by
  intro nextWorld future value good
  obtain ⟨_, valueEq, refs, deferred⟩ := good
  subst value
  change CodeAt total nextWorld .root
    (resolve (Programs.workersProgram total) ({point with completed := view}.childWith 1 (.cell ⟨index⟩)))
  refine .root (index + 1) _ ?_
  obtain ⟨bound, owner, path, env, _, _⟩ := stage
  refine ⟨by omega, future.1 ▸ owner, ?_, ?_, refs, deferred⟩
  · change point.path ++ [1] = List.replicate (index + 1) 1
    rw [path, List.replicate_succ']
  · change point.env ++ [Val.cell ⟨index⟩] = bindings.take (index + 1)
    rw [env]
    exact prefix_append index small

/-- The actual saved root binder now consumes the shared future-state contract. -/
theorem initializer_saved (total : Nat) (view : List (FiberId × ExitV)) (table : RowTable)
    (world : World) (index : Nat) (point : Point) (body : NCode) (small : index < 4)
    (stage : RootStage world index point) :
    AnswerFlow.SavedAt (model total) (interpAt (Programs.workersProgram total) view table).toPrimInterp
      world (.allocated index) .root (.onSuccess body (.cont point)) := by
  exact AnswerFlow.saved_success (model total) _ world (.allocated index) .root body (.cont point)
    (initializer_callback total view table world index point small stage)
    (fun _ _ _ good => good)

/-- The actual initializer push gives its body the allocation answer class.
Consumer: the next native reference operation supplies that class in its post-state. -/
theorem initializer_push (total : Nat) (view : List (FiberId × ExitV)) (table : RowTable)
    (world : World) (index : Nat) (point : Point) (initial : Val)
    (fiber : FrameFiber EffName EffThunk Val Err Defect FiberId Ann)
    (small : index < 4) (stage : RootStage world index point)
    (sourceValue : initial = initialValue index)
    (current : fiber.current = .onSuccess (.sync (.op (.refMake initial))) (.cont point))
    (stack : AnswerFlow.StackAt (model total)
      (interpAt (Programs.workersProgram total) view table).toPrimInterp
      world .root .root fiber.stack) :
    ∃ next events,
      fiber.step (interpAt (Programs.workersProgram total) view table).toPrimInterp = (.running next, events) ∧
      AnswerFlow.FrameAt (model total)
        (interpAt (Programs.workersProgram total) view table).toPrimInterp world .root next :=
  AnswerFlow.push_success (model total) _ world (.allocated index) .root .root fiber
    (.sync (.op (.refMake initial))) (.cont point) current
    (.allocating index point initial small sourceValue stage)
    (initializer_saved total view table world index point _ small stage) stack

/-- The actual compiled source initializer consumes the push contract at every total.
The positive child budget exposes the real allocation; a smaller budget remains a live frontier. -/
theorem initializer_source_push (total : Nat) (view : List (FiberId × ExitV)) (table : RowTable)
    (world : World) (index : Nat) (point : Point) (fuel : Nat)
    (fiber : FrameFiber EffName EffThunk Val Err Defect FiberId Ann)
    (small : index < 4) (stage : RootStage world index point)
    (amount : point.fuel = fuel + 2)
    (current : fiber.current = resolve (Programs.workersProgram total) point)
    (stack : AnswerFlow.StackAt (model total)
      (interpAt (Programs.workersProgram total) view table).toPrimInterp
      world .root .root fiber.stack) :
    ∃ next events,
      fiber.step (interpAt (Programs.workersProgram total) view table).toPrimInterp = (.running next, events) ∧
      AnswerFlow.FrameAt (model total)
        (interpAt (Programs.workersProgram total) view table).toPrimInterp world .root next := by
  have childFuel : (point.child 0).fuel = fuel + 1 := by
    change point.fuel - 1 = fuel + 1
    rw [amount]
    omega
  have code := initializer_compile total index point (fuel + 1) small stage.2.2.1 amount
  rw [initializer_operation index (point.child 0) fuel childFuel] at code
  exact initializer_push total view table world index point (initialValue index) fiber small stage rfl
    (current.trans code) stack

/-- The actual native allocator produces the answer class consumed by its saved binder.
The current source stage supplies the length; this law does not manufacture a history witness. -/
theorem initializer_native (total : Nat) (table : RowTable) (machine : Api.Machine)
    (fiber : RunFiber EffName EffThunk Val Err Defect FiberId Ann Ctx)
    (index : Nat) (point : Point) (initial : Val) (yielding : Bool)
    (stage : RootStage ⟨fiber.id, machine.state⟩ index point)
    (current : fiber.frame.current = .sync (.op (.refMake initial)))
    (stack : AnswerFlow.StackAt (model total)
      (interpAt (Programs.workersProgram total) machine.completedExits table).toPrimInterp
      ⟨fiber.id, machine.state⟩ (.allocated index) .root fiber.frame.stack) :
    evaluateNative (Programs.workersProgram total) machine fiber yielding table =
      ⟨{machine with state := {machine.state with refs := machine.state.refs ++ [initial]}},
        {fiber with frame := {fiber.frame with current := .success (.cell ⟨index⟩)}},
        yielding, .answered, [.drainDue]⟩ ∧
    AnswerFlow.FrameAt (model total)
      (interpAt (Programs.workersProgram total) machine.completedExits table).toPrimInterp
      ⟨fiber.id, {machine.state with refs := machine.state.refs ++ [initial]}⟩ .root
      {fiber.frame with current := .success (.cell ⟨index⟩)} := by
  obtain ⟨_, owner, _, _, length, deferred⟩ := stage
  constructor
  · apply ControlSteps.native_sync_op _ table machine fiber yielding _ _ _ current
    change some (_, Val.cell ⟨machine.state.refs.length⟩) = _
    rw [length]
  · have future : (model total).future ⟨fiber.id, machine.state⟩
        ⟨fiber.id, {machine.state with refs := machine.state.refs ++ [initial]}⟩ :=
      ⟨rfl, by
        change machine.state.refs.length ≤ (machine.state.refs ++ [initial]).length
        rw [List.length_append, List.length_singleton]
        omega, Nat.le_refl _⟩
    apply AnswerFlow.sync_answer (model total) _ future
      (.allocated index) .root fiber.frame (.cell ⟨index⟩) _ stack
    change Phase _ ∧ Val.cell ⟨index⟩ = Val.cell ⟨index⟩ ∧
      (machine.state.refs ++ [initial]).length = index + 1 ∧
      machine.state.deferreds.cells.length = 0
    exact ⟨Or.inl owner, rfl, by rw [List.length_append, List.length_singleton, length], deferred⟩

/-- The post-allocation answer resumes the real source binder in the new store.
Consumer: the initialization prefix advances before the first worker fork. -/
theorem initializer_resume (total : Nat) (view : List (FiberId × ExitV)) (table : RowTable)
    (world nextWorld : World) (index : Nat) (point : Point) (body : NCode)
    (fiber : FrameFiber EffName EffThunk Val Err Defect FiberId Ann)
    (small : index < 4) (stage : RootStage world index point)
    (future : (model total).future world nextWorld)
    (good : ValueAt nextWorld (.allocated index) (.cell ⟨index⟩))
    (noInterrupt : fiber.deferredInterrupt = false)
    (stack : AnswerFlow.StackAt (model total)
      (interpAt (Programs.workersProgram total) view table).toPrimInterp
      world .root .root fiber.stack) :
    ({fiber with stack := .onSuccess body (.cont point) :: fiber.stack}).resumeValue
        (interpAt (Programs.workersProgram total) view table).toPrimInterp (.cell ⟨index⟩) none =
      (.running {fiber with current :=
        (interpAt (Programs.workersProgram total) view table).contA (.cont point) (.cell ⟨index⟩)},
        [.popped (.onSuccess body (.cont point))]) ∧
    AnswerFlow.FrameAt (model total)
      (interpAt (Programs.workersProgram total) view table).toPrimInterp nextWorld .root
      {fiber with current :=
        (interpAt (Programs.workersProgram total) view table).contA (.cont point) (.cell ⟨index⟩)} := by
  apply AnswerFlow.resume_success (model total) _ nextWorld (.allocated index) .root .root
    fiber body (.cont point) (.cell ⟨index⟩) none noInterrupt good
  · intro exit absent
    cases absent
  · exact AnswerFlow.saved_mono (model total) _ future
      (initializer_saved total view table world index point body small stage)
  · exact AnswerFlow.stack_mono (model total) _ future stack

/-- The fifth binder enters the stable source phase with the actual gate key.
Consumer: child starts require this phase before they can run the workers. -/
theorem gate_callback (total : Nat) (view : List (FiberId × ExitV)) (table : RowTable)
    (world : World) (point : Point) (stage : RootStage world 4 point) :
    ∀ nextWorld, (model total).future world nextWorld → ∀ value,
      ValueAt nextWorld .gate value →
      CodeAt total nextWorld .root
        ((interpAt (Programs.workersProgram total) view table).contA (.cont point) value) := by
  intro nextWorld _ value good
  obtain ⟨equal, ready⟩ := good
  subst value
  change CodeAt total nextWorld .root
    (resolve (Programs.workersProgram total) ({point with completed := view}.childWith 1 (.promise ⟨0⟩)))
  refine .stable _ ready ?_ ?_
  · change SourceScope.levelAt (.eff (Programs.workersProgram total)) 0 (point.path ++ [1]) =
      some (point.env ++ [Val.promise ⟨0⟩]).length
    rw [stage.2.2.1, stage.2.2.2.1]
    kernel_rfl
  change (point.env ++ [Val.promise ⟨0⟩]).take 5 = bindings
  rw [stage.2.2.2.1]
  kernel_rfl

/-- The actual gate binder consumes its post-allocation class in the shared saved contract. -/
theorem gate_saved (total : Nat) (view : List (FiberId × ExitV)) (table : RowTable)
    (world : World) (point : Point) (body : NCode) (stage : RootStage world 4 point) :
    AnswerFlow.SavedAt (model total) (interpAt (Programs.workersProgram total) view table).toPrimInterp
      world .gate .root (.onSuccess body (.cont point)) :=
  AnswerFlow.saved_success (model total) _ world .gate .root body (.cont point)
    (gate_callback total view table world point stage) (fun _ _ _ good => good)

/-- The gate push installs the post-allocation class before entering the worker region. -/
theorem gate_push (total : Nat) (view : List (FiberId × ExitV)) (table : RowTable)
    (world : World) (point : Point)
    (fiber : FrameFiber EffName EffThunk Val Err Defect FiberId Ann)
    (stage : RootStage world 4 point)
    (current : fiber.current = .onSuccess (.sync (.op .deferredMake)) (.cont point))
    (stack : AnswerFlow.StackAt (model total)
      (interpAt (Programs.workersProgram total) view table).toPrimInterp
      world .root .root fiber.stack) :
    ∃ next events,
      fiber.step (interpAt (Programs.workersProgram total) view table).toPrimInterp = (.running next, events) ∧
      AnswerFlow.FrameAt (model total)
        (interpAt (Programs.workersProgram total) view table).toPrimInterp world .root next :=
  AnswerFlow.push_success (model total) _ world .gate .root .root fiber
    (.sync (.op .deferredMake)) (.cont point) current (.gateAllocating point stage)
    (gate_saved total view table world point _ stage) stack

/-- The actual gate allocator produces the stable post-state and gate answer class. -/
theorem gate_native (total : Nat) (table : RowTable) (machine : Api.Machine)
    (fiber : RunFiber EffName EffThunk Val Err Defect FiberId Ann Ctx)
    (point : Point) (yielding : Bool) (stage : RootStage ⟨fiber.id, machine.state⟩ 4 point)
    (current : fiber.frame.current = .sync (.op .deferredMake))
    (stack : AnswerFlow.StackAt (model total)
      (interpAt (Programs.workersProgram total) machine.completedExits table).toPrimInterp
      ⟨fiber.id, machine.state⟩ .gate .root fiber.frame.stack) :
    evaluateNative (Programs.workersProgram total) machine fiber yielding table =
      ⟨{machine with state := {machine.state with deferreds := machine.state.deferreds.make.2}},
        {fiber with frame := {fiber.frame with current := .success (.promise ⟨0⟩)}},
        yielding, .answered, [.drainDue]⟩ ∧
    AnswerFlow.FrameAt (model total)
      (interpAt (Programs.workersProgram total) machine.completedExits table).toPrimInterp
      ⟨fiber.id, {machine.state with deferreds := machine.state.deferreds.make.2}⟩ .root
      {fiber.frame with current := .success (.promise ⟨0⟩)} := by
  obtain ⟨_, _, _, _, refs, deferred⟩ := stage
  have future : (model total).future ⟨fiber.id, machine.state⟩
      ⟨fiber.id, {machine.state with deferreds := machine.state.deferreds.make.2}⟩ := by
    refine ⟨rfl, Nat.le_refl _, ?_⟩
    change machine.state.deferreds.cells.length ≤ machine.state.deferreds.make.2.cells.length
    simp only [DeferredStore.make, List.length_append, List.length_singleton]
    omega
  constructor
  · apply ControlSteps.native_sync_op _ table machine fiber yielding _ _ _ current
    change some (_, Val.promise ⟨machine.state.deferreds.cells.length⟩) = _
    rw [deferred]
    rfl
  · apply AnswerFlow.sync_answer (model total) _ future .gate .root fiber.frame (.promise ⟨0⟩) _ stack
    refine ⟨rfl, ?_, ?_⟩
    · change 4 ≤ machine.state.refs.length
      rw [refs]
      exact Nat.le_refl _
    · change 1 ≤ machine.state.deferreds.make.2.cells.length
      simp only [DeferredStore.make, List.length_append, List.length_singleton]
      rw [deferred]
      exact Nat.le_refl _

/-- Later source binders retain the five actual values through arbitrary added answers.
Only nondecreasing store sizes are used; no current initializer receives a weakening rule. -/
theorem stable_bind_callback (total : Nat) (view : List (FiberId × ExitV)) (table : RowTable)
    (world : World) (point : Point)
    (ready : 4 ≤ world.state.refs.length ∧ 1 ≤ world.state.deferreds.cells.length)
    (leading : point.env.take 5 = bindings)
    (next : SourceScope.NextAt (Programs.workersProgram total) point 1 1) :
    ∀ nextWorld, (model total).future world nextWorld → ∀ value,
      ValueAt nextWorld .root value →
      CodeAt total nextWorld .root
        ((interpAt (Programs.workersProgram total) view table).contA (.cont point) value) := by
  intro nextWorld future value _
  change CodeAt total nextWorld .root
    (resolve (Programs.workersProgram total) ({point with completed := view}.childWith 1 value))
  refine .stable _ ⟨Nat.le_trans ready.1 future.2.1, Nat.le_trans ready.2 future.2.2⟩
    (SourceScope.childWith_at _ _ 1 value next) ?_
  change (point.env ++ [value]).take 5 = bindings
  have length : 5 ≤ point.env.length := by
    have bound := List.length_take_le' (i := 5) (l := point.env)
    rw [leading] at bound
    exact bound
  rw [List.take_append_of_le_length length, leading]

/-- The actual later saved binders consume the shared contract with the stable prefix. -/
theorem stable_bind_saved (total : Nat) (view : List (FiberId × ExitV)) (table : RowTable)
    (world : World) (point : Point) (body : NCode)
    (ready : 4 ≤ world.state.refs.length ∧ 1 ≤ world.state.deferreds.cells.length)
    (leading : point.env.take 5 = bindings)
    (next : SourceScope.NextAt (Programs.workersProgram total) point 1 1) :
    AnswerFlow.SavedAt (model total) (interpAt (Programs.workersProgram total) view table).toPrimInterp
      world .root .root (.onSuccess body (.cont point)) :=
  AnswerFlow.saved_success (model total) _ world .root .root body (.cont point)
    (stable_bind_callback total view table world point ready leading next) (fun _ _ _ good => good)

/-- The actual loaded machine supplies the first source stage without a history assumption.
Consumer: initialization exclusivity starts from this live root frame. -/
theorem load_frames (total : Nat) (fuel : Nat) (table : RowTable) :
    ∀ fiber ∈ (Api.load (Programs.workersProgram total) fuel).fibers,
      AnswerFlow.FrameAt (model total)
        (interpAt (Programs.workersProgram total) [] table).toPrimInterp
        ⟨fiber.id, (Api.load (Programs.workersProgram total) fuel).state⟩ .root fiber.frame := by
  intro fiber member
  change fiber ∈ [RunFiber.make Api.root (compile (Programs.workersProgram total) fuel) true
    (stores.budgetOf emptyCtx) emptyCtx] at member
  have equal := List.mem_singleton.mp member
  subst fiber
  change ∃ input, CodeAt total ⟨⟨0⟩, Stores.empty⟩ input (compile (Programs.workersProgram total) fuel) ∧
    AnswerFlow.StackAt (model total)
      (interpAt (Programs.workersProgram total) [] table).toPrimInterp
      ⟨⟨0⟩, Stores.empty⟩ input .root []
  refine ⟨Kind.root, ?_, ?_⟩
  · apply CodeAt.root 0 (rootPoint fuel)
    exact ⟨by omega, rfl, rfl, rfl, rfl, rfl⟩
  · exact .nil _ Kind.root


/-- Current annotations transport under exact owner and allocation-size agreement.
This does not weaken a transient initializer to an arbitrary later store. -/
theorem code_sizes (total : Nat) (world nextWorld : World)
    (owner : world.owner = nextWorld.owner)
    (refs : world.state.refs.length = nextWorld.state.refs.length)
    (deferred : world.state.deferreds.cells.length = nextWorld.state.deferreds.cells.length)
    {kind : Kind} {code : NCode} (held : CodeAt total world kind code) :
    CodeAt total nextWorld kind code := by
  have phase (good : Phase world) : Phase nextWorld := by
    change nextWorld.owner = ⟨0⟩ ∨
      (4 ≤ nextWorld.state.refs.length ∧ 1 ≤ nextWorld.state.deferreds.cells.length)
    rw [← owner, ← refs, ← deferred]
    exact good
  have stage {index : Nat} {point : Point} (good : RootStage world index point) :
      RootStage nextWorld index point := by
    obtain ⟨bound, initialOwner, path, env, refLength, deferredLength⟩ := good
    exact ⟨bound, owner ▸ initialOwner, path, env, refs ▸ refLength, deferred ▸ deferredLength⟩
  have value {kind : Kind} {answer : Val} (good : ValueAt world kind answer) :
      ValueAt nextWorld kind answer := by
    cases kind with
    | gate =>
      simp only [ValueAt] at good ⊢
      rw [← refs, ← deferred]
      exact good
    | root =>
      simp only [ValueAt, Phase] at good ⊢
      rw [← owner, ← refs, ← deferred]
      exact good
    | allocated index =>
      simp only [ValueAt, Phase] at good ⊢
      rw [← owner, ← refs, ← deferred]
      exact good
    | yielded count promises =>
      simp only [ValueAt, Phase] at good ⊢
      rw [← owner, ← refs, ← deferred]
      exact good
  cases held with
  | success kind answer good => exact .success kind answer (value good)
  | failure kind reason good => exact .failure kind reason (phase good)
  | root index point good => exact .root index point (stage good)
  | allocating index point initial small valueEq good =>
    exact .allocating index point initial small valueEq (stage good)
  | gateAllocating point good => exact .gateAllocating point (stage good)
  | stable point ready lexical leading =>
    exact .stable point ⟨refs ▸ ready.1, deferred ▸ ready.2⟩ lexical leading
  | yielding priority count promises good countEq promisesEq =>
    exact .yielding priority count promises (phase good) (refs ▸ countEq) (deferred ▸ promisesEq)

/-- A forced-yield saved constant consumes a response with the retained allocation sizes.
The actual history must justify this response class while the old source body is parked. -/
theorem yield_saved (total : Nat) (view : List (FiberId × ExitV)) (table : RowTable)
    (world : World) (kind : Kind) (priority : Nat) (code : NCode)
    (held : CodeAt total world kind code) :
    AnswerFlow.SavedAt (model total) (interpAt (Programs.workersProgram total) view table).toPrimInterp
      world (.yielded world.state.refs.length world.state.deferreds.cells.length) kind
      (.onSuccessConst (.yieldNowWith priority) code) := by
  apply AnswerFlow.saved_constant (model total) _ world _ kind (.yieldNowWith priority) code
  · intro nextWorld future answer good
    exact code_sizes total world nextWorld future.1 good.2.2.1.symm good.2.2.2.symm held
  · intro nextWorld future reason good
    exact good

/-- The actual forced-yield push retains an initializer body through the saved constant.
No copy of the source body becomes a second active annotation. -/
theorem yield_push (total : Nat) (view : List (FiberId × ExitV)) (table : RowTable)
    (world : World) (input output : Kind) (priority : Nat) (code : NCode)
    (fiber : FrameFiber EffName EffThunk Val Err Defect FiberId Ann)
    (current : fiber.current = .onSuccessConst (.yieldNowWith priority) code)
    (held : CodeAt total world input code)
    (stack : AnswerFlow.StackAt (model total)
      (interpAt (Programs.workersProgram total) view table).toPrimInterp world input output fiber.stack) :
    ∃ next events,
      fiber.step (interpAt (Programs.workersProgram total) view table).toPrimInterp = (.running next, events) ∧
      AnswerFlow.FrameAt (model total)
        (interpAt (Programs.workersProgram total) view table).toPrimInterp world output next := by
  exact AnswerFlow.push_constant (model total) _ world _ input output fiber
    (.yieldNowWith priority) code current
    (.yielding priority _ _ (code_phase held) rfl rfl)
    (yield_saved total view table world input priority code held) stack

/-- A real unit yield response resumes the saved original source body in the matching store.
Consumer: scheduler resumes at a transient initializer or the later stable phase. -/
theorem yield_resume (total : Nat) (view : List (FiberId × ExitV)) (table : RowTable)
    (world nextWorld : World) (input output : Kind) (priority : Nat) (code : NCode)
    (fiber : FrameFiber EffName EffThunk Val Err Defect FiberId Ann)
    (future : (model total).future world nextWorld)
    (good : ValueAt nextWorld (.yielded world.state.refs.length world.state.deferreds.cells.length) .unit)
    (held : CodeAt total world input code) (noInterrupt : fiber.deferredInterrupt = false)
    (stack : AnswerFlow.StackAt (model total)
      (interpAt (Programs.workersProgram total) view table).toPrimInterp world input output fiber.stack) :
    ({fiber with stack := .onSuccessConst (.yieldNowWith priority) code :: fiber.stack}).resumeValue
        (interpAt (Programs.workersProgram total) view table).toPrimInterp .unit none =
      (.running {fiber with current := code}, [.popped (.onSuccessConst (.yieldNowWith priority) code)]) ∧
    AnswerFlow.FrameAt (model total)
      (interpAt (Programs.workersProgram total) view table).toPrimInterp nextWorld output
      {fiber with current := code} := by
  apply AnswerFlow.resume_constant (model total) _ nextWorld
    (.yielded world.state.refs.length world.state.deferreds.cells.length) input output fiber
    (.yieldNowWith priority) code .unit none noInterrupt good
  · intro exit absent
    cases absent
  · exact AnswerFlow.saved_mono (model total) _ future (yield_saved total view table world input priority code held)
  · exact AnswerFlow.stack_mono (model total) _ future stack


/-- The real native yield producer supplies the unit class in its unchanged store.
The returned fiber is parked; its saved original body remains on the same ordered stack. -/
theorem yield_native (total : Nat) (table : RowTable) (machine : Api.Machine)
    (fiber : RunFiber EffName EffThunk Val Err Defect FiberId Ann Ctx)
    (priority : Nat) (output : Kind) (yielding : Bool)
    (phase : Phase ⟨fiber.id, machine.state⟩)
    (current : fiber.frame.current = .yieldNowWith priority)
    (stack : AnswerFlow.StackAt (model total)
      (interpAt (Programs.workersProgram total) machine.completedExits table).toPrimInterp
      ⟨fiber.id, machine.state⟩ (.yielded machine.state.refs.length machine.state.deferreds.cells.length)
      output fiber.frame.stack) :
    AnswerFlow.FrameAt (model total)
      (interpAt (Programs.workersProgram total) machine.completedExits table).toPrimInterp
      ⟨fiber.id, (evaluateNative (Programs.workersProgram total) machine fiber yielding table).machine.state⟩
      output (evaluateNative (Programs.workersProgram total) machine fiber yielding table).fiber.frame := by
  simp only [evaluateNative, current, evaluatePrim]
  exact AnswerFlow.sync_answer (model total) _ ((model total).future_refl _)
    (.yielded machine.state.refs.length machine.state.deferreds.cells.length) output fiber.frame .unit
    ⟨phase, rfl, rfl, rfl⟩ stack

/-- Retaining the phase alone does not retain a transient yield's allocation sizes.
This is a finite response-class control, not a counterexample to the history log bound. -/
theorem phase_does_not_retain_yield :
    ∃ world : World, Phase world ∧ ¬ ValueAt world (.yielded 0 0) .unit := by
  refine ⟨⟨⟨0⟩, {Stores.empty with refs := [.nat 0]}⟩, Or.inl rfl, ?_⟩
  intro good
  have impossible : 1 = 0 := good.2.2.1
  cases impossible

end MachineWorkersSlots
