import Test.Dogfood.Scenario.Atomic.SourcePaths
import Test.Dogfood.Scenario.SourceUse
import Effect4.Laws.Program.SourceOpportunityFrames

/-!
Concept: scope-lifetime-finalization R11.
Consumers: FinalizerRun.once_placed_pushes_once and Workers.Assertions.registrations_step.
These readers apply compiler initialization and actual push debits at the scenario source addresses.
They retain every Workers job count and every source environment and compile budget.
They establish no whole-history opportunity bound.
-/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
namespace Test.Dogfood.Scenario.SourceOpportunity
open Effect4 Effect4.Program Effect4.Machine Effect4.Laws.Auto
open Effect4.Program.SourceScope.Opportunities


/-- Every Workers acquisition query lies outside all release and finalizer children.
The checked source census retains every job count and both worker indices. -/
theorem workers_clear (total : Nat) : ∀ i ∈ [1, 2],
    ClearFinalizers (Programs.workersProgram total) (Programs.crewAcquire i) := by
  intro i member
  rcases List.mem_cons.mp member with rfl | tail
  · unfold ClearFinalizers
    kernel_rfl
  · have selected := List.mem_singleton.mp tail
    subst i
    unfold ClearFinalizers
    kernel_rfl


/-- All six actual Atomic request queries lie outside all finalizer children. -/
theorem atomic_all_clear_census :
    (Atomic.Store.shopProgram.map fun root => Atomic.requests.all fun i =>
      (Node.addresses (.eff root)).all fun path =>
        (Node.at_ (.eff root) path).all fun node => match node with
          | .eff (.acquireRelease _ _) | .eff (.onExit _ _) =>
              !(path ++ [1]).isPrefixOf (Atomic.SourcePaths.requestPath i)
          | _ => true) = some true := by
  kernel_rfl

/-- Successful admission retains the checked full Atomic source address census. -/
theorem atomic_all_clear (b : Api.Built) (built : Api.Author.build (Atomic.shop .none) = .ok b) :
    ∀ i ∈ Atomic.requests, ClearFinalizers b.program (Atomic.SourcePaths.requestPath i) := by
  have program : Atomic.Store.shopProgram = some b.program := by
    unfold Atomic.Store.shopProgram
    rw [(Api.Author.build_retains built).1]
    rfl
  have clear := atomic_all_clear_census
  rw [program] at clear
  exact List.all_eq_true.mp (Option.some.inj clear)

/-- The actual first Atomic query lies outside all release and finalizer children. -/
theorem atomic_clear_census :
    (Atomic.Store.shopProgram.map fun root =>
      (Node.addresses (.eff root)).all fun path =>
        (Node.at_ (.eff root) path).all fun node => match node with
          | .eff (.acquireRelease _ _) | .eff (.onExit _ _) =>
              !(path ++ [1]).isPrefixOf SourceUse.atomicFirst
          | _ => true) = some true := by
  kernel_rfl

/-- A successful Atomic build discharges the finalizer-child query restriction. -/
theorem atomic_clear (b : Api.Built) (built : Api.Author.build (Atomic.shop .none) = .ok b) :
    ClearFinalizers b.program SourceUse.atomicFirst := by
  have program : Atomic.Store.shopProgram = some b.program := by
    unfold Atomic.Store.shopProgram
    rw [(Api.Author.build_retains built).1]
    rfl
  have clear := atomic_clear_census
  rw [program] at clear
  exact Option.some.inj clear

/-- The actual first Atomic request exposes the selected registration opportunity. -/
theorem atomic_selected (env : List Val) (fuel : Nat) :
    (Atomic.Store.shopProgram.map fun root => push SourceUse.atomicFirst
      (resolve root {path := SourceUse.atomicFirst, env, fuel := fuel + 1, tape := []})) = some 1 := by
  kernel_rfl

/-- The successful actual shop build has exactly one opportunity at its selected request. -/
theorem atomic_one (b : Api.Built) (built : Api.Author.build (Atomic.shop .none) = .ok b)
    (env : List Val) (fuel : Nat) :
    current b.program SourceUse.atomicFirst
      (resolve b.program {path := SourceUse.atomicFirst, env, fuel := fuel + 1, tape := []}) = 1 := by
  have program : Atomic.Store.shopProgram = some b.program := by
    unfold Atomic.Store.shopProgram
    rw [(Api.Author.build_retains built).1]
    rfl
  have selected := atomic_selected env fuel
  rw [program] at selected
  have pushed := Option.some.inj selected
  dsimp only at pushed
  have lower := push_le_current b.program SourceUse.atomicFirst
    (resolve b.program {path := SourceUse.atomicFirst, env, fuel := fuel + 1, tape := []})
  rw [pushed] at lower
  have upper := resolve_le b.program SourceUse.atomicFirst
    {path := SourceUse.atomicFirst, env, fuel := fuel + 1, tape := []}
  exact Nat.le_antisymm upper lower

/-- Every actual Workers acquisition initializes one opportunity, at every job count. -/
theorem worker_one (total : Nat) (env : List Val) (fuel : Nat) :
    current (Programs.workersProgram total) (Programs.crewAcquire 1)
      (resolve (Programs.workersProgram total)
        {path := Programs.crewAcquire 1, env, fuel := fuel + 1, tape := []}) = 1 := by
  kernel_rfl

/-- The actual Workers acquisition retains one opportunity before receiving its value. -/
theorem worker_acquire_one (total : Nat) (env : List Val) (fuel : Nat) (context : Ctx) (scope : Nat) :
    let point : Point := {path := Programs.crewAcquire 1, env, fuel, tape := []}
    current (Programs.workersProgram total) (Programs.crewAcquire 1)
      (contAOf (Programs.workersProgram total) (.acquireIn point context) (.scopeHandle scope)) = 1 := by
  dsimp only
  exact acquire_in_one (Programs.workersProgram total)
    {path := Programs.crewAcquire 1, env, fuel, tape := []} context scope

/-- Its acquired value retains one opportunity in the exact registration template. -/
theorem worker_registration_one (total : Nat) (env : List Val) (fuel : Nat)
    (context : Ctx) (scope : Nat) (acquired : Val) :
    let point : Point := {path := Programs.crewAcquire 1, env, fuel, tape := []}
    current (Programs.workersProgram total) (Programs.crewAcquire 1)
      (contAOf (Programs.workersProgram total) (.acquired point context scope) acquired) = 1 :=
  acquired_one _ _ context scope acquired

/-- Every actual response carries zero opportunity to register that acquisition again. -/
theorem worker_response_zero (total : Nat) (env : List Val) (fuel : Nat)
    (context : Ctx) (acquired answer : Val) :
    let point : Point := {path := Programs.crewAcquire 1, env, fuel, tape := []}
    current (Programs.workersProgram total) (Programs.crewAcquire 1)
      (contAOf (Programs.workersProgram total)
        (.afterScopeAdd acquired (.foreign (point.capture acquired context))) answer) = 0 := by
  dsimp only
  exact response_zero (Programs.workersProgram total)
    {path := Programs.crewAcquire 1, env, fuel, tape := []} context acquired answer

/-- The actual first Atomic request spends its push while keeping only future callbacks saved. -/
theorem atomic_push_debit (b : Api.Built)
    (interp : PrimInterp EffName EffThunk Val Err Defect FiberId Ann)
    (f : FrameFiber EffName EffThunk Val Err Defect FiberId Ann)
    (body : NCode) (env : List Val) (fuel : Nat) :
    let point : Point := {path := SourceUse.atomicFirst, env, fuel, tape := []}
    frame b.program SourceUse.atomicFirst
      {f with current := body, stack := .onExit body (.fin point) false :: f.stack} + 1 =
      frame b.program SourceUse.atomicFirst {f with current := .onExit body (.fin point) false} ∧
    ({f with current := .onExit body (.fin point) false}).step interp =
      (.running {f with current := body, stack := .onExit body (.fin point) false :: f.stack},
        [.pushed (.onExit body (.fin point) false)]) := by
  exact exit_push b.program SourceUse.atomicFirst interp f body _ false

/-- The actual Workers registration spends its push without copying active-body opportunities. -/
theorem worker_push_debit (total : Nat)
    (interp : PrimInterp EffName EffThunk Val Err Defect FiberId Ann)
    (f : FrameFiber EffName EffThunk Val Err Defect FiberId Ann)
    (env : List Val) (fuel : Nat) (context : Ctx) (scope : Nat) (acquired : Val) :
    let point : Point := {path := Programs.crewAcquire 1, env, fuel, tape := []}
    let captured := point.capture acquired context
    let body : NCode := .sync (.op (.scopeAdd scope (.foreign captured)))
    let callback : EffName := .afterScopeAdd acquired (.foreign captured)
    frame (Programs.workersProgram total) (Programs.crewAcquire 1)
      {f with current := body, stack := .onSuccess body callback :: f.stack} + 1 =
      frame (Programs.workersProgram total) (Programs.crewAcquire 1)
        {f with current := .onSuccess body callback} ∧
    ({f with current := .onSuccess body callback}).step interp =
      (.running {f with current := body, stack := .onSuccess body callback :: f.stack},
        [.pushed (.onSuccess body callback)]) := by
  exact registration_push (Programs.workersProgram total) (Programs.crewAcquire 1) interp f scope acquired _

/-- Every Workers selected acquisition lies outside the repeated job-loop body. -/
theorem workers_loops_clear (total : Nat) : ∀ i ∈ [1, 2],
    ClearLoops (Programs.workersProgram total) (Programs.crewAcquire i) := by
  intro i member
  rcases List.mem_cons.mp member with rfl | tail
  · unfold ClearLoops
    kernel_rfl
  · have selected := List.mem_singleton.mp tail
    subst i
    unfold ClearLoops
    kernel_rfl

/-- All six actual Atomic request sites lie outside every repeated loop body. -/
theorem atomic_loops_census :
    (Atomic.Store.shopProgram.map fun root => Atomic.requests.all fun i =>
      (Node.addresses (.eff root)).all fun path =>
        (Node.at_ (.eff root) path).all fun node => match node with
          | .eff (.iterate _ _ _ _ _ _) => !(path ++ [0]).isPrefixOf (Atomic.SourcePaths.requestPath i)
          | _ => true) = some true := by
  kernel_rfl

/-- Successful admission discharges the full Atomic loop-body exclusion census. -/
theorem atomic_loops_clear (b : Api.Built) (built : Api.Author.build (Atomic.shop .none) = .ok b) :
    ∀ i ∈ Atomic.requests, ClearLoops b.program (Atomic.SourcePaths.requestPath i) := by
  have program : Atomic.Store.shopProgram = some b.program := by
    unfold Atomic.Store.shopProgram
    rw [(Api.Author.build_retains built).1]
    rfl
  have clear := atomic_loops_census
  rw [program] at clear
  exact List.all_eq_true.mp (Option.some.inj clear)

/-- An actual Workers history funds the value arm of every saved source frame.
The result retains both source acquisition indices and every job count and budget. -/
theorem workers_saved_value_debit (total compileFuel : Nat) (b : Api.Built)
    (built : Api.Author.build (Workers.crew total) = .ok b) (m : NativeMachine)
    (history : Effect4.Run.HistoryOf b compileFuel m) (id : FiberId)
    (fiber : Effect4.Program.SourceScope.SourceFiber) (found : m.fiber? id = some fiber)
    (i : Nat) (member : i ∈ [1, 2]) (code : NCode) (savedCode : code ∈ fiber.frame.stack)
    (value : Val) (provided : Option ExitV) (next : NCode) (pushed : List NCode)
    (arm : code.armA (interpAt b.program m.completedExits b.table).toPrimInterp value provided = some (next, pushed)) :
    current b.program (Programs.crewAcquire i) next +
      (pushed.map (saved b.program (Programs.crewAcquire i))).sum ≤
      saved b.program (Programs.crewAcquire i) code := by
  have source := SourceFragment.workers_admitted_history_at total compileFuel b built m history
  have owned := (Effect4.Program.SourceScope.configuration_fiber b.program m id fiber source found).frame.2 code savedCode
  have clearFin : ClearFinalizers b.program (Programs.crewAcquire i) := by
    rw [Programs.workers_built_program total b built]
    exact workers_clear total i member
  have clearLoop : ClearLoops b.program (Programs.crewAcquire i) := by
    rw [Programs.workers_built_program total b built]
    exact workers_loops_clear total i member
  exact armA_le b.program _ clearFin clearLoop m.completedExits b.table code value provided next pushed owned arm

/-- An actual Atomic history funds every saved value frame at all six request sites. -/
theorem atomic_saved_value_debit (compileFuel : Nat) (b : Api.Built)
    (built : Api.Author.build (Atomic.shop .none) = .ok b) (m : NativeMachine)
    (history : Effect4.Run.HistoryOf b compileFuel m) (id : FiberId)
    (fiber : Effect4.Program.SourceScope.SourceFiber) (found : m.fiber? id = some fiber)
    (i : Nat) (member : i ∈ Atomic.requests) (code : NCode) (savedCode : code ∈ fiber.frame.stack)
    (value : Val) (provided : Option ExitV) (next : NCode) (pushed : List NCode)
    (arm : code.armA (interpAt b.program m.completedExits b.table).toPrimInterp value provided = some (next, pushed)) :
    current b.program (Atomic.SourcePaths.requestPath i) next +
      (pushed.map (saved b.program (Atomic.SourcePaths.requestPath i))).sum ≤
      saved b.program (Atomic.SourcePaths.requestPath i) code := by
  have source := Effect4.Program.SourceScope.admitted_history_at b
    (SourceFragment.atomic_built_fragment b built) compileFuel m history
  have owned := (Effect4.Program.SourceScope.configuration_fiber b.program m id fiber source found).frame.2 code savedCode
  exact armA_le b.program _ (atomic_all_clear b built i member) (atomic_loops_clear b built i member)
    m.completedExits b.table code value provided next pushed owned arm

/-- Every real Workers value resume consumes only its actual saved source reservations. -/
theorem workers_resume_value_debit (total compileFuel : Nat) (b : Api.Built)
    (built : Api.Author.build (Workers.crew total) = .ok b) (m : NativeMachine)
    (history : Effect4.Run.HistoryOf b compileFuel m) (id : FiberId)
    (fiber : Effect4.Program.SourceScope.SourceFiber) (found : m.fiber? id = some fiber)
    (i : Nat) (member : i ∈ [1, 2]) (value : Val) (provided : Option ExitV) :
    returned b.program (Programs.crewAcquire i)
      ((fiber.frame.resumeValue (interpAt b.program m.completedExits b.table).toPrimInterp value provided).1) ≤
      (fiber.frame.stack.map (saved b.program (Programs.crewAcquire i))).sum := by
  have source := SourceFragment.workers_admitted_history_at total compileFuel b built m history
  have owned := (Effect4.Program.SourceScope.configuration_fiber b.program m id fiber source found).frame
  have clearFin : ClearFinalizers b.program (Programs.crewAcquire i) := by
    rw [Programs.workers_built_program total b built]
    exact workers_clear total i member
  have clearLoop : ClearLoops b.program (Programs.crewAcquire i) := by
    rw [Programs.workers_built_program total b built]
    exact workers_loops_clear total i member
  exact resumeValue_le b.program _ clearFin clearLoop m.completedExits b.table fiber.frame value provided owned

/-- Every real Atomic value resume consumes only its actual saved source reservations. -/
theorem atomic_resume_value_debit (compileFuel : Nat) (b : Api.Built)
    (built : Api.Author.build (Atomic.shop .none) = .ok b) (m : NativeMachine)
    (history : Effect4.Run.HistoryOf b compileFuel m) (id : FiberId)
    (fiber : Effect4.Program.SourceScope.SourceFiber) (found : m.fiber? id = some fiber)
    (i : Nat) (member : i ∈ Atomic.requests) (value : Val) (provided : Option ExitV) :
    returned b.program (Atomic.SourcePaths.requestPath i)
      ((fiber.frame.resumeValue (interpAt b.program m.completedExits b.table).toPrimInterp value provided).1) ≤
      (fiber.frame.stack.map (saved b.program (Atomic.SourcePaths.requestPath i))).sum := by
  have source := Effect4.Program.SourceScope.admitted_history_at b
    (SourceFragment.atomic_built_fragment b built) compileFuel m history
  have owned := (Effect4.Program.SourceScope.configuration_fiber b.program m id fiber source found).frame
  exact resumeValue_le b.program _ (atomic_all_clear b built i member) (atomic_loops_clear b built i member)
    m.completedExits b.table fiber.frame value provided owned

end Test.Dogfood.Scenario.SourceOpportunity
