import Test.Dogfood.Scenario.NativeHeap
import Effect4.Laws.Auto.KernelRfl

/-!
# Actual source-use boundary probes

Concept: scope-lifetime-finalization R11, serving the existing placement and registration goals.
These source and callback equations identify where an unspent registration opportunity moves.
They add no machine invariant and no program representation.
The actual Atomic path is its first request's existing finalizer path.
The actual Workers path is its first acquisition, for every job count.
-/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
namespace Test.Dogfood.Scenario.SourceUse
open Effect4 Effect4.Machine Effect4.Program Effect4.Laws.Auto

abbrev atomicFirst : List Nat := [1, 1, 1, 1, 0, 0, 0]

/-- The actual Atomic point compiles to a frame carrying its finalizer address. -/
theorem atomic_header (env : List Val) (fuel : Nat) :
    (Atomic.Store.shopProgram.map fun root =>
      match resolve root {path := atomicFirst, env, fuel := fuel + 1, tape := []} with
      | .onExit _ (.fin saved) _ => saved.path == atomicFirst
      | _ => false) = some true := by
  kernel_rfl

/-- The actual Workers acquisition compiles to its context callback at every job count. -/
theorem worker_header (total : Nat) (env : List Val) (fuel : Nat) :
    (match resolve (Programs.workersProgram total)
      {path := Programs.crewAcquire 1, env, fuel := fuel + 1, tape := []} with
    | .onSuccess _ (.acquireCtx saved) => saved.path == Programs.crewAcquire 1
    | _ => false) = true := by
  kernel_rfl

/-- An actual Atomic finalizer pushes itself once and transfers execution to its body. -/
theorem atomic_push (interp : PrimInterp EffName EffThunk Val Err Defect FiberId Ann)
    (frame : FrameFiber EffName EffThunk Val Err Defect FiberId Ann)
    (env : List Val) (fuel : Nat) (body : NCode) :
    let point : Point := {path := atomicFirst, env, fuel, tape := []}
    ({frame with current := .onExit body (.fin point) false}).step interp =
      (.running {frame with current := body, stack := .onExit body (.fin point) false :: frame.stack},
        [.pushed (.onExit body (.fin point) false)]) := by
  exact FrameFiber.step_onExit interp frame body (.fin _) false

/-- An actual acquisition retains its callback while it runs the acquired source child. -/
theorem worker_acquire (total : Nat) (env : List Val) (fuel : Nat) (context : Ctx) (scope : Nat) :
    let point : Point := {path := Programs.crewAcquire 1, env, fuel, tape := []}
    contAOf (Programs.workersProgram total) (.acquireIn point context) (.scopeHandle scope) =
      .onSuccess (resolve (Programs.workersProgram total) (point.child 0))
        (.acquired point context scope) := rfl

/-- The acquired callback emits the single scope registration and a distinct response callback. -/
theorem worker_registration (total : Nat) (env : List Val) (fuel : Nat)
    (context : Ctx) (scope : Nat) (acquired : Val) :
    let point : Point := {path := Programs.crewAcquire 1, env, fuel, tape := []}
    let finalizer := FinName.foreign (point.capture acquired context)
    contAOf (Programs.workersProgram total) (.acquired point context scope) acquired =
      .onSuccess (.sync (.op (.scopeAdd scope finalizer))) (.afterScopeAdd acquired finalizer) := rfl

/-- A successful registration response cannot create a second registration. -/
theorem worker_registered (total : Nat) (env : List Val) (fuel : Nat)
    (context : Ctx) (acquired : Val) :
    let point : Point := {path := Programs.crewAcquire 1, env, fuel, tape := []}
    contAOf (Programs.workersProgram total)
      (.afterScopeAdd acquired (.foreign (point.capture acquired context))) .unit =
        .success acquired := rfl

/-- Source ownership alone allows two copies of the same actual Atomic residual.
This control supplies no reachability assertion and therefore refutes no history theorem. -/
theorem atomic_duplicate_stack (b : Api.Built)
    (built : Api.Author.build (Atomic.shop .none) = .ok b) (env : List Val) (fuel : Nat)
    (scopeAt : SourceScope.At b.program {path := atomicFirst, env, fuel, tape := []}) :
    SourceScope.StackAt b.program
      [resolve b.program {path := atomicFirst, env, fuel, tape := []},
       resolve b.program {path := atomicFirst, env, fuel, tape := []}] := by
  have owned := SourceScope.resolve_scoped b.program (SourceFragment.atomic_built_fragment b built)
    {path := atomicFirst, env, fuel, tape := []} scopeAt
  intro code member
  rcases List.mem_cons.mp member with rfl | rest
  · exact owned
  · rw [List.mem_singleton] at rest
    cases rest
    exact owned

/-- The actual acquisition's response callback cannot be attached to a success producer.
This control records why matching producer identity is part of the source invariant. -/
theorem worker_unmatched_response (total : Nat) (env : List Val) (fuel : Nat)
    (context : Ctx) (acquired : Val) :
    let point : Point := {path := Programs.crewAcquire 1, env, fuel, tape := []}
    ¬ SourceScope.CodeAt (Programs.workersProgram total)
      (.onSuccess (.success .unit) (.afterScopeAdd acquired (.foreign (point.capture acquired context)))) := by
  dsimp only
  intro owned
  obtain ⟨scope, impossible⟩ := SourceScope.registration_body _ _ _ _ owned
  cases impossible

end Test.Dogfood.Scenario.SourceUse
