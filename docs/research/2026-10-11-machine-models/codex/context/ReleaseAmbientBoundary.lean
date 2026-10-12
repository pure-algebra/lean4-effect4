import Effect4.Laws.Program.Typed.Denotation
import Effect4.Laws.Auto.KernelRfl
import Effect4.Program.Admission
import Effect4.Laws.Program.EvaluateR
/-!
Concept: residual-program-typing, R4 and R9; helper of typed-state-reachable.
The reader consumes the actual captured release source and its restoring region.
It retains service-table agreement and strong previous-map membership.
The controls distinguish captured-map coverage from previous-map coverage and release mask roles.
It establishes neither closed native reachability nor an outside-runtime observation.
-/
set_option autoImplicit false
namespace Test.ReleaseAmbientBoundary
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Typed Effect4.Program.Sched Effect4.Program.Denote

def key : ServiceKey := ⟨⟨4⟩, ⟨4⟩⟩
def source : ProgramSource := { program := .«scoped» (.provideService key (.lit (.nat 1)) (.acquireRelease (.succeed (.lit .unit)) (.service key))) }
def point : Point := { path := [0, 0], env := [], fuel := 8, tape := [] }
def previous : Ctx := Ctx.withServices
  ((Env.Context.empty : Env.Ctx).addV Env.scopeKey (Val.scopeHandle 0))
def captured : Ctx := { previous with services := previous.services.addV key (.nat 1) }
def releasePoint : Point :=
  (Point.ofCapture (point.capture .unit captured)).childWith 1 (reifyExitVal (.success .unit))
def releaseType : EffTy := ⟨.nat, .never, Env.Requirement.single key⟩

#guard (admitProgram source.program).toOption.isSome
#guard ((typeOfProgram source.signature source.program).map EffTy.requires) = some Row.empty
#guard Node.at_ (.eff source.program) point.path =
  some (.eff (.acquireRelease (.succeed (.lit .unit)) (.service key)))
#guard Node.at_ (.eff source.program) releasePoint.path = some (.eff (.service key))
#guard Checker.check (source.scopeSig releasePoint.path)
  [.unit, .exitOf .unknown .unknown] releasePoint.path (.service key) = .ok releaseType

example : contAOf source.program
    (.releaseBody (Point.ofCapture (point.capture .unit captured)) (.success .unit) previous) .unit =
    Prim.withFiber (.releaseMasked releasePoint previous) := by rfl

-- The earlier internal premise demands this false inclusion from the previous map.
example : ¬ previous.services.Satisfies captured.services.keysRow := by
  intro prior
  have present : key ∈ captured.services.keysRow := by decide
  have absent : (previous.services.get? key).isSome = false := by kernel_rfl
  have required := prior key present
  rw [absent] at required
  exact Bool.noConfusion required

-- Actual mask completion selects the restored map for either delivered exit.
example (exit : ExitV) :
    ambientFiberInput captured.services.keysRow (.mask false (.release releasePoint previous)) exit =
      previous.services.keysRow := by rfl

-- The admitted cleanup uses the capture's row; the previous map has no installed-row demand.
example (world : Typed.World)
    (body : BodyTyped source world (.release releasePoint previous) releaseType)
    (arguments : AmbientStackTyped source world captured.services.keysRow
      (scopeParams source.program releasePoint.path) releasePoint.params) :
    ambientFiberPre source world captured.services.keysRow
      (.mask false (.release releasePoint previous)) releaseType := by
  refine ⟨body, ?_, (fun _ _ impossible => by cases impossible), ?_, ?_⟩
  · exact (Provision.satisfies_iff_subset_keysRow _ _).mp (by
      intro service present
      have identity : service = key := (Row.mem_singleton key service).mp present
      subst service
      kernel_rfl)
  · intro flag point previous identity
    cases identity
    rfl
  · refine ⟨(fun _ impossible => by cases impossible),
      (fun _ _ _ impossible => by cases impossible), ?_⟩
    intro point role
    rcases role with impossible | ⟨ctx, impossible | identity⟩
    · cases impossible
    · cases impossible
    · cases identity
      exact arguments

-- The real cleanup source and restoring region compose without a previous-map service promise.
example (world : Typed.World) (services : world.serviceTy = source.sig.serviceTy)
    (previousMembers : ServicesFit world previous.services) :
    AmbientProg source world captured.services.keysRow
      (releaseType, previous.services.keysRow, (Row.empty : Env.Requirement))
      (bodyR (interpRAt source.program []) (.release releasePoint previous)) := by
  have node : Node.at_ (.eff source.program) releasePoint.path = some (.eff (.service key)) := by
    kernel_rfl
  have pointTyped : PointTyped source world releasePoint releaseType := by
    refine ⟨.service key, [.unit, .exitOf .unknown .unknown], ?_, ?_, ?_, ?_, ?_⟩
    · kernel_rfl
    · kernel_rfl
    · change EnvTyped world [.unit, .exitOf .unknown .unknown]
        [.unit, reifyExitVal (.success .unit)]
      exact envTyped_append (ty := .exitOf .unknown .unknown)
        (envTyped_append (ty := .unit) (v := .unit) (envTyped_nil world) True.intro)
        (v := reifyExitVal (.success .unit)) (by
          change Fits world Val.unit Ty.unknown
          intro handle absent
          cases absent)
    · intro entry absent
      exact nomatch absent
    · change StackTyped source world [] []
      exact stackTyped_nil source world []
  have budget : releasePoint.fuel ≠ 0 := by decide
  have cleanup : AmbientProg source world captured.services.keysRow
      (releaseType, captured.services.keysRow, captured.services.keysRow)
      (denoteAt source.program releasePoint) := by
    rw [show denoteAt source.program releasePoint = denoteR source.program (.service key) releasePoint from by
      simp only [denoteAt, node]]
    exact service_arm budget services node pointTyped
  exact ambient_onExit_restore_guarantees source previous previousMembers (fun key absent => False.elim (Row.not_mem_empty key absent))
    (fun key absent => False.elim (Row.not_mem_empty key absent)) cleanup


-- Ordinary true masks remain available; only the unsupported release role is refused.
#guard (admitProgram (.interruptible (.succeed (.lit .unit)))).toOption.isSome
example : ReleaseMaskAllowed (.mask true (.at_ releasePoint)) := by
  intro flag point previous impossible
  cases impossible
example : ¬ ReleaseMaskAllowed (.mask true (.release releasePoint previous)) := by
  intro accepted
  exact Bool.noConfusion (accepted true releasePoint previous rfl)
example (exit : ExitV) :
    ambientFiberInput captured.services.keysRow (.mask true (.release releasePoint previous)) exit =
      captured.services.keysRow := by rfl
end Test.ReleaseAmbientBoundary
