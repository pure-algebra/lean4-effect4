import Effect4.Machine.Approximation
import Effects.Algebra.Program

/-!
# The shared scheduler at an algebra instance

D1: these finite runs use the actual `Effects.Program` carrier, whose
continuations have no decidable equality. The fixture has one operation: read
and increment a natural-number store. It exercises the production command loop,
resume guard, yield dispatcher and interrupt path. It is not `evaluateR` and
does not claim a relation to compiled Eff or the host (`CORE-FB-SIMULATION`).
-/

set_option autoImplicit false

namespace Test.Runtime.SchedulerCoreContract

open Effect4 Effect4.Machine

abbrev Sig : Effects.Signature.{0, 0} := ⟨Unit, fun _ => Nat⟩
abbrev X := Exit Nat Unit Unit FiberId Unit
abbrev Code := Effects.Program Sig X

structure Saved where
  current : Code
  interruptible : Bool
  interruptedCause : Option (Cause Unit Unit FiberId Unit)
  deferredInterrupt : Bool
  finalizers : List Unit

instance algebraCore : FiberCore Unit Nat Unit Unit FiberId Unit Code Saved where
  current := Saved.current
  answerWith := fun f code => { f with current := code }
  start := fun code flag => ⟨code, flag, none, false, []⟩
  interruptible := Saved.interruptible
  interruptedCause := Saved.interruptedCause
  deferredInterrupt := Saved.deferredInterrupt
  recordCause := fun f cause => { f with interruptedCause := some cause }
  setDeferred := fun f flag => { f with deferredInterrupt := flag }
  pendingFailure := fun f =>
    { f with
      current := .pure (.failure (f.interruptedCause.getD Cause.empty))
      deferredInterrupt := false }
  pushAsyncFinalizer := fun name f => { f with finalizers := name :: f.finalizers }
  clearStack := fun f => { f with finalizers := [] }
  success := fun value => .pure (.success value)
  failure := fun cause => .pure (.failure cause)
  onSuccess := fun code _ => code

abbrev M := RunMachine Unit Unit Nat Unit Unit FiberId Unit Unit Nat Code Saved Unit
abbrev F := RunFiber Unit Unit Nat Unit Unit FiberId Unit Unit Code Saved
abbrev I := RunInterp Unit Unit Nat Unit Unit FiberId Unit Unit Nat Code
abbrev D := RunDecision Unit Unit Nat Unit Unit FiberId Unit
abbrev C := Cmd Unit Unit Nat Unit Unit FiberId Unit Code

def readNext : Code := .vis () (fun n => .pure (.success n))

def interp : I where
  contA := fun _ v => .pure (.success v)
  contE := fun _ c => .pure (.failure c)
  syncValue := fun _ => 0
  suspendBody := fun _ => readNext
  iterNext := fun _ v => ([], .done v)
  loopTest := fun _ _ => false
  loopBody := fun _ v => .pure (.success v)
  loopStep := fun _ _ v => v
  loopDone := fun _ => 0
  finalizerExit := fun _ _ => Exit.void
  reifyExit := fun _ => 0
  cancelThenFail := fun _ c => .pure (.failure c)
  notImplemented := ()
  parkOf := fun _ => none
  withFiberOf := fun _ => none
  syncState := fun _ _ => none
  registerAsync := fun _ _ _ s => (s, none)
  answerCode := fun
    | .ofExit exit => .pure exit
    | .ofRefGet _ => readNext
  dueResumes := fun s => ([], s)
  cancelName := fun _ _ _ => ()
  abortName := ()
  parkCancelName := ()
  raceCancelName := fun _ => ()
  raceSettle := fun _ exit => .pure exit
  finalizerProgram := fun _ _ => none
  restoreName := fun _ => ()
  mergeName := fun _ => ()
  scopeStatus := fun _ _ => none
  scopeLinkFiber := fun _ _ _ _ _ => none
  dropFinalizer := fun _ _ _ => none
  closeScope := fun _ _ _ _ _ => none
  ambientScope := fun _ => none
  budgetOf := fun _ => (2048, false)
  emptyContext := ()
  contextValue := fun _ => 0
  exitValue := fun exit _ => .pure exit
  fiberValue := FiberId.value
  fibersValue := List.length
  exitsValue := List.length
  voidValue := 0
  encodeFiber := id
  stackAnnotations := fun _ => ReasonAnnotations.empty
  asyncFiberError := ()
  missingScope := ()

instance algebraEvaluator : FiberEvaluator Unit Unit Nat Unit Unit FiberId Unit Unit Nat
    Code Saved Unit where
  evaluate := fun _ m f yielding =>
    match f.frame.current with
    | .pure exit => ⟨m, f, yielding, .finished exit, []⟩
    | .vis _ next =>
      ⟨{ m with state := m.state + 1 }, { f with frame := { f.frame with current := next m.state } },
        yielding, .continue_, []⟩

def initial : M :=
  { (RunMachine.empty 7 : M) with
    fibers := [RunFiber.make ⟨0⟩ readNext true (2048, false) ()], nextId := 1 }

def exitOf (m : M) : Option X := (m.fiber? ⟨0⟩).bind RunFiber.exit
def cmds : List C := [.evaluate ⟨0⟩, .drainDue]
def tape : List D := [.evaluate ⟨0⟩, .flush]

#guard !(settled (driveState interp 0 initial cmds))
#guard (driveState interp 2 initial cmds).1.state = 8
#guard !(settled (driveState interp 2 initial cmds))
#guard exitOf (driveState interp 20 initial cmds).1 = some (.success 7)
#guard settled (driveState interp 20 initial cmds)
#guard Suffices interp 20 tape initial
#guard (replayEval interp 1 tape initial).terminal = false
#guard (replayEval interp 20 tape initial).terminal

-- The existing splitting and tape-stability laws apply to this code carrier.
theorem splitFuel (a b : Nat) :
    driveState interp (a + b) initial cmds =
      driveState interp b (driveState interp a initial cmds).1 (driveState interp a initial cmds).2 :=
  driveState_add interp a b initial cmds

theorem stableTape (k : Nat) :
    replayEval interp (20 + k) tape initial = replayEval interp 20 tape initial :=
  replay_stable interp 20 tape initial (by decide) k

-- The scheduler injects a yield, saves algebra code on a task, then resumes it.
def yielding : M := initial.modify ⟨0⟩ fun f => { f with yieldOverride := some true }
#guard exitOf (replayEval interp 20 tape yielding).machine = some (.success 7)
#guard (replayEval interp 20 tape yielding).machine.armed.isEmpty

-- External Completion data and the existing guard are used without a tape translation.
def parked : M := initial.modify ⟨0⟩ fun f => { f with parked := .withGuard 3 }
def answer (token : Nat) : D := .answerAsync ⟨0⟩ token (.ofExit (.success 42))
#guard exitOf (replayEval interp 20 [answer 3] parked).machine = some (.success 42)
#guard exitOf (replayEval interp 20 [answer 4] parked).machine = none
#guard exitOf (replayEval interp 20 [answer 3, answer 3] parked).machine = some (.success 42)

-- The shared interrupt path builds failure code through the chosen core.
#guard exitOf (replayEval interp 20 [.interruptFrom (some ⟨1⟩) ReasonAnnotations.empty ⟨0⟩] initial).machine =
  some (.failure (Cause.interrupt (some ⟨1⟩)))

-- CORE-FB-TRACE: an unconstrained evaluator can erase already recorded events.
@[instance_reducible] def erasesTrace : FiberEvaluator Unit Unit Nat Unit Unit FiberId Unit Unit Nat Code Saved Unit where
  evaluate := fun i m f y =>
    let it := algebraEvaluator.evaluate i m f y
    { it with machine := { it.machine with trace := [] } }

#guard (drive (evaluator := erasesTrace) interp 1 initial cmds).trace.length = 1
#guard (drive (evaluator := erasesTrace) interp 2 initial cmds).trace.length = 0

end Test.Runtime.SchedulerCoreContract
