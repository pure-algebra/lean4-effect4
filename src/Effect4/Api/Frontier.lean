import Effect4.Program.Admit

/-! Live frontier observations, separate from program syntax and the outcome.
Authority: foundation-wave2.contract.md, formal foundations amendment.
The host-key carrier lives here so replay and the host protocol share one alphabet.
-/
set_option autoImplicit false

namespace Effect4.Api.HostProtocol
open Effect4

structure Key where
  fiber : FiberId
  token : Nat
deriving DecidableEq, Repr

end Effect4.Api.HostProtocol

namespace Effect4.Api
open Effect4 Effect4.Machine Effect4.Program

inductive FrontierReason
  | commandFuel
  | compileFuel (fiber : FiberId)
  | awaitHost (key : HostProtocol.Key)
  | awaitTimer (fiber : FiberId) (wakeAt : ClockMillis)
  | awaitDecision
deriving DecidableEq, Repr

/-- The runnable condition already used by frontier inspection: the fiber has no exit and
is not parked. This does not assert that its next command will progress at a given budget. -/
@[simp] def isRunnable (f : RunFiber EffName EffThunk Val Err Defect FiberId Ann Ctx) : Bool :=
  f.exit.isNone && f.parked == .notParked

def hasRunnable (m : NativeMachine) : Bool := m.fibers.any isRunnable

/-- Runnable fibers in their existing machine order. Frontier inspection and work planning
read the same predicate. -/
def runnableFibers (m : NativeMachine) : List FiberId :=
  (m.fibers.filter isRunnable).map (·.id)

def hostReasons (m : NativeMachine) : List FrontierReason :=
  (Program.awaits m).map fun a => .awaitHost ⟨a.fiber, a.token⟩

def timerReasons (m : NativeMachine) : List FrontierReason :=
  m.state.timers.wake.waiters.map fun w => .awaitTimer w.fiber w.payload

def isCompileFrontier : NCode → Bool
  | .suspend (.body p) => p.fuel == 0
  | _ => false

def compileReasons (m : NativeMachine) : List FrontierReason :=
  m.fibers.filterMap fun f =>
    if isCompileFrontier f.frame.current then some (.compileFuel f.id) else none

def frontierReasons (why : Exhaustion) (m : NativeMachine) : List FrontierReason :=
  (match why with | .fuel => [.commandFuel] | .tape => []) ++
    compileReasons m ++ hostReasons m ++ timerReasons m ++
    (match why with
    | .fuel => []
    | .tape => if hasRunnable m then [.awaitDecision] else [])

end Effect4.Api
