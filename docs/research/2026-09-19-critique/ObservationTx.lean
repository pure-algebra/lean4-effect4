import Effect4.Run
import Effect4.Laws.Machine.Behaviour

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 800000

namespace CritiqueObservationTx
open Effect4 Effect4.Machine Effect4.Program

def p : NativeEff := .succeed (.lit (.nat 42))
def initial : Api.Machine := Api.load p 400

def short := stepDecisionState (interpOf p) 1 initial Api.evaluate

def restarted := stepDecisionState (interpOf p) 400 short.1 Api.evaluate

-- Existing machine probe: enough later fuel on a new evaluate is not refueling
-- the lost command residue of an earlier evaluate.
#guard short.2 = false
#guard (short.1.fiber? Api.root).map RunFiber.running = some true
#guard restarted.2 = true
#guard (restarted.1.fiber? Api.root).bind RunFiber.exit = none
#guard (stepDecisionState (interpOf p) 400 initial Api.evaluate).2 = true
#guard ((stepDecisionState (interpOf p) 400 initial Api.evaluate).1.fiber? Api.root).bind
  RunFiber.exit = some (.success (.nat 42))

-- In contrast, continuing the explicit command residue does finish.
def cmdResidue := driveState (interpOf p) 1 initial [Cmd.evaluate Api.root, Cmd.drainDue]
def resumed := driveState (interpOf p) 400 cmdResidue.1 cmdResidue.2
#guard cmdResidue.2.length = 2
#guard resumed.2 = []
#guard (resumed.1.fiber? Api.root).bind RunFiber.exit = some (.success (.nat 42))

-- Existing machine probe: a different decision is still applied at the frontier.
def interrupted := stepDecisionState (interpOf p) 0 short.1
  (.interruptFrom none ReasonAnnotations.empty Api.root)
#guard interrupted.1.trace.length > short.1.trace.length

-- Direct projection countermodel, not a claim that both states are reachable
-- under one program: deleting the fork history changes supervision despite
-- equality of the frozen machine observation.
def bornAsChild : Api.Machine :=
  { initial with trace := [.forked ⟨7⟩ Api.root true] }
#guard obs initial = obs bornAsChild
#guard Api.fiberStatuses initial = [(Api.root, .root)]
#guard Api.fiberStatuses bornAsChild = [(Api.root, .daemon)]

-- Finite observations do not by themselves imply convergence or non-divergence.
-- This is an abstract countermodel of an insufficient local simulation premise.
inductive SpecStep : Unit → Unit → Prop
inductive ImplStep : Unit → Unit → Prop
  | spin : ImplStep () ()
def Related (_ _ : Unit) : Prop := True
example : ∀ s t, Related s t → ImplStep t t → Related s t :=
  fun _ _ _ _ => True.intro
example : ¬ ∃ s', SpecStep () s' := by
  rintro ⟨_, h⟩
  cases h

end CritiqueObservationTx
