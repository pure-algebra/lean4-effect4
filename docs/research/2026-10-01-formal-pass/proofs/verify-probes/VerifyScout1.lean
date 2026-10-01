import Effect4.Laws.Program.Typed.Assembly
import Effect4.Laws.Machine.Lift

/-! Verifier scouting (no claims): running flags in probe A's machines, and the shape of the
denoted root code of the typed corpus's `awaitFiber.value` entry. -/
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Sched Effect4.Program.Typed

namespace VerifyScout1
def n (i : Nat) : Term := .lit (.nat i)
def yes : Term := .lit (.bool true)
def sleepy : NativeEff := .perform .sleep (.lit (.nat 1))
def prog : NativeEff :=
  .catchIf yes (.uninterruptible (.bind sleepy (.bind (.succeed (n 0)) (.fail (n 42)))))
    (.succeed (n 0))
def interruptRoot : Api.Decision :=
  .interruptFrom (some Api.root) ReasonAnnotations.empty Api.root
def tape : List Api.Decision :=
  [Api.evaluate, Api.flush, interruptRoot, .advance (ClockMillis.ofNat 1), Api.flush]

def flags (m : RState) : List (Nat × Bool × Bool × Bool) :=
  m.fibers.map fun f => (f.id.value, f.running, f.exit.isSome, f.parked == .notParked)

def kind : ReplayResult EffName EffThunk Val Err Defect FiberId Ann Ctx Stores RProgram RSaved Unit → String
  | .finished _ => "finished" | .frontier .fuel _ => "frontier-fuel"
  | .frontier .tape _ => "frontier-tape" | .stuck _ _ => "stuck"

#eval (List.range 13).map fun k => (k, (List.range 6).map fun j =>
  let r := replayR prog k (tape.take j)
  (j, kind r, flags r.machine))

-- the corpus entry
def v (i : Nat) : Term := .var i
def opts : Supervision.ForkOptions := ⟨true, false, .inherit⟩
def forked : NativeEff := .withFiber (.fork (.succeed (n 1)) opts)
def awaitProg : NativeEff := .bind forked (.awaitFiber (v 0) .awaitValue)
#eval (Api.typeOf awaitProg).isSome
def opName : RProgram → String
  | .pure _ => "pure"
  | .vis (.inl _) _ => "store"
  | .vis (.inr op) _ => match op with
    | .fork _ _ _ => "fork" | .await _ _ => "await" | .guard_ _ => "guard" | _ => "fiber-other"
#eval opName (denoteR awaitProg awaitProg (rootPoint 5))
end VerifyScout1
