import Effect4.Laws.Program.Typed.Assembly

/-! Scouting only (no claims): search for a command budget whose fuel cut lands between the
walk that finishes the root and its queued `finish`, for the host-free preempted-catch
program with `b` pure binds between the timer and the failure. -/
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Sched Effect4.Program.Typed

def n (i : Nat) : Term := .lit (.nat i)
def yes : Term := .lit (.bool true)
def sleepy : NativeEff := .perform .sleep (.lit (.nat 1))
def chain : Nat → NativeEff
  | 0 => .fail (n 42)
  | k + 1 => .bind (.succeed (n k)) (chain k)
def escapeTimed (b : Nat) : NativeEff :=
  .catchIf yes (.uninterruptible (.bind sleepy (chain b))) (.succeed (n 0))
def interruptRoot : Api.Decision :=
  .interruptFrom (some Api.root) ReasonAnnotations.empty Api.root
def tape : List Api.Decision :=
  [Api.evaluate, Api.flush, interruptRoot, .advance (ClockMillis.ofNat 100000), Api.flush]

def staleFail : RProgram → Bool
  | .pure (.failure c) => c.reasons.any (fun r => r.tag == .fail)
  | _ => false

def window (b fuel : Nat) : Bool :=
  let r := replayR (escapeTimed b) fuel tape
  match r.machine.fiber? Api.root with
  | none => false
  | some f => f.exit.isNone && f.frame.stack.isEmpty && staleFail f.frame.current

#eval (List.range 7).map fun b => (b, (Api.typeOf (escapeTimed b)).isSome,
  (List.range 40).filter (window b))
