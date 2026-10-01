import Effect4.Laws.Program.Typed.Assembly

/-! Scouting only (no claims): where does a fuel cut land in the finish window of the
host-free preempted-catch program (E4-SCHED-CE-008's escape, with a timer in place of the
deferred answer)? Prints the root fiber's shape at each command budget. -/
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Sched Effect4.Program.Typed

def n (i : Nat) : Term := .lit (.nat i)
def yes : Term := .lit (.bool true)
def sleepy : NativeEff := .perform .sleep (.lit (.nat 1))
def escapeTimed : NativeEff :=
  .catchIf yes (.uninterruptible (.bind sleepy (.fail (n 42)))) (.succeed (n 0))
def interruptRoot : Api.Decision :=
  .interruptFrom (some Api.root) ReasonAnnotations.empty Api.root
def tape : List Api.Decision :=
  [Api.evaluate, Api.flush, interruptRoot, .advance (ClockMillis.ofNat 100000), Api.flush]

def codeShape : RProgram → String
  | .pure (.success v) => s!"pure success {repr v}"
  | .pure (.failure c) => s!"pure failure {c.reasons.length} reasons, fail? {c.reasons.any (fun r => r.tag == .fail)}"
  | .vis (.inl _) _ => "vis store"
  | .vis (.inr _) _ => "vis fiber"

def outcomeName : RReplay → String
  | .finished _ => "finished"
  | .frontier .fuel _ => "frontier fuel"
  | .frontier .tape _ => "frontier tape"
  | .stuck _ _ => "stuck"

def exitShape : Option ExitV → String
  | none => "none"
  | some (.success v) => s!"ok {repr v}"
  | some (.failure c) => s!"fail {c.reasons.length} reasons, fail? {c.reasons.any (fun r => r.tag == .fail)}"

def rootShape (p : NativeEff) (t : List Api.Decision) (fuel : Nat) : String :=
  let r := replayR p fuel t
  match r.machine.fiber? Api.root with
  | none => s!"{fuel}: {outcomeName r} no root"
  | some f => s!"{fuel}: {outcomeName r} stack={f.frame.stack.length} exit={exitShape f.exit} running={f.running} current={codeShape f.frame.current}"

#eval (Api.typeOf escapeTimed).isSome
#eval (List.range 40).map (rootShape escapeTimed tape)
