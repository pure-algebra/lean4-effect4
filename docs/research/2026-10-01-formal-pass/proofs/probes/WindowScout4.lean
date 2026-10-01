import Effect4.Laws.Program.Typed.Assembly

/-! Scouting only (no claims): the command sequence of the cut decision in probe A. -/
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Sched Effect4.Program.Typed

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
def before : RState := (replayR prog 6 (tape.take 3)).machine

def cmdName : RCmd → String
  | .evaluate _ => "evaluate" | .loop _ _ => "loop" | .deliver _ _ => "deliver"
  | .finish _ _ => "finish" | .resume _ t _ => s!"resume {t}" | .drainDue => "drainDue"
  | .observe _ _ _ => "observe" | .exitDone _ => "exitDone" | _ => "other"

def trace : Nat → RState → List RCmd → List String
  | 0, _, cmds => [s!"stop residue={cmds.map cmdName}"]
  | _ + 1, _, [] => ["empty"]
  | k + 1, m, c :: rest =>
    letI := termEvaluatorFor prog
    let r := driveStep (interpR prog) m c rest
    cmdName c :: trace k r.1 r.2

#eval
  match (interpR prog).clockStep (ClockMillis.ofNat 1) before.state with
  | (none, _) => ["no owed"]
  | (some owed, st) =>
    let r := drainOwed { before with state := st } [owed]
    trace 6 r.1 (r.2 ++ [Cmd.drainDue])
