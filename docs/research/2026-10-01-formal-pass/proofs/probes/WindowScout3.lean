import Effect4.Laws.Program.Typed.Assembly

/-! Scouting only (no claims): which decision does the fuel-6 cut land in, and what residue
does it drop? -/
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Sched Effect4.Program.Typed

def n (i : Nat) : Term := .lit (.nat i)
def yes : Term := .lit (.bool true)
def sleepy : NativeEff := .perform .sleep (.lit (.nat 1))
def escapeTimed : NativeEff :=
  .catchIf yes (.uninterruptible (.bind sleepy (.bind (.succeed (n 0)) (.fail (n 42))))) (.succeed (n 0))
def interruptRoot : Api.Decision :=
  .interruptFrom (some Api.root) ReasonAnnotations.empty Api.root
def tape : List Api.Decision :=
  [Api.evaluate, Api.flush, interruptRoot, .advance (ClockMillis.ofNat 100000), Api.flush]

def outcomeName : RReplay → String
  | .finished _ => "finished"
  | .frontier .fuel _ => "frontier fuel"
  | .frontier .tape _ => "frontier tape"
  | .stuck _ _ => "stuck"

def cmdName : RCmd → String
  | .evaluate _ => "evaluate" | .loop _ _ => "loop" | .deliver _ _ => "deliver"
  | .finish _ ex => s!"finish {match ex with | .success _ => "ok" | .failure c => s!"fail fail?={c.reasons.any (fun r => r.tag == ReasonTag.fail)}"}"
  | .resume _ t _ => s!"resume {t}" | .launch _ => "launch" | .enrollRace _ _ => "enrollRace"
  | .registrationDone _ _ => "registrationDone" | .interruptTarget _ _ _ => "interruptTarget"
  | .afterInterrupt _ _ _ => "afterInterrupt" | .raceCancel _ _ _ _ _ => "raceCancel"
  | .trackChild _ _ => "trackChild" | .observe _ _ _ => "observe" | .exitDone _ => "exitDone"
  | .closeParAwait _ _ _ => "closeParAwait" | .link _ _ _ _ _ => "link" | .drainDue => "drainDue"
  | .wake _ _ => "wake"

-- The receipts of each prefix at fuel 6.
#eval (List.range 6).map fun k => (k, outcomeName (replayR escapeTimed 6 (tape.take k)))

def before : RState := (replayR escapeTimed 6 (tape.take 3)).machine
#eval before.armed
#eval (before.fiber? Api.root).map fun f => (f.parked == .notParked, f.dispatcher.buckets.length)
-- The advance's first clock step and its drain, at fuel 6.
#eval
  letI := termEvaluatorFor escapeTimed
  match (interpR escapeTimed).clockStep (ClockMillis.ofNat 100000) before.state with
  | (none, _) => ["no owed"]
  | (some owed, st) =>
    let r := drainOwed { before with state := st } [owed]
    let d := driveState (interpR escapeTimed) 6 r.1 (r.2 ++ [Cmd.drainDue])
    [s!"mode now? {match owed.mode with | .now => true | _ => false}",
     s!"after drain cmds={(r.2 ++ [Cmd.drainDue]).map cmdName}",
     s!"residue={d.2.map cmdName} armed={d.1.armed.length}"]
