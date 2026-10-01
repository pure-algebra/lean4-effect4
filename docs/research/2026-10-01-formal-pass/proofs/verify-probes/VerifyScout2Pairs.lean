import Test.Program.TypedCorpus
import Effect4.Laws.Program.Typed.Assembly

/-! Verifier scouting (tested, no theorem): (1) the typed corpus interleaving pairs (`pairPrograms`) on the reference machine at
small and large command budgets: whether any fiber is `running` at a settled result
(`finished` or a consumed tape), and how often an exited fiber's code slot is not its exit;
(2) the store rows seat PROOFS did not scout; (3) the denoted root of `awaitFiber.value`. -/
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Sched Effect4.Program.Typed
open Test.Program.TypedCorpus

namespace VerifyScout2Pairs

abbrev RR := ReplayResult EffName EffThunk Val Err Defect FiberId Ann Ctx Stores RProgram RSaved Unit

def interruptRoot : Api.Decision := .interruptFrom none ReasonAnnotations.empty Api.root
def advanceAll : Api.Decision := .advance (ClockMillis.ofNat 100000)
def tapes : List (List Api.Decision) := [
  [Api.evaluate, Api.flush],
  [Api.evaluate, Api.flush, advanceAll, Api.flush],
  [Api.evaluate, interruptRoot, Api.flush, advanceAll, Api.flush],
  [Api.evaluate, Api.flush, .advance (ClockMillis.ofNat 1), interruptRoot, Api.flush, advanceAll, Api.flush]]

def settledKind : RR → Bool
  | .finished _ => true | .frontier .tape _ => true | _ => false
def isFinished : RR → Bool
  | .finished _ => true | _ => false
def isFuel : RR → Bool
  | .frontier .fuel _ => true | _ => false

def anyRunning (m : RState) : Bool := m.fibers.any (·.running)

/-- An exited fiber whose code slot is not `pure` of its recorded exit. -/
def staleExited (m : RState) : Nat :=
  (m.fibers.filter fun f => match f.exit, f.frame.current with
    | some ex, .pure ex' => !(decide (ex = ex'))
    | some _, .vis _ _ => true
    | none, _ => false).length

def budgets : List Nat := [3, 6, 9, 14, 25, 4000]

structure Tally where
  runs : Nat := 0
  settled : Nat := 0
  settledRunning : Nat := 0
  fuelRunning : Nat := 0
  fuelRuns : Nat := 0
  finished : Nat := 0
  finishedStale : Nat := 0
  examples : List String := []
deriving Repr

def noteEx (t : Tally) (msg : String) : Tally := { t with examples := msg :: t.examples.take 4 }

def tally : Tally := Id.run do
  let mut t : Tally := {}
  for e in pairPrograms do
    if e.table.isEmpty then
      for tape in tapes do
        for k in budgets do
          let r := replayR e.program k tape
          let m := r.machine
          t := { t with runs := t.runs + 1 }
          if settledKind r then
            t := { t with settled := t.settled + 1 }
            if anyRunning m then
              t := noteEx { t with settledRunning := t.settledRunning + 1 } ("settled-running " ++ e.name ++ " k=" ++ toString k)
          if isFuel r then
            t := { t with fuelRuns := t.fuelRuns + 1 }
            if anyRunning m then t := { t with fuelRunning := t.fuelRunning + 1 }
          if isFinished r then
            t := { t with finished := t.finished + 1 }
            if staleExited m > 0 then
              t := noteEx { t with finishedStale := t.finishedStale + 1 } ("finished-stale " ++ e.name ++ " k=" ++ toString k)
  return t

#eval tally
end VerifyScout2Pairs
