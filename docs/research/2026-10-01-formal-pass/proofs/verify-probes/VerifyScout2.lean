import Test.Program.TypedCorpus
import Effect4.Laws.Program.Typed.Assembly

/-! Verifier scouting (tested, no theorem): (1) the typed corpus on the reference machine at
small and large command budgets: whether any fiber is `running` at a settled result
(`finished` or a consumed tape), and how often an exited fiber's code slot is not its exit;
(2) the store rows seat PROOFS did not scout; (3) the denoted root of `awaitFiber.value`. -/
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Sched Effect4.Program.Typed
open Test.Program.TypedCorpus

namespace VerifyScout2

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
  for e in programs do
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

-- (2) store rows not in seat PROOFS' scout, on a store holding one `bool` cell, one deferred and
-- one memo map with an entry
def boolCellStore : Stores :=
  (syncOpStep (.refMake (.bool true)) Stores.empty).map (·.1) |>.getD Stores.empty
def shape : Val → String
  | .unit => "unit" | .nat _ => "nat" | .bool _ => "bool" | .str _ => "str"
  | v => s!"other {(repr v).pretty.take 50}"
#eval [("refModify incr @bool", syncOpStep (.refModify ⟨0⟩ .incr) boolCellStore),
       ("refModifySome incr @bool", syncOpStep (.refModifySome ⟨0⟩ .incr) boolCellStore),
       ("refGetAndUpdateSome @bool", syncOpStep (.refGetAndUpdateSome ⟨0⟩ .incr) boolCellStore),
       ("refUpdateSomeAndGet @bool", syncOpStep (.refUpdateSomeAndGet ⟨0⟩ .incr) boolCellStore)].map
  fun (n, r) => match r with | none => s!"{n}: frontier" | some (_, v) => s!"{n}: {shape v}"

def memoStore : Stores :=
  let s1 := (syncOpStep (.memoFork none) Stores.empty).map (·.1) |>.getD Stores.empty
  (syncOpStep (.memoBuild [] ⟨0⟩) s1).map (·.1) |>.getD s1
#eval [("memoRelease (one observer)", syncOpStep (.memoRelease [] ⟨0⟩) memoStore),
       ("memoComplete", syncOpStep (.memoComplete [] ⟨0⟩ (.success .unit)) memoStore),
       ("memoGet", syncOpStep (.memoGet [] ⟨0⟩) memoStore)].map
  fun (n, r) => match r with | none => s!"{n}: frontier" | some (_, v) => s!"{n}: {shape v}"

-- (3) the corpus's await-by-value entry: its checked type and the head of its denoted root
def awaitProg : NativeEff := .bind forked (.awaitFiber (v 0) .awaitValue)
#eval (Api.typeOf awaitProg).isSome
#eval match Api.typeOf awaitProg with
  | some t => decide (t = EffTy.pure (.exitOf .nat .never)) | none => false
def head : RProgram → String
  | .pure _ => "pure"
  | .vis (.inl _) _ => "store"
  | .vis (.inr op) _ => match op with
    | .fork _ _ _ => "fork" | .await _ .awaitValue => "await-value" | .await _ _ => "await-join"
    | .guard_ _ => "guard" | .suspend _ => "suspend" | .construction => "construction" | _ => "fiber-other"
#eval head (denoteR awaitProg awaitProg (rootPoint 5))
end VerifyScout2
