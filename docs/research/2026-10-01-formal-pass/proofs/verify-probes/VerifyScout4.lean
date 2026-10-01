import Test.Program.TypedCorpus
import Effect4.Laws.Program.Typed.Assembly

/-! Verifier scouting (tested, no theorem): at fuel frontiers of the typed corpus on the
reference machine, roots that are running, have not exited, hold `pure ex'` over an empty
stack, and whose `ex'` fails the executable shape check at the program's checked type: the
window shape of `StaleCode.window6`, untypable at every valid world under HEAD's TypedState. -/
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Sched Effect4.Program.Typed
open Test.Program.TypedCorpus

namespace VerifyScout4
abbrev RR := ReplayResult EffName EffThunk Val Err Defect FiberId Ann Ctx Stores RProgram RSaved Unit
def interruptRoot : Api.Decision := .interruptFrom none ReasonAnnotations.empty Api.root
def advanceAll : Api.Decision := .advance (ClockMillis.ofNat 100000)
def tapes : List (String × List Api.Decision) := [
  ("quiet", [Api.evaluate, Api.flush]),
  ("timers", [Api.evaluate, Api.flush, advanceAll, Api.flush]),
  ("interrupt", [Api.evaluate, interruptRoot, Api.flush, advanceAll, Api.flush]),
  ("late", [Api.evaluate, Api.flush, .advance (ClockMillis.ofNat 1), interruptRoot, Api.flush, advanceAll, Api.flush])]
def isFuel : RR → Bool | .frontier .fuel _ => true | _ => false

/-- `some true`: the window shape, untypable; `some false`: the window shape, passes the check. -/
def window (ty : EffTy) (m : RState) : Option Bool :=
  match m.fiber? Api.root with
  | none => none
  | some f =>
    if f.exit.isSome || !f.running || !f.frame.stack.isEmpty then none else
    match f.frame.current with
    | .pure ex' => some !(Val.hasTy (reifyExitVal ex') (.exitOf ty.answer ty.error) m.state.externals.allocated)
    | _ => none

def scan : Nat × Nat × Nat × List String := Id.run do
  let mut fuel := 0
  let mut shapes := 0
  let mut bad := 0
  let mut names : List String := []
  for e in programs do
    if e.table.isEmpty then
      match Api.typeOf e.program with
      | none => pure ()
      | some ty =>
        for (tn, tape) in tapes do
          for k in List.range 41 do
            let r := replayR e.program k tape
            if isFuel r then
              fuel := fuel + 1
              match window ty r.machine with
              | some true =>
                shapes := shapes + 1
                bad := bad + 1
                names := (e.name ++ "@" ++ tn ++ " k=" ++ toString k) :: names
              | some false => shapes := shapes + 1
              | none => pure ()
  return (fuel, shapes, bad, names.reverse.take 30)

#eval scan
end VerifyScout4
