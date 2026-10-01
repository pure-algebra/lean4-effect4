import Test.Program.TypedCorpus
import Effect4.Laws.Program.Typed.Assembly

/-! Verifier scouting (tested, no theorem): on finished reference runs of the typed corpus, the
root's code slot after it exited. `pure ex'` whose reified exit fails the executable shape check
at the program's checked type cannot be typed at any valid world (`fits_hasTy`, contrapositive;
the stack is empty after `exitDone`), so the current `TypedState` fails there. -/
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Sched Effect4.Program.Typed
open Test.Program.TypedCorpus

namespace VerifyScout3
abbrev RR := ReplayResult EffName EffThunk Val Err Defect FiberId Ann Ctx Stores RProgram RSaved Unit
def interruptRoot : Api.Decision := .interruptFrom none ReasonAnnotations.empty Api.root
def advanceAll : Api.Decision := .advance (ClockMillis.ofNat 100000)
def tapes : List (String × List Api.Decision) := [
  ("quiet", [Api.evaluate, Api.flush]),
  ("timers", [Api.evaluate, Api.flush, advanceAll, Api.flush]),
  ("interrupt", [Api.evaluate, interruptRoot, Api.flush, advanceAll, Api.flush]),
  ("late", [Api.evaluate, Api.flush, .advance (ClockMillis.ofNat 1), interruptRoot, Api.flush, advanceAll, Api.flush])]
def isFinished : RR → Bool | .finished _ => true | _ => false

/-- The root's code-slot verdict at a finished run: `0` code is its exit, `1` pure and passes the
shape check, `2` pure and fails it (untypable), `3` a `vis` node, `4` stack not empty. -/
def verdict (ty : EffTy) (m : RState) : Option Nat :=
  (m.fiber? Api.root).bind fun f => f.exit.map fun ex =>
    if !f.frame.stack.isEmpty then 4 else
    match f.frame.current with
    | .pure ex' =>
      if decide (ex = ex') then 0
      else if Val.hasTy (reifyExitVal ex') (.exitOf ty.answer ty.error)
          m.state.externals.allocated then 1 else 2
    | .vis _ _ => 3

structure T where
  finished : Nat := 0
  counts : List Nat := [0, 0, 0, 0, 0]
  untypable : List String := []
deriving Repr

def bump (l : List Nat) (i : Nat) : List Nat := l.modify i (· + 1)

def scan : T := Id.run do
  let mut t : T := {}
  for e in programs do
    if e.table.isEmpty then
      match Api.typeOf e.program with
      | none => pure ()
      | some ty =>
        for (tn, tape) in tapes do
          let r := replayR e.program 4000 tape
          if isFinished r then
            t := { t with finished := t.finished + 1 }
            match verdict ty r.machine with
            | none => pure ()
            | some v =>
              t := { t with counts := bump t.counts v }
              if v == 2 then t := { t with untypable := (e.name ++ "@" ++ tn) :: t.untypable }
  return t

#eval let t := scan; (t.finished, t.counts, t.untypable.length, t.untypable.reverse.take 40)

def visName : RProgram → String
  | .vis (.inr op) _ => match op with
    | .unguard _ => "unguard" | .finishFinalizer _ => "finishFinalizer" | .scopeExit _ _ _ => "scopeExit"
    | .setContext _ => "setContext" | .closeScope _ _ => "closeScope" | .guard_ _ => "guard"
    | .await _ _ => "await" | _ => "fiber-other"
  | .vis (.inl _) _ => "store"
  | .pure _ => "pure"

/-- Category-1 runs (pure code slot differing from the exit) and the `vis` shapes. -/
def details : List String × List (String × Nat) := Id.run do
  let mut ones : List String := []
  let mut shapes : List (String × Nat) := []
  for e in programs do
    if e.table.isEmpty then
      match Api.typeOf e.program with
      | none => pure ()
      | some ty =>
        for (tn, tape) in tapes do
          let r := replayR e.program 4000 tape
          if isFinished r then
            match verdict ty r.machine, (r.machine.fiber? Api.root) with
            | some 1, _ => ones := (e.name ++ "@" ++ tn) :: ones
            | some 3, some f =>
              let n := visName f.frame.current
              shapes := match shapes.find? (·.1 == n) with
                | some _ => shapes.map fun (a, c) => if a == n then (a, c + 1) else (a, c)
                | none => (n, 1) :: shapes
            | _, _ => pure ()
  return (ones.reverse, shapes)

#eval details

/-- Exited roots at finished runs whose code slot is an `unguard`/`finishFinalizer` marker whose
payload fails the shape check at the program's type (the marker arms of `TypedProg` type the
payload at the slot's type, here the declared type over the cleared stack). -/
def markerBad : Nat × Nat := Id.run do
  let mut markers := 0
  let mut bad := 0
  for e in programs do
    if e.table.isEmpty then
      match Api.typeOf e.program with
      | none => pure ()
      | some ty =>
        for (_, tape) in tapes do
          let r := replayR e.program 4000 tape
          if isFinished r then
            match r.machine.fiber? Api.root with
            | some f =>
              if f.exit.isSome && f.frame.stack.isEmpty then
                match f.frame.current with
                | .vis (.inr (.unguard ex')) _ | .vis (.inr (.finishFinalizer ex')) _ =>
                  markers := markers + 1
                  if !(Val.hasTy (reifyExitVal ex') (.exitOf ty.answer ty.error)
                      r.machine.state.externals.allocated) then bad := bad + 1
                | _ => pure ()
            | none => pure ()
  return (markers, bad)

#eval markerBad
end VerifyScout3
