import Test.Program.SemaphoreScenarios
import Effect4.Program.Authoring.Defs

/-! Probe MODS-3: Latch's library against its atomic model filling, over bounded schedules.

The model filling: each operation is one atomic step of the cell, and nothing is posted. A
waiting `await` enrols, then a private spinner polls its own ready predicate (the latch is open,
or the request is no longer enrolled: a release let it through) and resolves the request's
hint. The check: every root exit of the library is a root exit of the model filling. A red
control: a release that opens the latch. -/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Authoring Effect4.Modules
open Test.Program.SemaphoreScenarios (mark noNumbers)

namespace LatchSim

/-! ## The cell and its steps: terms -/
def waiterFields : List (String × Bool × Ty) := [("id", false, idTy), ("hint", false, idTy)]
def cellFields : List (String × Bool × Ty) :=
  [("open", false, .bool), ("waiters", false, .list (.record [("hint", false, idTy), ("id", false, idTy)]))]

def awaitStep (id hint s : TermSrc) : TermSrc :=
  ifT (field s "open") (app "pair" [bool true, s])
    (app "pair" [bool false, recordSet s "waiters"
      (snoc (removeById (field s "waiters") id) (record waiterFields [("id", id), ("hint", hint)]))])
def wakeStep (setOpen : Bool) (s : TermSrc) : TermSrc :=
  let woken := field s "waiters"
  let emptied := recordSet s "waiters" (noneOf woken)
  ifT (field s "open") (app "pair" [tuple [bool false, noneOf woken], s])
    (app "pair" [tuple [bool true, woken],
      if setOpen then recordSet emptied "open" (bool true) else emptied])
def closeStep (s : TermSrc) : TermSrc :=
  ifT (field s "open") (app "pair" [bool true, recordSet s "open" (bool false)])
    (app "pair" [bool false, s])
def withdrawStep (id s : TermSrc) : TermSrc :=
  app "pair" [unit, recordSet s "waiters" (removeById (field s "waiters") id)]

/-! ## The operations: the waiting wrapper -/
def make (isOpen : Bool) : Src NativeOp :=
  Ref.make (record cellFields [("open", bool isOpen), ("waiters", nilT)])
def await (q : TermSrc) : Src NativeOp :=
  waitAnswer
    { hint := .unit
      attempt := fun id hint wait done =>
        bindWith (Ref.modifyWith q (awaitStep id hint)) fun passed => ifElse passed (done unit) wait
      withdraw := fun id => Ref.modifyWith q (withdrawStep id) }
def wake (setOpen : Bool) (q : TermSrc) : Src NativeOp :=
  uninterruptible
    (bindWith (Ref.modifyWith q (wakeStep setOpen)) fun reply =>
      andThen (postAll (tupleAt reply 1) unit) (succeed (tupleAt reply 0)))
def openL (q : TermSrc) : Src NativeOp := wake true q
def release (q : TermSrc) : Src NativeOp := wake false q
def close (q : TermSrc) : Src NativeOp := Ref.modifyWith q closeStep

/-! ## As definitions: one `Def.of` each -/
def cellTy : Ty := .record [("open", false, .bool),
  ("waiters", false, .list (.record [("hint", false, idTy), ("id", false, idTy)]))]
def handleTy : Ty := .refOf cellTy
def awaitD := Def.of "latchAwait" [("latch", handleTy)] .unit await
def openD := Def.of "latchOpen" [("latch", handleTy)] .bool openL
def releaseD := Def.of "latchRelease" [("latch", handleTy)] .bool release
def closeD := Def.of "latchClose" [("latch", handleTy)] .bool close
def defs : List (DefSrc NativeOp) := [awaitD.src, openD.src, releaseD.src, closeD.src]


/-! ## The interface record, the library filling and a fault -/
structure Ops where
  await : TermSrc → Src NativeOp
  openL : TermSrc → Src NativeOp
  release : TermSrc → Src NativeOp

def library : Ops := { await := await, openL := openL, release := release }
/-- Fault: a release that opens the latch. -/
def releaseOpens : Ops := { await := await, openL := openL, release := openL }

/-! ## The model filling -/

/-- Whether the request is still enrolled: removing it shortens the list. -/
def enrolled (ws id : TermSrc) : TermSrc := notT (app "eq" [len (removeById ws id), len ws])
/-- The ready predicate of a request, as a step that changes nothing. -/
def readyStep (id s : TermSrc) : TermSrc :=
  app "pair" [orT (field s "open") (notT (enrolled (field s "waiters") id)), s]

def spinnerOptions : Effect4.Supervision.ForkOptions := ⟨true, true, .interruptible⟩

def spinner (q id done : TermSrc) : Src NativeOp :=
  iterateWith (bool false)
    { while_ := fun passed => notT passed
      body := fun _ => andThen (yieldNow 0)
        (bindWith (Ref.modifyWith q (readyStep id)) fun passed =>
          ifElse passed (andThen (Deferred.succeed done unit) (succeed (bool true)))
            (succeed (bool false)))
      step := fun _ next => next }

def mAwait (q : TermSrc) : Src NativeOp :=
  uninterruptibleMaskWith fun restore =>
    bindWith (Deferred.make .unit .never) fun id =>
      bindWith (Ref.modifyWith q (awaitStep id id)) fun passed =>
        ifElse passed (succeed unit)
          (bindWith (Deferred.make .unit .never) fun done =>
            bindWith (fork (spinner q id done) spinnerOptions) fun sp =>
              onInterrupt (restore (Deferred.await done))
                (andThen (withFiber (Action.interrupt sp)) (Ref.modifyWith q (withdrawStep id))))

def mWake (setOpen : Bool) (q : TermSrc) : Src NativeOp :=
  bindWith (Ref.modifyWith q (wakeStep setOpen)) fun reply => succeed (tupleAt reply 0)

def model : Ops := { await := mAwait, openL := mWake true, release := mWake false }

/-! ## Clients: marks in their own log, no read of the latch -/

/-- C1: A waits; the root releases; B waits after the release; the root marks 3 and opens. -/
def c1 (o : Ops) : Src NativeOp := eff do
  let l ← make false
  let log ← Ref.make noNumbers
  let fa ← fork (andThen (o.await l) (mark log (nat 1)))
  let _ ← o.release l
  let fb ← fork (andThen (o.await l) (mark log (nat 2)))
  let _ ← mark log (nat 3)
  let _ ← o.openL l
  let _ ← join fa
  let _ ← join fb
  let x ← Ref.get log
  return x

/-- C2: two waiters; one open lets both through; the root's mark races them. -/
def c2 (o : Ops) : Src NativeOp := eff do
  let l ← make false
  let log ← Ref.make noNumbers
  let fa ← fork (andThen (o.await l) (mark log (nat 1)))
  let fb ← fork (andThen (o.await l) (mark log (nat 2)))
  let _ ← o.openL l
  let _ ← mark log (nat 3)
  let _ ← join fa
  let _ ← join fb
  let x ← Ref.get log
  return x

def programOf (src : Src NativeOp) : Option Api.Program := (elaborateModule { main := src }).toOption
def rootExit (m : Api.Machine) : Option ExitV := (m.fiber? Api.root).bind RunFiber.exit
def explore (p : Api.Program) (fuel : Nat) (alphabet : List Api.Decision) :
    Nat → Api.Machine → List ExitV
  | 0, m => (rootExit m).toList
  | depth + 1, m =>
    letI := evaluatorFor p []
    (rootExit m).toList ++ alphabet.flatMap fun d =>
      if m.stuck.isSome then []
      else
        let r := stepDecisionState (interpOf p []) fuel m d
        if r.2 then explore p fuel alphabet depth r.1 else []
def exitsOf (src : Src NativeOp) (fuel depth : Nat) (alphabet : List Api.Decision) : List ExitV :=
  match programOf src with
  | none => []
  | some p =>
    letI := evaluatorFor p []
    let r := stepDecisionState (interpOf p []) fuel (Api.load p fuel) Api.evaluate
    if r.2 then (explore p fuel alphabet depth r.1).eraseDups else []

def alphabet : List Api.Decision :=
  [Api.flush, .fire ⟨0⟩, .fire ⟨1⟩, .fire ⟨2⟩, .fire ⟨3⟩, .fire ⟨4⟩, .fire ⟨5⟩]

partial def numbersOf : Val → List Nat
  | .nat n => [n]
  | .list vs => vs.flatMap numbersOf
  | _ => []
def shown (es : List ExitV) : List (List Nat) :=
  es.map fun
    | .success v => numbersOf v
    | .failure _ => [1000]

end LatchSim

open LatchSim in
#eval ([c1, c2] : List (Ops → Src NativeOp)).map fun c =>
  let lib := exitsOf (c library) 2000 4 alphabet
  let mod := exitsOf (c model) 2000 4 alphabet
  (shown lib, shown mod, shown (lib.filter (!mod.contains ·)))

open LatchSim in
#eval ([c1, c2] : List (Ops → Src NativeOp)).map fun c =>
  let bad := exitsOf (c releaseOpens) 2000 4 alphabet
  let mod := exitsOf (c model) 2000 4 alphabet
  shown (bad.filter (!mod.contains ·))

/-! ## Probe MODS-4: the pin's own Latch as host rows, beside the library, on rc.112 -/

namespace LatchSim

def latchTy : Ty := .handle "Latch.Latch"
def pinMake : RowDef := Row.host "Latch.make" .bool latchTy
def pinAwait : RowDef := Row.host "Latch.await" latchTy .unit
def pinOpen : RowDef := Row.host "Latch.open" latchTy .bool
def pinRelease : RowDef := Row.host "Latch.release" latchTy .bool
def pinRows : List RowDef := [pinMake, pinAwait, pinOpen, pinRelease]

/-- A client over a constructor too, so the pin's handle is the pin's. -/
structure Full where
  make : Bool → Src NativeOp
  ops : Ops

def libFull : Full := { make := make, ops := library }
def pinFull : Full :=
  { make := fun b => Row.call pinMake (bool b)
    ops := { await := Row.call pinAwait, openL := Row.call pinOpen, release := Row.call pinRelease } }

def d1 (f : Full) : Src NativeOp := eff do
  let l ← f.make false
  let log ← Ref.make noNumbers
  let fa ← fork (andThen (f.ops.await l) (mark log (nat 1)))
  let _ ← f.ops.release l
  let fb ← fork (andThen (f.ops.await l) (mark log (nat 2)))
  let _ ← mark log (nat 3)
  let _ ← f.ops.openL l
  let _ ← join fa
  let _ ← join fb
  let x ← Ref.get log
  return x

def d2 (f : Full) : Src NativeOp := eff do
  let l ← f.make false
  let log ← Ref.make noNumbers
  let fa ← fork (andThen (f.ops.await l) (mark log (nat 1)))
  let fb ← fork (andThen (f.ops.await l) (mark log (nat 2)))
  let _ ← f.ops.openL l
  let _ ← mark log (nat 3)
  let _ ← join fa
  let _ ← join fb
  let x ← Ref.get log
  return x

/-- A waiter interrupted while it waits, then an open: the log holds only the root's mark. -/
def d3 (f : Full) : Src NativeOp := eff do
  let l ← f.make false
  let log ← Ref.make noNumbers
  let fa ← fork (andThen (f.ops.await l) (mark log (nat 1)))
  let _ ← yieldNow 0
  let _ ← withFiber (Action.interrupt fa)
  let o ← f.ops.openL l
  let _ ← mark log (nat 3)
  let x ← Ref.get log
  return tuple [o, x]

def textOf (rows : List RowDef) (src : Src NativeOp) : String :=
  match Effect4.Api.Author.build { rows := rows, main := src } with
  | .ok b => match Api.printModule "main" b.program (RowDef.table rows) with
    | some m => String.join (m.decls.map (TypeScript.Render.decl TypeScript.house0))
    | none => "// print refused"
  | .error _ => "// build refused"

end LatchSim

open LatchSim in
#eval do
  let dir := "docs/research/2026-10-08-seat-MODULES/pin"
  for (name, c) in [("d1", d1), ("d2", d2), ("d3", d3)] do
    IO.FS.writeFile s!"{dir}/{name}-lib.ts" (textOf [] (c libFull))
    IO.FS.writeFile s!"{dir}/{name}-pin.ts" (textOf pinRows (c pinFull))
  return "written"

open LatchSim in
#eval [d1, d2, d3].map fun c =>
  match programOf (c libFull) with
  | some p => shown ((Api.run p 2000).exit.toList)
  | none => [[999]]
