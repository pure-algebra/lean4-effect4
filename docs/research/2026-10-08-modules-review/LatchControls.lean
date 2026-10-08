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


end LatchSim

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

/-!
Review controls for MODULES at 29f369ca.
The definitions above reproduce the submitted LatchSim definitions without its evaluations.
These are finite controls for the proposed row 329 client restriction and Conform producer.
They state no new semantic theorem and change no frozen contract.
-/
namespace LatchSim

def identityClient (o : Ops) : Src NativeOp := eff do
  let l ← make false
  let fa ← fork (o.await l)
  let _ ← withFiber (Action.interrupt fa)
  let observer ← fork (withFiber Action.getId)
  join observer

def observedNat (src : Src NativeOp) : Option Nat :=
  (programOf src).bind fun p => (Api.run p 2000).exit.bind fun
    | .success (.nat n) => some n
    | _ => none

#guard (Api.Author.build { main := identityClient library }).isOk
#guard (Api.Author.build { main := identityClient model }).isOk
#guard observedNat (identityClient library) == some 2
#guard observedNat (identityClient model) == some 3
#eval ([library, model] : List Ops).map fun o => observedNat (identityClient o)

-- Numeric identity can affect a Boolean, so final-value renaming is insufficient.
def identityTest (o : Ops) : Src NativeOp :=
  bindWith (identityClient o) fun id => succeed (app "eq" [id, nat 2])
#guard (Api.Author.build { main := identityTest library }).isOk
#guard (Api.Author.build { main := identityTest model }).isOk
#guard ((programOf (identityTest library)).bind fun p => (Api.run p 2000).exit) ==
  some (.success (.bool true))
#guard ((programOf (identityTest model)).bind fun p => (Api.run p 2000).exit) ==
  some (.success (.bool false))

-- No automatic yield accounts for this difference.
#guard ([library, model] : List Ops).all fun o =>
  match programOf (identityClient o) with
  | none => false
  | some p => !((Api.run p 2000).trace.any fun
    | .yieldInjected _ _ => true
    | _ => false)

-- The current search can report no mismatch after discarding both live frontiers.
#guard (exitsOf (c1 library) 0 4 alphabet).isEmpty
#guard (exitsOf (c1 model) 0 4 alphabet).isEmpty
#guard ((exitsOf (c1 library) 0 4 alphabet).filter
  (!(exitsOf (c1 model) 0 4 alphabet).contains ·)).isEmpty

-- It also discards failed elaboration and accepts a scoped but ill-typed client.
#guard (programOf (succeed (var "missing"))).isNone
#guard (exitsOf (succeed (var "missing")) 2000 4 alphabet).isEmpty
#guard (programOf (Ref.get unit)).isSome
#guard !(Api.Author.build { main := Ref.get unit }).isOk

-- Common-model inclusion does not imply equal observations or directed compatibility.
#guard ([1] : List Nat).all ([1, 2].contains ·)
#guard ([2] : List Nat).all ([1, 2].contains ·)
#guard !(([1] : List Nat).all ([2].contains ·))
#guard ([1] : List Nat) != [2]

-- Public client for rc.112 batch coalescing, with no read of the latch's cell.
def batchClient (f : Full) : Src NativeOp := eff do
  let l ← f.make false
  let log ← Ref.make noNumbers
  let a ← fork (andThen (f.ops.await l) (mark log (nat 1)))
  let _ ← f.ops.release l
  let middle ← withFiber (Action.fork (mark log (nat 9)) posted)
  let b ← fork (andThen (f.ops.await l) (mark log (nat 2)))
  let _ ← f.ops.release l
  let _ ← join a
  let _ ← join b
  let _ ← join middle
  Ref.get log

#guard (Api.Author.build { main := batchClient libFull }).isOk
#guard (Api.Author.build { rows := pinRows, main := batchClient pinFull }).isOk
#guard ((programOf (batchClient libFull)).bind fun p => (Api.run p 2000).exit) ==
  some (.success (.list [.nat 1, .nat 9, .nat 2]))

-- Probe whether the permissive model admits both measured batch orders.
#guard
  let es := exitsOf (batchClient { make := make, ops := model }) 2000 4 alphabet
  es.contains (.success (.list [.nat 1, .nat 9, .nat 2])) &&
    es.contains (.success (.list [.nat 1, .nat 2, .nat 9]))

-- Retain an exact mismatch witness, not the original lossy display of ExitV.
#guard ((exitsOf (identityClient library) 2000 4 alphabet).filter
  (!(exitsOf (identityClient model) 2000 4 alphabet).contains ·)) ==
    [.success (.nat 2)]

-- Emit only after both admission and target printing succeed.
def emitReview (name : String) (rows : List RowDef) (src : Src NativeOp) : IO Unit := do
  match Api.Author.build { rows, main := src } with
  | .error _ => throw (IO.userError s!"{name}: Author.build refused")
  | .ok b =>
    match Api.printModule "main" b.program b.table with
    | none => throw (IO.userError s!"{name}: printModule refused")
    | some m => do
      let rendered := String.join (m.decls.map (TypeScript.Render.decl TypeScript.house0))
      IO.FS.writeFile s!"docs/research/2026-10-08-modules-review/{name}.body.ts" rendered

#eval do
  emitReview "batch-lib" [] (batchClient libFull)
  emitReview "batch-pin" pinRows (batchClient pinFull)
  IO.println "batch clients admitted and emitted"

end LatchSim
