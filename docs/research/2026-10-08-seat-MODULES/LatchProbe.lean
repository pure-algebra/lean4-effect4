import Effect4
import Effect4.Program.Authoring.Defs
import Effect4.Modules.Waiting

/-! Probe MODS-1: Effect's `Latch` (vendor/effect-4.0.0-rc.112/src/Latch.ts, `class Latch` of
internal/effect.ts) written with today's tools: model, cell, steps, operations, definitions. -/

open Effect4 Effect4.Program Effect4.Program.Authoring Effect4.Modules

namespace LatchProbe

/-! ## The model (the spec): pure Lean -/
namespace Model
structure State where
  isOpen : Bool
  waiters : List Nat
  deriving DecidableEq, Repr

/-- `await`: pass when open; else enrol (own entry first removed). -/
def await (s : State) (id : Nat) : State × Bool :=
  if s.isOpen then (s, true) else ({ s with waiters := s.waiters.filter (· != id) ++ [id] }, false)
/-- `open`: true where it was closed; every waiter is woken. -/
def openL (s : State) : State × (Bool × List Nat) :=
  if s.isOpen then (s, (false, [])) else (⟨true, []⟩, (true, s.waiters))
/-- `release`: true where closed; every current waiter is woken, the latch stays closed. -/
def release (s : State) : State × (Bool × List Nat) :=
  if s.isOpen then (s, (false, [])) else ({ s with waiters := [] }, (true, s.waiters))
/-- `close`: true where it was open. -/
def close (s : State) : State × Bool :=
  if s.isOpen then ({ s with isOpen := false }, true) else (s, false)
def withdraw (s : State) (id : Nat) : State := { s with waiters := s.waiters.filter (· != id) }
end Model

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

/-! ## Clients over an interface record -/
structure Ops where
  make : Bool → Src NativeOp
  await : TermSrc → Src NativeOp
  openL : TermSrc → Src NativeOp
  release : TermSrc → Src NativeOp
  close : TermSrc → Src NativeOp

def inlined : Ops :=
  { make := make, await := await, openL := openL, release := release, close := close }
def invoked : Ops :=
  { make := make, await := awaitD.call, openL := openD.call, release := releaseD.call,
    close := closeD.call }

/-- L1: a waiter forked at a closed latch; the root opens it; the waiter's mark follows. -/
def l1 (o : Ops) : Src NativeOp := eff do
  let l ← o.make false
  let f ← fork (andThen (o.await l) (succeed (nat 7)))
  let a ← o.openL l
  let b ← o.openL l
  let x ← join f
  return tuple [a, b, x]

/-- L2: release wakes the current waiter; the latch stays closed; close answers false. -/
def l2 (o : Ops) : Src NativeOp := eff do
  let l ← o.make false
  let f ← fork (andThen (o.await l) (succeed (nat 1)))
  let r ← o.release l
  let x ← join f
  let c ← o.close l
  return tuple [r, x, c]

/-- L3: an interrupted waiter withdraws; the cell keeps no waiter. -/
def l3 (o : Ops) : Src NativeOp := eff do
  let l ← o.make false
  let f ← fork (o.await l)
  let _ ← withFiber (Action.interrupt f)
  let a ← o.openL l
  let s ← Ref.get l
  return tuple [a, len (field s "waiters")]

def build (m : Module NativeOp) : Option Api.Program :=
  (Effect4.Api.Author.build m).toOption.map (·.program)
def exitOf (p : Api.Program) : Option Machine.ExitV := (Api.run p 2000).exit
def renderLen (p : Api.Program) : Option Nat :=
  (Api.printModule "main" p).map fun m => (String.join (m.decls.map (TypeScript.Render.decl TypeScript.house0))).length

end LatchProbe

open LatchProbe in
#eval [l1, l2, l3].map fun c =>
  ((build { main := c inlined }).isSome, (build { main := c invoked, defs := defs }).isSome)
open LatchProbe in
#eval [l1, l2, l3].map fun c =>
  let a := (build { main := c inlined }).bind exitOf
  let b := (build { main := c invoked, defs := defs }).bind exitOf
  (a.isSome, decide (a = b))
open LatchProbe in
#eval decide ((build { main := l1 invoked, defs := defs }).bind exitOf =
  some (.success (.list [.bool true, .bool false, .nat 7])))
open LatchProbe in
#eval decide ((build { main := l2 invoked, defs := defs }).bind exitOf =
  some (.success (.list [.bool true, .nat 1, .bool false])))
open LatchProbe in
#eval decide ((build { main := l3 invoked, defs := defs }).bind exitOf =
  some (.success (.list [.bool true, .nat 0])))
open LatchProbe in
#eval [l1, l2, l3].map fun c =>
  ((build { main := c inlined }).bind renderLen, (build { main := c invoked, defs := defs }).bind renderLen)
