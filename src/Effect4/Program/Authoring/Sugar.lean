import Effect4.Program.Authoring.Lifts

/-!
# Program.Authoring.Sugar — the native rows as Effect spells them, and derived forms

A row is `perform` of its operation on its request; these give the native rows the names the
printed image carries (`Ref.make(0)`, `Ref.get(r)`, `Ref.set(r, 1)`), so an authored program
reads like the Effect it prints to. A pair request is the `pair` atom. Package rows get the
same treatment from the generated tables (DI-89); these hand-written wrappers cover the native
alphabet until that generator exists and are the only hand-written row spellings.

The derived forms are `Src`-level functions over the generated lifts: no constructor, no
second expansion owner (`Codegen/Forms` prints them by recognition).
-/

namespace Effect4.Program.Authoring

open Effect4.Program

/-! ## Binders as Lean functions over a fresh name.

The fresh name is minted from the scope's length, so it can shadow nothing an author wrote
with a different spelling and resolves to itself at the nearest binder. -/

/-- `bindWith first (fun r => rest)` is `bind "_<level>" first rest` with `r` the variable. -/
def bindWith {Op : Type} (first : Src Op) (rest : TermSrc → Src Op) : Src Op := fun env p =>
  let x := "_" ++ toString env.names.length
  bind x first (rest (var x)) env p

/-- `Effect.flatMap` under its Effect name. -/
def flatMap {Op : Type} (answer : String) (first rest : Src Op) : Src Op := bind answer first rest

/-- `Effect.andThen` with a discarded answer. -/
def andThen {Op : Type} (first rest : Src Op) : Src Op := bind "_" first rest

/-- `Effect.map` through a pure atom: `bind` then `succeed` of the atom applied to the answer. -/
def map {Op : Type} (atom : String) (effect : Src Op) : Src Op :=
  bindWith effect fun v => succeed (app atom [v])

/-- `Effect.if`: `if` is a Lean keyword. -/
def ifElse {Op : Type} (test : TermSrc) (thenB elseB : Src Op) : Src Op := branch test thenB elseB

/-! ## The native rows -/

namespace Ref

def make (value : TermSrc) : Src NativeOp := perform .refMake value
def get (ref : TermSrc) : Src NativeOp := perform .refGet ref
def set (ref value : TermSrc) : Src NativeOp := perform .refSet (app "pair" [ref, value])
def getAndSet (ref value : TermSrc) : Src NativeOp := perform .refGetAndSet (app "pair" [ref, value])
def setAndGet (ref value : TermSrc) : Src NativeOp := perform .refSetAndGet (app "pair" [ref, value])
def update (f : Effect4.Machine.FnName) (ref : TermSrc) : Src NativeOp := perform (.refUpdate f) ref
def getAndUpdate (f : Effect4.Machine.FnName) (ref : TermSrc) : Src NativeOp :=
  perform (.refGetAndUpdate f) ref
def updateAndGet (f : Effect4.Machine.FnName) (ref : TermSrc) : Src NativeOp :=
  perform (.refUpdateAndGet f) ref
def modify (f : Effect4.Machine.FnName) (ref : TermSrc) : Src NativeOp := perform (.refModify f) ref

end Ref

namespace Deferred

def make : Src NativeOp := perform .deferredMake unit
def isDone (deferred : TermSrc) : Src NativeOp := perform .deferredIsDone deferred
def poll (deferred : TermSrc) : Src NativeOp := perform .deferredPoll deferred
def await (deferred : TermSrc) : Src NativeOp := perform .deferredAwait deferred
def succeed (deferred value : TermSrc) : Src NativeOp :=
  perform .deferredSucceed (app "pair" [deferred, value])
def fail (deferred error : TermSrc) : Src NativeOp :=
  perform .deferredFail (app "pair" [deferred, error])

end Deferred

end Effect4.Program.Authoring
