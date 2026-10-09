module

public import Effect4.Library.SynchronizedRef.Cell
public import Effect4.Library.Semaphore.Ops
public import Effect4.Step.Callback

/-! A pure SynchronizedRef callback composes the existing Semaphore wrapper with Ref.modify.
The value transition remains Ref.Model.modify.
No effectful callback, schedule agreement, waiting progress, or host behavior is claimed.
Sources: vendor/effect-4.0.1/src/SynchronizedRef.ts, construction 66–71, get 123, modify 487–489. -/

@[expose] public section
set_option autoImplicit false
namespace Effect4.SynchronizedRef
open Effect4.Program Effect4.Program.Authoring Effect4.Modules

/-- Allocate a backing reference and one permit, as latest's makeUnsafe does at 66–71.
The record declaration checks the requested backing value type. -/
def make (A : Ty) (initial : TermSrc) : Src NativeOp :=
  bindWith (Ref.make initial) fun backing =>
    bindWith (Semaphore.make 1) fun semaphore =>
      succeed (record (handleFields A) [("backing", backing), ("semaphore", semaphore)])

/-- Read the backing reference directly, as latest's get does at 123. -/
def get (self : TermSrc) : Src NativeOp := Ref.get (field self "backing")

/-- Run a pure stored callback under one permit, as latest's modify does at 487–489.
Self and captures resolve before the wrapper adds locals.
The existing Ref callback connector supplies the current-value binder. -/
def modify {A B : Ty} {Γ : List Ty} (self : TermSrc)
    (body : Step (A :: Γ) (.prod B A))
    (captures : {t : Ty} → Input Γ t → TermSrc) : Src NativeOp :=
  fun env path =>
    let held := Step.freeze self env path
    let inputs : {t : Ty} → Input Γ t → TermSrc := fun x => Step.freeze (captures x) env path
    Semaphore.withPermits (field held "semaphore") (nat 1)
      (Step.callback body inputs (Ref.modifyWith (field held "backing"))) env path

end Effect4.SynchronizedRef
