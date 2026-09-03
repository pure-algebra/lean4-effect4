import Effect4.Runtime.LiveStack

/-!
# Independent live-stack contract

The exact eight public declarations below fix the generic, whole-result
claims. The finite detector functions below them are independent targets:
they retain full primitive payloads, causes, state and chronological events,
and can be applied to a separately compiled wrong candidate without importing
that candidate's proof claims. They are not a reference traversal.
-/

set_option autoImplicit false

open Effect4
universe u v

#check (@FrameFiber.popLive :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u},
    FrameFiber ν σ β ε δ ι α → Arm → Bool → FramePop ν σ β ε δ ι α)

#check (@FrameFiber.getContLive :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u},
    FrameFiber ν σ β ε δ ι α → Arm → Bool → FramePop ν σ β ε δ ι α)

#check (@FrameFiber.popLive_eq_popFrom :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u}
    (self : FrameFiber ν σ β ε δ ι α) (demand : Arm) (skip : Bool),
    FrameFiber.popLive self demand skip =
      FrameFiber.popFrom demand skip self.stack { self with stack := [] })

#check (@FrameFiber.getContLive_eq_getCont :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u}
    (self : FrameFiber ν σ β ε δ ι α) (demand : Arm) (skip : Bool),
    self.deferredInterrupt = false →
    FrameFiber.getContLive self demand skip = self.getCont demand skip)

#check (@FrameFiber.getContLive_false_eq_getCont :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u}
    (self : FrameFiber ν σ β ε δ ι α) (demand : Arm),
    FrameFiber.getContLive self demand false = self.getCont demand false)

#check (@FrameFiber.getContLive_deferred_kept :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u}
    (self : FrameFiber ν σ β ε δ ι α) (demand : Arm) (skip : Bool),
    self.deferredInterrupt = true → (skip && self.interrupted) = false →
    FrameFiber.getContLive self demand skip =
      (⟨.deferred self.pendingCause, [], [.deferred self.pendingCause],
        { self with deferredInterrupt := false }⟩ : FramePop ν σ β ε δ ι α))

#check (@FrameFiber.getContLive_deferred_discarded :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u}
    (self : FrameFiber ν σ β ε δ ι α) (demand : Arm),
    self.deferredInterrupt = true → self.interrupted = true →
    FrameFiber.getContLive self demand true =
      let next : FramePop ν σ β ε δ ι α :=
        FrameFiber.popLive { self with deferredInterrupt := false } demand true
      { next with events := .deferred self.pendingCause :: next.events })

#check (@FrameFiber.getContLive_while :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u}
    (self : FrameFiber ν σ β ε δ ι α) (demand : Arm),
    FrameFiber.getContLive self demand true =
      let first : FramePop ν σ β ε δ ι α := FrameFiber.getContLive self demand false
      match first.answer with
      | .empty => first
      | _ =>
        if first.fiber.interrupted then
          let next : FramePop ν σ β ε δ ι α :=
            FrameFiber.getContLive first.fiber demand true
          { next with popped := first.popped ++ next.popped,
                      events := first.events ++ next.events }
        else first)

namespace Effect4Test.Runtime.LiveStackContract

private abbrev P := Prim Nat Nat Nat Nat Nat Nat Nat
private abbrev F := FrameFiber Nat Nat Nat Nat Nat Nat Nat
private abbrev R := FramePop Nat Nat Nat Nat Nat Nat Nat
private abbrev C := Cause Nat Nat Nat Nat

private def notes : ReasonAnnotations Nat :=
  ⟨[("z", 17), ("a", 23)], by decide⟩

private def cause : C :=
  ⟨[.fail 41 notes, .interrupt (some 53) .empty, .fail 41 notes]⟩

private def now : P := .onSuccess (.success 101) 107
private def value : P := .onSuccess (.failure cause) 109
private def handler : P := .onFailure (.success 113) 127
private def finalizer : P := .onExit (.failure cause) 131 false
private def interruptibleFinalizer : P := .onExit (.success 137) 139 true

/-! The expected results are written as complete records, not computed by the
old traversal or by a copied recurrence. List order and repeated entries count. -/

def popCases : List (String × F × Arm × Bool × R) := [
  ("empty-keeps-all-other-fields",
    ⟨now, [], false, some cause, true⟩, .contA, false,
    ⟨.empty, [], [], ⟨now, [], false, some cause, true⟩⟩),
  ("value-keeps-body-name-and-suffix",
    ⟨now, [value, handler], true, some cause, false⟩, .contA, false,
    ⟨.frame value, [value], [.popped value],
      ⟨now, [handler], true, some cause, false⟩⟩),
  ("failure-without-skip-keeps-handler",
    ⟨now, [handler, value], true, some cause, false⟩, .contE, false,
    ⟨.frame handler, [handler], [.popped handler],
      ⟨now, [value], true, some cause, false⟩⟩),
  ("mask-stops-skip-after-earlier-handler",
    ⟨now, [handler, .setInterruptible false, handler], true, some cause, false⟩,
    .contE, true,
    ⟨.frame handler, [handler, .setInterruptible false, handler],
      [.popped handler, .popped (.setInterruptible false),
       .ranContAll (.setInterruptible false), .popped handler],
      ⟨now, [], false, some cause, false⟩⟩),
  ("restoring-mask-substitutes-exact-cause",
    ⟨now, [.setInterruptible true, value, handler], false, some cause, false⟩,
    .contA, false,
    ⟨.replacement (.failure cause), [.setInterruptible true],
      [.popped (.setInterruptible true), .ranContAll (.setInterruptible true),
       .substituted cause], ⟨now, [value, handler], true, some cause, false⟩⟩),
  ("restoring-mask-starts-skip",
    ⟨now, [.setInterruptible true, handler], false, some cause, false⟩,
    .contE, true,
    ⟨.empty, [.setInterruptible true, handler],
      [.popped (.setInterruptible true), .ranContAll (.setInterruptible true),
       .substituted cause, .popped handler], ⟨now, [], true, some cause, false⟩⟩),
  ("finalizer-masks-before-discard-test",
    ⟨now, [finalizer, handler], true, some cause, false⟩, .contE, true,
    ⟨.frame finalizer, [finalizer], [.popped finalizer, .ranContAll finalizer],
      ⟨now, [.setInterruptible true, handler], false, some cause, false⟩⟩),
  ("interruptible-finalizer-does-not-stop-skip",
    ⟨now, [interruptibleFinalizer, handler], true, some cause, false⟩, .contE, true,
    ⟨.empty, [interruptibleFinalizer, handler],
      [.popped interruptibleFinalizer, .ranContAll interruptibleFinalizer,
       .popped handler], ⟨now, [], true, some cause, false⟩⟩),
  ("already-masked-finalizer-pushes-nothing",
    ⟨now, [finalizer, handler], false, some cause, true⟩, .contE, true,
    ⟨.frame finalizer, [finalizer], [.popped finalizer, .ranContAll finalizer],
      ⟨now, [handler], false, some cause, true⟩⟩),
  ("duplicate-passed-frames-stay-ordered",
    ⟨now, [value, value, handler], false, none, false⟩, .contE, false,
    ⟨.frame handler, [value, value, handler],
      [.popped value, .popped value, .popped handler],
      ⟨now, [], false, none, false⟩⟩),
  ("non-frame-thunk-is-passed-not-executed",
    ⟨now, [.sync 149, value, handler], false, none, false⟩, .contA, false,
    ⟨.frame value, [.sync 149, value], [.popped (.sync 149), .popped value],
      ⟨now, [handler], false, none, false⟩⟩),
  ("model-contAll-finalizer",
    ⟨now, [finalizer, handler], true, none, false⟩, .contAll, true,
    ⟨.frame finalizer, [finalizer], [.popped finalizer, .ranContAll finalizer],
      ⟨now, [.setInterruptible true, handler], false, none, false⟩⟩),
  ("model-contAll-mask",
    ⟨now, [.setInterruptible false, handler], true, some cause, false⟩,
    .contAll, true,
    ⟨.frame (.setInterruptible false), [.setInterruptible false],
      [.popped (.setInterruptible false), .ranContAll (.setInterruptible false)],
      ⟨now, [handler], false, some cause, false⟩⟩)
]

def entryCases : List (String × F × Arm × Bool × R) := [
  ("plain-entry-finalizer", ⟨now, [finalizer, handler], true, some cause, false⟩,
    .contE, true,
    ⟨.frame finalizer, [finalizer], [.popped finalizer, .ranContAll finalizer],
      ⟨now, [.setInterruptible true, handler], false, some cause, false⟩⟩),
  ("deferred-value-keeps-entire-stack", ⟨now, [value, handler], true, some cause, true⟩,
    .contA, false,
    ⟨.deferred cause, [], [.deferred cause],
      ⟨now, [value, handler], true, some cause, false⟩⟩),
  ("deferred-failure-no-skip", ⟨now, [handler], true, some cause, true⟩,
    .contE, false,
    ⟨.deferred cause, [], [.deferred cause], ⟨now, [handler], true, some cause, false⟩⟩),
  ("masked-deferred-failure-is-not-discarded", ⟨now, [handler], false, some cause, true⟩,
    .contE, true,
    ⟨.deferred cause, [], [.deferred cause], ⟨now, [handler], false, some cause, false⟩⟩),
  ("deferred-without-cause-is-total-model-state", ⟨now, [handler], true, none, true⟩,
    .contE, true,
    ⟨.deferred Cause.empty, [], [.deferred Cause.empty], ⟨now, [handler], true, none, false⟩⟩),
  ("discarded-deferred-event-precedes-pop",
    ⟨now, [.setInterruptible false, handler], true, some cause, true⟩, .contE, true,
    ⟨.frame handler, [.setInterruptible false, handler],
      [.deferred cause, .popped (.setInterruptible false),
       .ranContAll (.setInterruptible false), .popped handler],
      ⟨now, [], false, some cause, false⟩⟩),
  ("discarded-deferred-event-survives-empty-stack", ⟨now, [], true, some cause, true⟩,
    .contE, true,
    ⟨.empty, [], [.deferred cause], ⟨now, [], true, some cause, false⟩⟩),
  ("empty-unmasked-no-pending", ⟨now, [], true, none, false⟩, .contE, true,
    ⟨.empty, [], [], ⟨now, [], true, none, false⟩⟩),
  ("model-contAll-deferred-before-mask",
    ⟨now, [.setInterruptible false, handler], false, some cause, true⟩,
    .contAll, true,
    ⟨.deferred cause, [], [.deferred cause],
      ⟨now, [.setInterruptible false, handler], false, some cause, false⟩⟩)
]

def checkCases (cases : List (String × F × Arm × Bool × R))
    (candidate : F → Arm → Bool → R) : Bool :=
  cases.all fun (_, self, demand, skip, expected) =>
    decide (candidate self demand skip = expected)

/- Frozen positive control for the independently written pop table. -/
#guard checkCases popCases (fun self demand skip =>
  FrameFiber.popFrom demand skip self.stack { self with stack := [] })

#guard popCases.length = 13
#guard entryCases.length = 9
#guard checkCases popCases FrameFiber.popLive
#guard checkCases entryCases FrameFiber.getContLive

end Effect4Test.Runtime.LiveStackContract
