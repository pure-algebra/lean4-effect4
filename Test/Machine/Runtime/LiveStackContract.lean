import Effect4.Laws.Machine.LiveStack

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

namespace Test.Runtime.LiveStackContract

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
    ⟨.empty, [], [], ⟨now, [], false, some cause, true⟩, none⟩),
  ("value-keeps-body-name-and-suffix",
    ⟨now, [value, handler], true, some cause, false⟩, .contA, false,
    ⟨.frame value, [value], [.popped value],
      ⟨now, [handler], true, some cause, false⟩, none⟩),
  ("failure-without-skip-keeps-handler",
    ⟨now, [handler, value], true, some cause, false⟩, .contE, false,
    ⟨.frame handler, [handler], [.popped handler],
      ⟨now, [value], true, some cause, false⟩, none⟩),
  ("mask-stops-skip-after-earlier-handler",
    ⟨now, [handler, .setInterruptible false, handler], true, some cause, false⟩,
    .contE, true,
    ⟨.frame handler, [handler, .setInterruptible false, handler],
      [.popped handler, .popped (.setInterruptible false),
       .ranContAll (.setInterruptible false), .popped handler],
      ⟨now, [], false, some cause, false⟩, none⟩),
  ("restoring-mask-substitutes-exact-cause",
    ⟨now, [.setInterruptible true, value, handler], false, some cause, false⟩,
    .contA, false,
    ⟨.replacement (.failure cause), [.setInterruptible true],
      [.popped (.setInterruptible true), .ranContAll (.setInterruptible true),
       .substituted cause], ⟨now, [value, handler], true, some cause, false⟩, none⟩),
  ("restoring-mask-starts-skip",
    ⟨now, [.setInterruptible true, handler], false, some cause, false⟩,
    .contE, true,
    ⟨.empty, [.setInterruptible true, handler],
      [.popped (.setInterruptible true), .ranContAll (.setInterruptible true),
       .substituted cause, .popped handler], ⟨now, [], true, some cause, false⟩, none⟩),
  ("finalizer-masks-before-discard-test",
    ⟨now, [finalizer, handler], true, some cause, false⟩, .contE, true,
    ⟨.frame finalizer, [finalizer], [.popped finalizer, .ranContAll finalizer],
      ⟨now, [.setInterruptible true, handler], false, some cause, false⟩, none⟩),
  ("interruptible-finalizer-does-not-stop-skip",
    ⟨now, [interruptibleFinalizer, handler], true, some cause, false⟩, .contE, true,
    ⟨.empty, [interruptibleFinalizer, handler],
      [.popped interruptibleFinalizer, .ranContAll interruptibleFinalizer,
       .popped handler], ⟨now, [], true, some cause, false⟩, none⟩),
  ("already-masked-finalizer-pushes-nothing",
    ⟨now, [finalizer, handler], false, some cause, true⟩, .contE, true,
    ⟨.frame finalizer, [finalizer], [.popped finalizer, .ranContAll finalizer],
      ⟨now, [handler], false, some cause, true⟩, none⟩),
  ("duplicate-passed-frames-stay-ordered",
    ⟨now, [value, value, handler], false, none, false⟩, .contE, false,
    ⟨.frame handler, [value, value, handler],
      [.popped value, .popped value, .popped handler],
      ⟨now, [], false, none, false⟩, none⟩),
  ("non-frame-thunk-is-passed-not-executed",
    ⟨now, [.sync 149, value, handler], false, none, false⟩, .contA, false,
    ⟨.frame value, [.sync 149, value], [.popped (.sync 149), .popped value],
      ⟨now, [handler], false, none, false⟩, none⟩),
  ("model-contAll-finalizer",
    ⟨now, [finalizer, handler], true, none, false⟩, .contAll, true,
    ⟨.frame finalizer, [finalizer], [.popped finalizer, .ranContAll finalizer],
      ⟨now, [.setInterruptible true, handler], false, none, false⟩, none⟩),
  ("model-contAll-mask",
    ⟨now, [.setInterruptible false, handler], true, some cause, false⟩,
    .contAll, true,
    ⟨.frame (.setInterruptible false), [.setInterruptible false],
      [.popped (.setInterruptible false), .ranContAll (.setInterruptible false)],
      ⟨now, [handler], false, some cause, false⟩, none⟩)
]

def entryCases : List (String × F × Arm × Bool × R) := [
  ("plain-entry-finalizer", ⟨now, [finalizer, handler], true, some cause, false⟩,
    .contE, true,
    ⟨.frame finalizer, [finalizer], [.popped finalizer, .ranContAll finalizer],
      ⟨now, [.setInterruptible true, handler], false, some cause, false⟩, none⟩),
  ("deferred-value-keeps-entire-stack", ⟨now, [value, handler], true, some cause, true⟩,
    .contA, false,
    ⟨.deferred cause, [], [.deferred cause],
      ⟨now, [value, handler], true, some cause, false⟩, none⟩),
  ("deferred-failure-no-skip", ⟨now, [handler], true, some cause, true⟩,
    .contE, false,
    ⟨.deferred cause, [], [.deferred cause], ⟨now, [handler], true, some cause, false⟩, none⟩),
  ("masked-deferred-failure-is-not-discarded", ⟨now, [handler], false, some cause, true⟩,
    .contE, true,
    ⟨.deferred cause, [], [.deferred cause], ⟨now, [handler], false, some cause, false⟩, none⟩),
  ("deferred-without-cause-is-total-model-state", ⟨now, [handler], true, none, true⟩,
    .contE, true,
    ⟨.deferred Cause.empty, [], [.deferred Cause.empty], ⟨now, [handler], true, none, false⟩, none⟩),
  ("discarded-deferred-event-precedes-pop",
    ⟨now, [.setInterruptible false, handler], true, some cause, true⟩, .contE, true,
    ⟨.frame handler, [.setInterruptible false, handler],
      [.deferred cause, .popped (.setInterruptible false),
       .ranContAll (.setInterruptible false), .popped handler],
      ⟨now, [], false, some cause, false⟩, none⟩),
  ("discarded-deferred-event-survives-empty-stack", ⟨now, [], true, some cause, true⟩,
    .contE, true,
    ⟨.empty, [], [.deferred cause], ⟨now, [], true, some cause, false⟩, none⟩),
  ("empty-unmasked-no-pending", ⟨now, [], true, none, false⟩, .contE, true,
    ⟨.empty, [], [], ⟨now, [], true, none, false⟩, none⟩),
  ("model-contAll-deferred-before-mask",
    ⟨now, [.setInterruptible false, handler], false, some cause, true⟩,
    .contAll, true,
    ⟨.deferred cause, [], [.deferred cause],
      ⟨now, [.setInterruptible false, handler], false, some cause, false⟩, none⟩)
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

end Test.Runtime.LiveStackContract
