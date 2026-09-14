/-
Contract packet: `Test/contracts/cause-exit.contract.md`

Breaker-owned red battery. The implementation phase must not edit this file.
It is red until `src/Effect4/Machine/Cause.lean` and `src/Effect4/Machine/Exit.lean`
declare the frozen surface.

Until 2026-09-13 every public declaration was also frozen here by a hand-typed
`#check (@name : proposition)` copy of its statement; those copies were retired, since a
statement lives in its theorem and its change is that file's diff. What remains is what
only this battery says: the guards over named programs and the counterexample theorems.
-/

import Effect4.Machine.Cause
import Effect4.Machine.Exit

set_option autoImplicit false

namespace Effect4
end Effect4

namespace Test.Semantics.CauseExitContract

open Effect4

universe u

section AnnotationSurface

/-! A1: the finite per-reason annotation map (census: cause.annotations). -/

example {α : Type u} [DecidableEq α] : DecidableEq (ReasonAnnotations α) :=
  inferInstance

/-! The exact merge shape: kept position, in-place overwrite, appended tail. -/

/-! Insertion order is retained, so annotation equality is not extensional. -/

/-! The WeakMap host-identity memory is refused, not modelled. -/

end AnnotationSurface

section ReasonSurface

/-! A2: the closed three-value reason alphabet (census: exit.reason-alphabet). -/

#synth DecidableEq ReasonTag
#synth Repr ReasonTag

/-! A3: reasons carry payload and annotations, and nothing else. -/

example {ε δ ι α : Type u} [DecidableEq ε] [DecidableEq δ] [DecidableEq ι]
    [DecidableEq α] : DecidableEq (Reason ε δ ι α) :=
  inferInstance

/-! Reason equality compares tag, payload, and annotations. -/

end ReasonSurface

section CauseSurface

/-! A4: a cause is exactly an ordered reason list (census: cause.flat-reasons,
rule.cause-has-no-structure). -/

example {ε δ ι α : Type u} [DecidableEq ε] [DecidableEq δ] [DecidableEq ι]
    [DecidableEq α] : DecidableEq (Cause ε δ ι α) :=
  inferInstance

/-! rc.112 `CauseImpl` equality: same length and pairwise-equal ordered reasons. -/

/-! A5: first-occurrence deduplication, the `Arr.union` kernel. -/

/-! A5b: `hasInterrupts` (census: cause.reason-interrupt).

rc.112's `internal/effect.ts:186`, `self.reasons.some(isInterruptReason)`. It is
the predicate `AsyncFinalizer[contE]` reads before deciding whether to run its
cancel effect. -/

/-! A6: `causeCombine` (census: cause.combine-union,
rule.cause-has-no-structure). -/

/-! The definition-level union law for two nonempty causes. -/
/-! No sequential or parallel node: combine introduces no new reason. -/
/-! `Arr.union` order: `self`, then the elements of `that` not already present. -/
/-! The structural-equality short circuit. -/

end CauseSurface

section SquashSurface

/-! A7: `causeSquash` has four arms (census: cause.squash). -/

example {ε δ : Type u} [DecidableEq ε] [DecidableEq δ] :
    DecidableEq (Squashed ε δ) :=
  inferInstance

/-! Arm one: the first `Fail` error in reason order. -/
/-! Arm two: with no `Fail`, the first `Die` defect in reason order. -/
/-! Arm three: "All fibers interrupted without error". -/
/-! Arm four: "Empty cause". -/

/-! First-occurrence order: a later `Fail` still beats an earlier `Die`. -/

end SquashSurface

section ExitSurface

/-! A8: exits (census: exit.success-failure, cause.finalizer-merge,
scope.exit-as-void-all). -/

example {β ε δ ι α : Type u} [DecidableEq β] [DecidableEq ε] [DecidableEq δ]
    [DecidableEq ι] [DecidableEq α] : DecidableEq (Exit β ε δ ι α) :=
  inferInstance

/-! `combineFinalizerCause`, exactly as pinned at internal/effect.ts:3800-3804. -/

/-! Under a successful exit the finalizer failure stands alone. -/
/-! `catchCause` does not intercept a successful finalizer. -/
/-! A finalizer failure under a failed exit is merged by `causeCombine`. -/

/-! The caller-side restore at internal/effect.ts:4023-4028. -/

/-! `exitAsVoidAll`, exactly as pinned at internal/effect.ts:2024-2038. -/

/-! The exact concatenation order: failed exits' reasons, in list order. -/
/-! A failed exit with an empty cause contributes nothing, so the join succeeds. -/
/-! `exitAsVoidAll` concatenates; unlike `causeCombine` it does not deduplicate. -/

end ExitSurface

section GroundChecks

/-! Small executable checks over closed alphabets. They are finite probes, not
laws; each law above is separately frozen. -/

abbrev Err := Nat
abbrev Defect := Bool
abbrev Interruptor := Nat
abbrev Ann := Nat

abbrev GroundReason := Reason Err Defect Interruptor Ann
abbrev GroundCause := Cause Err Defect Interruptor Ann
abbrev GroundExit := Exit Unit Err Defect Interruptor Ann

def firstFail : GroundReason := Reason.fail 1 ReasonAnnotations.empty
def secondFail : GroundReason := Reason.fail 2 ReasonAnnotations.empty
def someDie : GroundReason := Reason.die true ReasonAnnotations.empty

def leftCause : GroundCause := Cause.mk [firstFail]
def rightCause : GroundCause := Cause.mk [secondFail]

/-! Combine deduplicates rather than appending. -/
example :
    Cause.combine leftCause (Cause.mk [firstFail, secondFail]) =
      Cause.mk [firstFail, secondFail] := by
  decide

/-! Combine is idempotent on a duplicate-free cause. -/
example : Cause.combine leftCause leftCause = leftCause := by
  decide

/-! Combine retains operand order, so it is not commutative. -/
example : Cause.combine leftCause rightCause ≠
    Cause.combine rightCause leftCause := by
  decide

/-! An earlier `Die` does not beat a later `Fail`. -/
example : (Cause.mk [someDie, firstFail] : GroundCause).squash =
    Squashed.error 1 := by
  decide

/-! A failed exit carrying an empty cause joins to success. -/
example :
    Exit.asVoidAll [(Exit.failure Cause.empty : GroundExit)] =
      Exit.success () := by
  decide

/-! The join concatenates and keeps duplicates. -/
example :
    Exit.asVoidAll
        [(Exit.failure (Cause.mk [firstFail]) : GroundExit),
          Exit.failure (Cause.mk [firstFail])] =
      Exit.failure (Cause.mk [firstFail, firstFail]) := by
  decide

/-! A finalizer failure under a successful exit stands alone. -/
example :
    Exit.mergeFinalizer (Exit.success () : GroundExit)
        (Exit.failure rightCause) =
      Exit.failure rightCause := by
  decide

/-! A finalizer failure under a failed exit is unioned into the exit cause. -/
example :
    Exit.mergeFinalizer (Exit.failure leftCause : GroundExit)
        (Exit.failure rightCause) =
      Exit.failure (Cause.mk [firstFail, secondFail]) := by
  decide

def keptAnnotations : ReasonAnnotations Ann :=
  ReasonAnnotations.mk [("effect/Cause/StackTrace", 1)] (by decide)

def replacementAnnotations : ReasonAnnotations Ann :=
  ReasonAnnotations.mk [("effect/Cause/StackTrace", 2)] (by decide)

/-! `annotate` never overwrites an existing key unless asked. -/
example :
    (keptAnnotations.annotate replacementAnnotations false).lookup
        "effect/Cause/StackTrace" = some 1 := by
  decide

/-! With `overwrite := true` the new value replaces the old one in place. -/
example :
    (keptAnnotations.annotate replacementAnnotations true).entries =
      [("effect/Cause/StackTrace", 2)] := by
  decide

/-! Annotating with the empty map is the identity. -/
example : keptAnnotations.annotate ReasonAnnotations.empty true = keptAnnotations := by
  decide

end GroundChecks

section AxiomReceipts

#print axioms Effect4.ReasonAnnotations.keys_eq
#print axioms Effect4.ReasonAnnotations.annotate_entries
#print axioms Effect4.ReasonAnnotations.lookup_annotate_kept
#print axioms Effect4.ReasonAnnotations.order_retained
#print axioms Effect4.Reason.host_memory_refused
#print axioms Effect4.Reason.cases_receipt
#print axioms Effect4.Cause.eq_iff_pointwise
#print axioms Effect4.Cause.combine_order
#print axioms Effect4.Cause.combine_self
#print axioms Effect4.Cause.squash_error
#print axioms Effect4.Cause.squash_emptyCause_iff
#print axioms Effect4.Exit.mergeFinalizer_failure_failure
#print axioms Effect4.Exit.asVoidAll_reasons

end AxiomReceipts

end Test.Semantics.CauseExitContract
