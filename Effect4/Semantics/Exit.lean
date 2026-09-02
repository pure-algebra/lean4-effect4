import Effect4.Semantics.Cause

/-!
# Semantics.Exit.lean

Owner: Success and cause-indexed exits.

This module freezes the first-order `Exit` model of `effect@4.0.0-rc.112`: the
two-constructor success-or-failure alphabet over the exit value and the four
cause alphabets, the void exit, the success and cause observations, the
`combineFinalizerCause` merge, the caller-side exit restore, and the
`exitAsVoidAll` join. It imports only `Effect4.Semantics.Cause`.

Pinned source: `vendor/effect-4.0.0-rc.112/src/internal/effect.ts` 2024-2038,
3800-3804, and 4023-4028. The frozen surface is
`test/contracts/cause-exit.contract.md`, held by the battery
`Effect4Test/Semantics/CauseExitContract.lean` and the axiom report
`Effect4Test/Semantics/CauseExitAxiomReport.lean`.
-/

namespace Effect4

universe u v

/-- A finished computation: a value, or the cause it failed with. -/
inductive Exit (β : Type v) (ε δ ι α : Type u)
  /-- The computation produced a value. -/
  | success (value : β)
  /-- The computation failed with a cause. -/
  | failure (cause : Cause ε δ ι α)
deriving DecidableEq

namespace Exit

/-- The successful exit carrying no information, rc.112's `exitVoid`. -/
def void {ε δ ι α : Type u} : Exit Unit ε δ ι α := success ()

/-- rc.112's `exitIsSuccess`. -/
def isSuccess {β : Type v} {ε δ ι α : Type u} : Exit β ε δ ι α -> Bool
  | success _ => true
  | failure _ => false

/-- The cause of a failed exit, if any. -/
def cause? {β : Type v} {ε δ ι α : Type u} : Exit β ε δ ι α -> Option (Cause ε δ ι α)
  | success _ => none
  | failure cause => some cause

/-- The reasons contributed by an exit: none from a success. -/
def causeReasons {β : Type v} {ε δ ι α : Type u} : Exit β ε δ ι α -> List (Reason ε δ ι α)
  | success _ => []
  | failure cause => cause.reasons

/-- rc.112's `combineFinalizerCause`, as an exit-to-exit function. -/
def mergeFinalizer {β : Type v} {ε δ ι α : Type u} [DecidableEq ε] [DecidableEq δ]
    [DecidableEq ι] [DecidableEq α] :
    Exit β ε δ ι α -> Exit Unit ε δ ι α -> Exit Unit ε δ ι α
  | success _, finalizer => finalizer
  | failure _, success value => success value
  | failure cause, failure finalizerCause =>
    failure (Cause.combine cause finalizerCause)

/-- The caller-side composite that restores the original exit. -/
def restoreAfterFinalizer {β : Type v} {ε δ ι α : Type u} [DecidableEq ε] [DecidableEq δ]
    [DecidableEq ι] [DecidableEq α] (self : Exit β ε δ ι α)
    (finalizer : Exit Unit ε δ ι α) : Exit β ε δ ι α :=
  match mergeFinalizer self finalizer with
  | success _ => self
  | failure cause => failure cause

/-- rc.112's `exitAsVoidAll`: concatenate the failed exits' reasons. -/
def asVoidAll {β : Type v} {ε δ ι α : Type u} (exits : List (Exit β ε δ ι α)) :
    Exit Unit ε δ ι α :=
  match exits.flatMap causeReasons with
  | [] => void
  | reason :: rest => failure (Cause.mk (reason :: rest))

/-- There is no third exit constructor. census: exit.success-failure -/
theorem cases_receipt {β : Type v} {ε δ ι α : Type u} (self : Exit β ε δ ι α) :
    (exists value, self = success value) \/ (exists cause, self = failure cause) := by
  cases self with
  | success value => exact Or.inl ⟨value, rfl⟩
  | failure cause => exact Or.inr ⟨cause, rfl⟩

/-- Success and failure are distinct. census: exit.success-failure -/
theorem success_ne_failure {β : Type v} {ε δ ι α : Type u} (value : β) (cause : Cause ε δ ι α) :
    (success value : Exit β ε δ ι α) ≠ failure cause := by
  intro h
  nomatch h

/-- Success equality is value equality. census: exit.success-failure -/
theorem success_inj {β : Type v} {ε δ ι α : Type u} (left right : β) :
    (success left : Exit β ε δ ι α) = success right <-> left = right := by
  constructor
  · intro h
    injection h
  · intro h
    rw [h]

/-- Failure equality is cause equality. census: exit.success-failure -/
theorem failure_inj {β : Type v} {ε δ ι α : Type u} (left right : Cause ε δ ι α) :
    (failure left : Exit β ε δ ι α) = failure right <-> left = right := by
  constructor
  · intro h
    injection h
  · intro h
    rw [h]

/-- The void exit is the successful unit exit. census: exit.success-failure -/
theorem void_eq {ε δ ι α : Type u} : (void : Exit Unit ε δ ι α) = success () := rfl

/-- A success reports success. census: exit.success-failure -/
theorem isSuccess_success {β : Type v} {ε δ ι α : Type u} (value : β) :
    (success value : Exit β ε δ ι α).isSuccess = true := rfl

/-- A failure reports failure. census: exit.success-failure -/
theorem isSuccess_failure {β : Type v} {ε δ ι α : Type u} (cause : Cause ε δ ι α) :
    (failure cause : Exit β ε δ ι α).isSuccess = false := rfl

/-- A success carries no cause. census: exit.success-failure -/
theorem cause_success {β : Type v} {ε δ ι α : Type u} (value : β) :
    (success value : Exit β ε δ ι α).cause? = none := rfl

/-- A failure carries its cause. census: exit.success-failure -/
theorem cause_failure {β : Type v} {ε δ ι α : Type u} (cause : Cause ε δ ι α) :
    (failure cause : Exit β ε δ ι α).cause? = some cause := rfl

/-- A success contributes no reason. census: scope.exit-as-void-all -/
theorem causeReasons_success {β : Type v} {ε δ ι α : Type u} (value : β) :
    (success value : Exit β ε δ ι α).causeReasons = [] := rfl

/-- A failure contributes its cause's reasons. census: scope.exit-as-void-all -/
theorem causeReasons_failure {β : Type v} {ε δ ι α : Type u} (cause : Cause ε δ ι α) :
    (failure cause : Exit β ε δ ι α).causeReasons = cause.reasons := rfl

/-- Under a successful exit the finalizer stands alone. census: cause.finalizer-merge -/
theorem mergeFinalizer_success {β : Type v} {ε δ ι α : Type u} [DecidableEq ε] [DecidableEq δ]
    [DecidableEq ι] [DecidableEq α] (value : β) (finalizer : Exit Unit ε δ ι α) :
    mergeFinalizer (success value) finalizer = finalizer := rfl

/-- A finalizer failure under a successful exit is the whole result.
census: cause.finalizer-merge -/
theorem mergeFinalizer_success_failure {β : Type v} {ε δ ι α : Type u} [DecidableEq ε]
    [DecidableEq δ] [DecidableEq ι] [DecidableEq α] (value : β)
    (finalizerCause : Cause ε δ ι α) :
    mergeFinalizer (success value) (failure finalizerCause) =
      failure finalizerCause := rfl

/-- `catchCause` does not intercept a successful finalizer.
census: cause.finalizer-merge -/
theorem mergeFinalizer_failure_success {β : Type v} {ε δ ι α : Type u} [DecidableEq ε]
    [DecidableEq δ] [DecidableEq ι] [DecidableEq α] (cause : Cause ε δ ι α)
    (value : Unit) :
    mergeFinalizer (failure cause : Exit β ε δ ι α) (success value) =
      success value := rfl

/-- A finalizer failure under a failed exit is merged by `causeCombine`.
census: cause.finalizer-merge -/
theorem mergeFinalizer_failure_failure {β : Type v} {ε δ ι α : Type u} [DecidableEq ε]
    [DecidableEq δ] [DecidableEq ι] [DecidableEq α]
    (cause finalizerCause : Cause ε δ ι α) :
    mergeFinalizer (failure cause : Exit β ε δ ι α) (failure finalizerCause) =
      failure (Cause.combine cause finalizerCause) := rfl

/-- A successful finalizer leaves the exit unchanged. census: cause.finalizer-merge -/
theorem restoreAfterFinalizer_success_finalizer {β : Type v} {ε δ ι α : Type u} [DecidableEq ε]
    [DecidableEq δ] [DecidableEq ι] [DecidableEq α] (self : Exit β ε δ ι α)
    (value : Unit) : restoreAfterFinalizer self (success value) = self := by
  cases self <;> rfl

/-- A failing finalizer under a failed exit short-circuits with the union.
census: cause.finalizer-merge -/
theorem restoreAfterFinalizer_failure_failure {β : Type v} {ε δ ι α : Type u} [DecidableEq ε]
    [DecidableEq δ] [DecidableEq ι] [DecidableEq α]
    (cause finalizerCause : Cause ε δ ι α) :
    restoreAfterFinalizer (failure cause : Exit β ε δ ι α) (failure finalizerCause) =
      failure (Cause.combine cause finalizerCause) := rfl

/-- A failing finalizer under a successful exit stands alone.
census: cause.finalizer-merge -/
theorem restoreAfterFinalizer_success_failure {β : Type v} {ε δ ι α : Type u} [DecidableEq ε]
    [DecidableEq δ] [DecidableEq ι] [DecidableEq α] (value : β)
    (finalizerCause : Cause ε δ ι α) :
    restoreAfterFinalizer (success value : Exit β ε δ ι α) (failure finalizerCause) =
      failure finalizerCause := rfl

/-- The join concatenates the failed exits' reasons in list order.
census: scope.exit-as-void-all -/
theorem asVoidAll_reasons {β : Type v} {ε δ ι α : Type u} (exits : List (Exit β ε δ ι α)) :
    (asVoidAll exits).causeReasons = exits.flatMap causeReasons := by
  unfold asVoidAll
  cases hflat : exits.flatMap causeReasons with
  | nil => rfl
  | cons reason rest => rfl

/-- The empty join succeeds. census: scope.exit-as-void-all -/
theorem asVoidAll_nil {β : Type v} {ε δ ι α : Type u} :
    asVoidAll ([] : List (Exit β ε δ ι α)) = success () := rfl

/-- A list of successes joins to success. census: scope.exit-as-void-all -/
theorem asVoidAll_all_success {β : Type v} {ε δ ι α : Type u} (exits : List (Exit β ε δ ι α))
    (h : forall exit, exit ∈ exits -> exists value, exit = success value) :
    asVoidAll exits = success () := by
  have hflat : forall list : List (Exit β ε δ ι α),
      (forall exit, exit ∈ list -> exists value, exit = success value) ->
      list.flatMap causeReasons = [] := by
    intro list
    induction list with
    | nil => intro _; rfl
    | cons head tail ih =>
      intro hall
      have ⟨value, hvalue⟩ := hall head List.mem_cons_self
      rw [List.flatMap_cons, hvalue,
        ih (fun exit hmem => hall exit (List.mem_cons_of_mem head hmem))]
      rfl
  unfold asVoidAll
  rw [hflat exits h]
  rfl

/-- A nonempty reason concatenation joins to that exact cause.
census: scope.exit-as-void-all -/
theorem asVoidAll_failure {β : Type v} {ε δ ι α : Type u} (exits : List (Exit β ε δ ι α))
    (reason : Reason ε δ ι α) (rest : List (Reason ε δ ι α))
    (h : exits.flatMap causeReasons = reason :: rest) :
    asVoidAll exits = failure (Cause.mk (reason :: rest)) := by
  unfold asVoidAll
  rw [h]

/-- A failed exit with an empty cause contributes nothing.
census: scope.exit-as-void-all -/
theorem asVoidAll_empty_cause {ε δ ι α : Type u} :
    asVoidAll [(failure Cause.empty : Exit Unit ε δ ι α)] = success () := rfl

/-- The join concatenates without deduplicating. census: scope.exit-as-void-all -/
theorem asVoidAll_keeps_duplicates {ε δ ι α : Type u} (reason : Reason ε δ ι α) :
    asVoidAll [(failure (Cause.mk [reason]) : Exit Unit ε δ ι α),
        failure (Cause.mk [reason])] =
      failure (Cause.mk [reason, reason]) := rfl

end Exit

end Effect4
