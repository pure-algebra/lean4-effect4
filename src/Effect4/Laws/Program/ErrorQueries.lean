import Effect4.Program.ErrorQueries
import Effect4.Program.Typed

/-!
# Error query laws (DI-09)

These statements concern the native cause/exit image and its allocation-aware membership.
They do not establish the TypeScript adapter contract. Selection uses Reason.error? first,
then the closed partial error image; no later error can replace a selected boom.
-/

set_option autoImplicit false

namespace Effect4.Program
open Effect4 Effect4.Machine

/-- The selected error occurs before every other Fail that could be selected. -/
theorem firstFailure?_eq_some_iff (cause : CauseV) (error : Err) :
    firstFailure? cause = some error ↔
      ∃ before reason after, cause.reasons = before ++ reason :: after ∧
        reason.error? = some error ∧ ∀ previous ∈ before, previous.error? = none :=
  List.findSome?_eq_some_iff

theorem firstFailure?_head (error : Err) (annotations : ReasonAnnotations Ann)
    (tail : List (Reason Err Defect FiberId Ann)) :
    firstFailure? ⟨.fail error annotations :: tail⟩ = some error := rfl

theorem firstErrorValue?_boom (annotations : ReasonAnnotations Ann)
    (tail : List (Reason Err Defect FiberId Ann)) :
    firstErrorValue? ⟨.fail .boom annotations :: tail⟩ = none := rfl

theorem queryReasons?_exitErr (cause : CauseV) :
    queryReasons? (Val.exitErr cause) = some cause.reasons := by
  change (Val.cause? (Val.exitErr cause)).map Cause.reasons = _
  rw [Val.cause?_exitErr]
  rfl

theorem queryReasons?_exitOk (value : Val) : queryReasons? (Val.exitOk value) = some [] := rfl

/-- Successful extraction belongs to the declared error type at the same allocation. -/
theorem firstErrorValue?_typed (cause : CauseV) (error : Ty) (allocated : List String)
    (value : Val)
    (hadmits : causeAdmits (fun v _ => Val.hasTy v error allocated) error cause = true)
    (hextract : firstErrorValue? cause = some value) :
    Val.hasTy value error allocated = true := by
  obtain ⟨selected, hselected, hvalue⟩ := Option.bind_eq_some_iff.mp hextract
  obtain ⟨reason, hmem, hreason⟩ := List.exists_of_findSome?_eq_some hselected
  have hfit := List.all_eq_true.mp hadmits reason hmem
  cases reason with
  | fail actual annotations =>
    simp only [Reason.error?, Option.some.injEq] at hreason
    cases hreason
    simpa only [reasonAdmits, hvalue] using hfit
  | die defect annotations => cases hreason
  | interrupt fiber annotations => cases hreason

/-- Both advertised input families decode; only their typed failures contribute to E. -/
theorem queryReasons?_typed (value : Val) (input error : Ty) (allocated : List String)
    (hinput : causeInputError? input = some error)
    (hfit : Val.hasTy value input allocated = true) :
    ∃ reasons, queryReasons? value = some reasons ∧
      reasons.all (reasonAdmits (fun v _ => Val.hasTy v error allocated) error) = true := by
  unfold causeInputError? at hinput
  split at hinput
  · cases hinput
    change (match Val.cause? value with
      | some c => causeAdmits (fun v _ => Val.hasTy v error allocated) error c
      | none => false) = true at hfit
    cases hc : Val.cause? value with
    | none => simp only [hc, Bool.false_eq_true] at hfit
    | some cause =>
      have hv := Val.cause?_exact hc
      subst value
      exact ⟨cause.reasons, queryReasons?_exitErr cause,
        by simpa only [Val.cause?_exitErr, causeAdmits] using hfit⟩
  · cases hinput
    unfold Val.hasTy at hfit
    split at hfit
    · exact ⟨[], rfl, rfl⟩
    · next written =>
      cases hc : causeImage.ofVal written with
      | none => simp only [hc, Bool.false_eq_true] at hfit
      | some cause =>
        refine ⟨cause.reasons, ?_, ?_⟩
        · change (causeImage.ofVal written).map Cause.reasons = _
          rw [hc]
          rfl
        · simpa only [hc, causeAdmits] using hfit
    · cases hfit
  all_goals cases hinput

theorem queryTag_typed (tag : ReasonTag) (value : Val) (input error : Ty)
    (allocated : List String) (hinput : causeInputError? input = some error)
    (hfit : Val.hasTy value input allocated = true) :
    ∃ answer, queryTag tag value = some answer ∧ Val.hasTy answer .bool allocated = true := by
  obtain ⟨reasons, hquery, _⟩ := queryReasons?_typed value input error allocated hinput hfit
  refine ⟨Val.bool (reasons.any fun reason => decide (reason.tag = tag)), ?_, rfl⟩
  simp only [queryTag, hquery, Option.map_some]

theorem queryError_typed (value : Val) (input error : Ty) (allocated : List String)
    (hinput : causeInputError? input = some error)
    (hfit : Val.hasTy value input allocated = true) :
    ∃ answer, queryError value = some answer ∧
      Val.hasTy answer (.option error) allocated = true := by
  obtain ⟨reasons, hquery, hadmits⟩ := queryReasons?_typed value input error allocated hinput hfit
  cases hfound : (reasons.findSome? Reason.error?).bind valOfErr with
  | none => exact ⟨.none, by simp [queryError, hquery, hfound], rfl⟩
  | some extracted =>
    refine ⟨.some extracted, ?_, ?_⟩
    · simp [queryError, hquery, hfound]
    · exact firstErrorValue?_typed ⟨reasons⟩ error allocated extracted hadmits hfound

end Effect4.Program
