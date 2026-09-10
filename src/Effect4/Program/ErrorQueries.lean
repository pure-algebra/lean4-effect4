import Effect4.Program.ErrorImage

/-!
# Error queries (DI-09)

DI-09's first-Fail selection uses the existing Reason.error? projection before converting
the selected Err. rc.112: vendor/effect-4.0.0-rc.112/src/internal/effect.ts:148,157-168,171,186. Cause values and failed
exits share Val.exitErr in the native image; successful exits have no reasons. This helper
does not reuse reasonsOfVal's list-flattening behavior for a scalar cause query.
-/

namespace Effect4.Program

open Effect4 Effect4.Machine

/-- First Fail including boom. Conversion must happen after this search. -/
def firstFailure? (cause : CauseV) : Option Err :=
  cause.reasons.findSome? Reason.error?

/-- The error binder/query payload. A first boom stays none even if a later Fail converts. -/
def firstErrorValue? (cause : CauseV) : Option Val :=
  (firstFailure? cause).bind valOfErr

/-- Scalar cause/exit query input. Invalid raw values are refused, not flattened. -/
def queryReasons? : Val → Option (List (Reason Err Defect FiberId Ann))
  | Val.exitOk _ => some []
  | value => (Val.cause? value).map Cause.reasons

/-- The two input families advertised by the query atoms. -/
def causeInputError? : Ty → Option Ty
  | .causeOf error | .exitOf _ error => some error
  | _ => none

def queryTag (tag : ReasonTag) (value : Val) : Option Val :=
  (queryReasons? value).map fun reasons =>
    Val.bool (reasons.any fun reason => decide (reason.tag = tag))

/-- Cause.findErrorOption with DI-09's documented boom boundary. -/
def queryError (value : Val) : Option Val := do
  let reasons ← queryReasons? value
  let found := (reasons.findSome? Reason.error?).bind valOfErr
  pure (match found with | none => .none | some error => .some error)

end Effect4.Program
