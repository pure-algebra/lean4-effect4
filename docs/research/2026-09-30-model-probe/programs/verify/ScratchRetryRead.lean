import Effect4.Api.Author
import Effect4.Program.Authoring.Loops

/-! Verifier scratch: what printing does to the seat's retry form (located for
`VerifyPrograms.lean` §1). -/
set_option autoImplicit false
set_option maxRecDepth 8192
namespace Verify.RetryRead
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Authoring

def retryForm (attempt : Src NativeOp) (retryable : TermSrc → TermSrc) (times base : Nat)
    (answerTy errorTy : Ty) : Src NativeOp :=
  let cursorTy : Ty := .prod .nat (.prod .nat (.prod (.option answerTy) (.option errorTy)))
  bindName "retry.last"
    (iterateWith (app "pair" [nat 0, app "pair" [nat base, app "pair" [app "none" [], app "none" []]]])
      { cursorTy := some cursorTy
        while_ := fun c =>
          app "and" [app "not" [app "isSome" [app "fst" [app "snd" [app "snd" [c]]]]],
            app "or" [app "eq" [app "fst" [c], nat 0],
              app "lt" [app "fst" [c], nat (times + 1)]]]
        body := fun c => eff do
          let _ ← ifElse (app "lt" [nat 0, app "fst" [c]])
            (Effect.sleep (app "fst" [app "snd" [c]])) (succeed unit)
          catchIf "retry.error" (retryable (var "retry.error"))
            (bindName "retry.answer" attempt fun a =>
              succeed (app "pair" [app "some" [a], app "none" []]))
            (succeed (app "pair" [app "none" [], app "some" [var "retry.error"]]))
        step := fun c last =>
          app "pair" [app "succ" [app "fst" [c]],
            app "pair" [app "mul" [app "fst" [app "snd" [c]], nat 2], last]]
        result := fun c => app "snd" [app "snd" [c]] })
    fun last =>
      selectOption "retry.ok" (app "fst" [last])
        (selectOption "retry.err" (app "snd" [last])
          (failCause (Cause.die (str "retry: no attempt ran")))
          (fail (var "retry.err")))
        (succeed (var "retry.ok"))

def retryAlone : Option Effect4.Api.Program :=
  (elaborate (retryForm (succeed (str "ok")) (fun _ => bool true) 3 100 .string .string)).toOption

-- typed before printing
#eval (retryAlone.bind (Effect4.Api.typeOf ·)).isSome
-- does the round trip succeed, and does its result type?
#eval retryAlone.map fun p => match Effect4.Api.roundTrip p with
  | .ok q => s!"read back; typed: {(Effect4.Api.typeOf q).isSome}; equal: {decide (q = p)}"
  | .error (.unknownHead n) => s!"refused: unknownHead {n}"
  | .error (.unknownIdent n) => s!"refused: unknownIdent {n}"
  | .error (.arity n) => s!"refused: arity {n}"
  | .error (.binder n) => s!"refused: binder {n}"
  | .error (.shape n) => s!"refused: shape {n}"
  | .error (.negative _) => "refused: negative"
  | .error .unsupportedStmt => "refused: unsupportedStmt"
  | .error (.annotation n) => s!"refused: annotation {n}"
-- the explain of the read-back program
#eval retryAlone.bind fun p => match Effect4.Api.roundTrip p with
  | .ok q => (Effect4.Api.explain q).map (fun r => r.reason.head)
  | .error _ => none
end Verify.RetryRead
