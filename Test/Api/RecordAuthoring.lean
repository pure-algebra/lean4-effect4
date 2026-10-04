import Effect4.Api

/-! Application-facing record examples using the ordinary API import.
These finite checks cover named composition, optional presence and immutable overwrite.
They establish no general target execution or host-session property. -/

namespace Effect4.Test.RecordAuthoring
open Effect4.Program

def person : Authoring.TermSrc :=
  Authoring.record [("name", false, .string), ("nickname", true, .string)]
    [("name", Authoring.str "Ada")]

def nickname : Authoring.Src NativeOp :=
  Authoring.bind "person" (Authoring.succeed person)
    (Authoring.succeed (Authoring.optionalField (Authoring.var "person") "nickname"))

def changed : Authoring.Src NativeOp :=
  Authoring.bind "person" (Authoring.succeed person)
    (Authoring.bind "updated"
      (Authoring.succeed (Authoring.recordSet (Authoring.var "person") "nickname" (Authoring.str "Countess")))
      (Authoring.succeed (Authoring.field (Authoring.var "updated") "nickname")))

def original : Authoring.Src NativeOp :=
  Authoring.bind "person" (Authoring.succeed person)
    (Authoring.bind "updated"
      (Authoring.succeed (Authoring.recordSet (Authoring.var "person") "nickname" (Authoring.str "Countess")))
      (Authoring.succeed (Authoring.optionalField (Authoring.var "person") "nickname")))

#guard (Effect4.Api.author nickname).map (fun p => p.ty.answer) = .ok (.option .string)
#guard (Effect4.Api.author changed).map (fun p => p.ty.answer) = .ok (.lit "Countess")
#guard match Effect4.Api.author nickname with
  | .ok p => p.runSync == .success .none && p.print.isOk
  | .error _ => false
#guard match Effect4.Api.author changed with
  | .ok p => p.runSync == .success (.str "Countess") && p.print.isOk
  | .error _ => false
#guard match Effect4.Api.author original with
  | .ok p => p.runSync == .success .none
  | .error _ => false

end Effect4.Test.RecordAuthoring
