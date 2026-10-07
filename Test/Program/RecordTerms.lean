import Effect4.Program.Admission

/-! Finite controls for the record term signature in decisions row 195.
The controls check raw evaluation, stored modes, variable weakening and term typing.
They establish no target execution claim. -/

namespace Effect4.Test.RecordTerms
open Effect4.Program Effect4.Machine

def personFields : List (String × Bool × Ty) :=
  [("name", false, .string), ("nickname", true, .string)]

def person : Term := .record personFields ["name"] (.cons (.lit (.str "Ada")) .nil)

#guard evalTerm [] person = some (Record.frame [("name", .str "Ada")])
#guard evalTerm [] (.field .required person "name") = some (.str "Ada")
#guard evalTerm [] (.field .optional person "name") = some (Store.Val.some (.str "Ada"))
#guard evalTerm [] (.field .optional person "nickname") = some Store.Val.none
#guard evalTerm [] (.field .required person "nickname") = none
#guard evalTerm [] (.record [] ["z", "a"]
  (.cons (.lit (.nat 7)) (.cons (.lit (.str "Ada")) .nil))) =
  some (Record.frame [("a", .str "Ada"), ("z", .nat 7)])
#guard evalTerm [] (.record [] ["name"] .nil) = none
#guard evalTerm [] (.record [] ["name", "name"]
  (.cons (.lit (.nat 1)) (.cons (.lit (.nat 2)) .nil))) = none
#guard evalTerm [] (.record [] [] (.cons (.lit .unit) .nil)) = none
#guard evalTerm [] (.recordSet person "nickname" (.lit (.str "A"))) =
  some (Record.frame [("name", .str "Ada"), ("nickname", .str "A")])
#guard evalTerm [] (.recordSet person "name" (.lit (.nat 4))) =
  some (Record.frame [("name", .nat 4)])
#guard evalTerm [Record.frame [("nickname", Store.Val.none)]]
  (.field .optional (.var 0) "nickname") = some (Store.Val.some Store.Val.none)
#guard evalTerm [Record.frame [("nickname", .unit)]]
  (.field .optional (.var 0) "nickname") = some (Store.Val.some .unit)

#guard person.scoped 0
#guard !(Term.record personFields ["name"] (.cons (.var 0) .nil)).scoped 0
#guard (Term.field .optional (.var 0) "name").scoped 1
#guard !(Term.recordSet (.var 0) "name" (.var 1)).scoped 1
#guard Term.weaken 0 (.record personFields ["name"] (.cons (.var 0) .nil)) =
  .record personFields ["name"] (.cons (.var 1) .nil)
#guard Term.weaken 1 (.recordSet (.var 0) "name" (.field .optional (.var 1) "nickname")) =
  .recordSet (.var 0) "name" (.field .optional (.var 2) "nickname")

-- The declaration retains absent optional fields and direct literal tags.
#guard termTy (nativeSignature []) [] person = some (Ty.record personFields).normalize
#guard termTy (nativeSignature []) [] (.record personFields [] .nil) = none
#guard termTy (nativeSignature []) [] (.record personFields ["other"] (.cons (.lit .unit) .nil)) = none
#guard termTy (nativeSignature []) [] (.record personFields ["name", "name"]
  (.cons (.lit (.str "Ada")) (.cons (.lit (.str "A")) .nil))) = none
#guard termTy (nativeSignature []) [] (.record personFields ["name"] .nil) = none
#guard termTy (nativeSignature []) [] (.record personFields ["name"] (.cons (.lit (.nat 1)) .nil)) = none
#guard termTy (nativeSignature []) []
  (.record [("x", true, .nat), ("x", true, .nat)] [] .nil) = none
#guard termTy (nativeSignature []) []
  (.record [("x", true, .map .nat .string)] [] .nil) = none
#guard termTy (nativeSignature []) [] (.record [("_tag", false, .lit "Found")]
  ["_tag"] (.cons (.lit (.str "Found")) .nil)) = some (.record [("_tag", false, .lit "Found")])
#guard termTy (nativeSignature []) [.string] (.record [("_tag", false, .lit "Found")]
  ["_tag"] (.cons (.var 0) .nil)) = none

#guard termTy (nativeSignature []) [] (.field .required person "name") = some .string
#guard termTy (nativeSignature []) [] (.field .required person "nickname") = none
#guard termTy (nativeSignature []) [] (.field .optional person "nickname") = some (.option .string)
#guard termTy (nativeSignature []) [.record [("x", true, .option .nat)]]
  (.field .optional (.var 0) "x") = some (.option (.option .nat))
#guard termTy (nativeSignature []) [.union (.record [("x", false, .nat)])
  (.record [("x", false, .string)])] (.field .required (.var 0) "x") = some (Ty.join .nat .string)
#guard termTy (nativeSignature []) [.union (.record [("x", false, .nat)]) .nat]
  (.field .required (.var 0) "x") = none
#guard termTy (nativeSignature []) [] (.recordSet person "nickname" (.lit (.nat 4))) =
  some (.record [("name", false, .string), ("nickname", false, .nat)])
#guard termTy (nativeSignature []) [] (.recordSet person "name" (.lit (.str "Grace"))) =
  some (.record [("name", false, .lit "Grace"), ("nickname", true, .string)])
#guard argTy (nativeSignature []) [] true person = argTy (nativeSignature []) [] false person

-- An integer field is admitted (decisions row 317), even after its value is discarded.
def intRecord : Term := .record [("n", false, .int)] ["n"] (.cons (.lit (.nat 1)) .nil)
def discardInt : NativeEff := .bind (.succeed intRecord) (.succeed (.lit (.nat 0)))
#guard (admitProgram discardInt).isOk

-- Generated program views reach terms in every type-bearing leaf position.
def badMetadata : Term := .record [("x", true, .map .nat .string)] [] .nil
#guard (Formation.checkInput (.succeed badMetadata : NativeEff) []).isSome
#guard (Formation.checkInput (.failCause (.die badMetadata) : NativeEff) []).isSome
#guard (Formation.checkInput (.gen (.cons (.ret badMetadata) .nil) : NativeEff) []).isSome
#guard (Formation.checkInput (.withFiber (.interruptAll (.lit .unit) (some badMetadata)) : NativeEff) []).isSome
#guard (Formation.checkInput (.provideLayer (.effect ⟨⟨0⟩, ⟨0⟩⟩ (.succeed badMetadata)) false
  (.succeed (.lit .unit)) : NativeEff) []).isSome
#guard (Formation.checkInput (.succeed (.app "some" (.cons badMetadata .nil)) : NativeEff) []).isSome

end Effect4.Test.RecordTerms
