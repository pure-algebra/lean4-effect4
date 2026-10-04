import Effect4.Laws.Program.Signature

/-!
Finite record typing refusal controls. These examples check field names, nested term addresses,
first-failure order and successful neighbors. The general acceptance statement remains `toOption_term?`.
-/

namespace Test.Program.RecordRefusals

open Effect4.Program

def fields : Record.Fields := [("name", false, .string), ("nickname", true, .string)]
def declared : Ty := .record fields

def run (term : Term) (env : TyEnv := []) : Except TypeRefusal Ty :=
  Checker.term? (nativeSignature []) env [2, 1] term

def error (reason : RecordTypingReason) (path : List Nat := []) : Except TypeRefusal Ty :=
  .error ⟨[2, 1], .recordTerm ⟨path, reason⟩⟩

def missing : Term := .record fields [] .nil

#guard run (.record [("name", false, .string), ("name", true, .nat)] [] .nil) =
  error (.duplicateDeclaration "name")
#guard run (.record fields ["name", "name"]
    (.cons (.lit (.str "Ada")) (.cons (.lit (.str "Grace")) .nil))) =
  error (.duplicateSupplied "name")
#guard run missing = error (.missingRequired "name")
#guard run (.record fields ["other"] (.cons (.lit (.str "Ada")) .nil)) =
  error (.unknownSupplied "other")
#guard run (.record fields ["name"] (.cons (.lit (.bool true)) .nil)) =
  error (.fieldNotSubtype "name" .bool .string)
#guard run (.record fields ["name"] .nil) = error (.columnLengths 1 0)
#guard run (.record fields [] (.cons (.lit (.str "Ada")) .nil)) =
  error (.columnLengths 0 1)

#guard run (.field .required (.var 0) "nickname") [declared] =
  error (.optionalReadField "nickname" declared.normalize)
#guard run (.field .required (.var 0) "other") [declared] =
  error (.missingReadField "other" declared.normalize)
#guard run (.field .optional (.var 0) "other") [declared] =
  error (.missingReadField "other" declared.normalize)

-- The node path remains [2, 1]; the nested address belongs to the term.
#guard run (.app "some" (.cons missing .nil)) = error (.missingRequired "name") [0]
#guard run (.field .required missing "name") = error (.missingRequired "name") [0]
#guard run (.recordSet (.var 0) "child" missing) [declared] =
  error (.missingRequired "name") [1]
#guard run (.recordSet missing "child" (.var 5)) = error (.missingRequired "name") [0]

def genericFirst : Term := .app "pair" (.cons (.var 5) (.cons missing .nil))
#guard run genericFirst = .error ⟨[2, 1], .term genericFirst⟩

-- The caller computes a record-specific reason only after the existing rule refuses.
#guard run (.record fields ["name"] (.cons (.lit (.str "Ada")) .nil)) =
  .ok declared.normalize
#guard run (.field .required (.var 0) "name") [declared] = .ok .string
#guard run (.field .optional (.var 0) "nickname") [declared] = .ok (.option .string)
#guard run (.record [("_tag", false, .lit "User")] ["_tag"]
    (.cons (.lit (.str "User")) .nil)) = .ok (.record [("_tag", false, .lit "User")])
#guard run (.record [("_tag", false, .lit "User")] ["_tag"] (.cons (.var 0) .nil)) [.string] =
  error (.fieldNotSubtype "_tag" .string (.lit "User"))

#guard match run (.record [("bad", true, .map .nat .nat)] [] .nil) with
  | .error ⟨[2, 1], .recordTerm ⟨[], .declarationFormation why⟩⟩ => why.ty = .map .nat .nat
  | _ => false

-- Cause and term addresses remain distinct, including nested `both` nodes.
def runCause (cause : CauseTerm) : Except TypeRefusal EffTy :=
  Checker.check (nativeSignature []) [] [2, 1] (.failCause cause)

#guard runCause (.die missing) =
  .error ⟨[2, 1], .recordCause ⟨[], ⟨[], .missingRequired "name"⟩⟩⟩
#guard runCause (.both (.interrupt none) (.die (.app "some" (.cons missing .nil)))) =
  .error ⟨[2, 1], .recordCause ⟨[1], ⟨[0], .missingRequired "name"⟩⟩⟩
#guard runCause (.both (.both (.interrupt none) (.fail missing)) (.die (.var 5))) =
  .error ⟨[2, 1], .recordCause ⟨[0, 1], ⟨[], .missingRequired "name"⟩⟩⟩
#guard runCause (.interrupt (some missing)) =
  .error ⟨[2, 1], .recordCause ⟨[], ⟨[], .missingRequired "name"⟩⟩⟩

def genericCause : CauseTerm := .both (.die (.var 5)) (.fail missing)
#guard runCause genericCause = .error ⟨[2, 1], .cause genericCause⟩
#guard runCause (.interrupt (some (.lit (.str "not a fiber id")))) =
  .error ⟨[2, 1], .cause (.interrupt (some (.lit (.str "not a fiber id"))))⟩
#guard runCause (.interrupt none) = .ok ⟨.never, .never, Effect4.Machine.Env.Requirement.empty⟩

example {Op : Type} (sig : Signature Op) (env : TyEnv) (path : List Nat) (term : Term) :
    (Checker.term? sig env path term).toOption = termTy sig env term :=
  Checker.toOption_term? sig env path term

#print axioms Checker.toOption_term?
#print axioms Checker.term?_eq_ok
#print axioms Checker.toOption_cause?
#print axioms Checker.cause?_eq_ok
#print axioms termRefusal_ext
#print axioms cause?_ext
#print axioms term?_ext

end Test.Program.RecordRefusals
