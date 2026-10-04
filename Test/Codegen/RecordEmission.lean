import Effect4.Api

/-! Finite controls for checked record declaration production and source admission.
These controls serve `printed-modules` under Exact Codecs and Embeddings, for decisions row 195.
The host supplies lexical bindings. These checks establish no target execution claim. -/

namespace Effect4.Test.RecordEmission
open Effect4.Program Effect4.Codegen

def person : Term := .record [("id", false, .nat), ("nickname", true, .string)]
  ["id"] (.cons (.lit (.nat 1)) .nil)

def program : NativeEff := .succeed (.field .optional person "nickname")

def origins : List Bindings.Origin :=
  effectOrigins ++ Effect4.Codegen.Record.helperNames.map (fun name => .imported "./records" (some name))

def ambient : List TypeScript.Import :=
  [.named ["Effect", "Option"] "effect", .named ["recordValue", "recordRequired", "recordOptional", "recordRaw", "recordSet"] "./records"]

#guard (Effect4.Api.printDecl "main" program).isSome
#guard match emitModule "main" program with
  | .ok emission => match admitModule "main" emission.module [] origins ambient with
    | .ok reading => reading.program == program
    | .error _ => false
  | .error _ => false

-- An absent field can retain unsupported metadata even when the program returns a number.
def unsupported : Term := .record [("slot", true, .app "Unresolved" [.nat])] [] .nil

def discarded : NativeEff := .bind (.succeed unsupported) (.succeed (.lit (.nat 0)))

#guard Formation.checkInput discarded [] = none
#guard typeOfProgram (nativeSignature []) discarded = some (.pure .nat)
#guard (Effect4.Api.print discarded).isOk
#guard (Effect4.Api.printDecl "main" discarded).isNone
#guard match emitModule "main" discarded with
  | .error (.print (.typeSpelling _)) => true
  | _ => false

-- Raw reconstruction remains available; checked source admission refuses unsupported metadata.
#guard match Program.printModule (nativeSignature []) "main" (.pure .nat) discarded with
  | .ok declarations =>
    let module : TypeScript.Module := { header := [], imports := [], decls := declarations.map .const }
    match admitModule "main" module [] origins ambient with
    | .error (.unrepresentable (.typeSpelling _)) => true
    | _ => false
  | .error _ => false

#print axioms Effect4.Program.annotationRefusal
#print axioms Effect4.Program.printEntry_checks
#print axioms Effect4.Program.printEntry_annotations

end Effect4.Test.RecordEmission
