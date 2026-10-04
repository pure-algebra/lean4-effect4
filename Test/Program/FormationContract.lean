import Effect4.Laws.Api.Formation
import Effect4.Laws.Program.Template
import Effect4.Laws.Codegen.Checked
import Effect4.Laws.Codegen.Admit

/-!
# Raw and instantiated formation (rows 192 and 193)

Finite controls for `raw-formation` and `instantiated-formation`. The laws decide
raw formation and project actual row bindings. These examples also exercise each
checked boundary, including an empty replay tape. They establish no host behavior.
-/

namespace Test.Program.FormationContract

open Effect4 Effect4.Program

/-- A raw external row for boundary controls. -/
def row (request answer : Ty) : Row :=
  { name := "query", spelling := "Host.query", kind := .async, registration := .external,
    request, answer, cite := "formation contract" }

def pureProgram : NativeEff := .succeed (.lit (.nat 1))
def duplicate : Ty := .record [("x", false, .nat), ("x", true, .string)]
def badTable : RowTable := [row .nat (.list duplicate)]
def validTable : RowTable := [row .nat (.map .string .nat)]

-- Raw syntax is checked before record normalization can discard the second field.
#guard duplicate.normalize = (Ty.record [("x", false, .nat)]).normalize
#guard Formation.checkInput pureProgram badTable =
  some ⟨["table", "0", "answer", "type", "1"], duplicate, .repeatedField "x"⟩
#guard Formation.checkInput pureProgram validTable = none
#guard Formation.checkInput pureProgram [row (.map .nat .string) .unit] =
  some ⟨["table", "0", "request", "type", "0"], .map .nat .string, .mapKey⟩
#guard (Formation.checkInput pureProgram [row .unit (.app "Box" [.tuple [.nat, duplicate]])]).isSome

-- Unused raw annotations and unused table rows still belong to the input.
def badAnnotation : NativeEff :=
  .suspend (.iterate (some duplicate) (.lit .unit) (.lit (.bool false))
    (.lit .unit) (.lit .unit) (.succeed (.lit .unit)))
#guard match Formation.checkInput badAnnotation [] with
  | some why => why.ty = duplicate && why.reason = .repeatedField "x"
  | none => false

-- Every checked public boundary shares the raw refusal, independent of the tape.
#guard match admitProgram pureProgram ⟨badTable, []⟩ with
  | .error (.formation why) => why.ty = duplicate
  | _ => false
#guard match Effect4.Codegen.emitModule "main" pureProgram badTable with
  | .error (.formation why) => why.ty = duplicate
  | _ => false

def typedBadTable : TypedProgram (nativeSignature badTable) pureProgram :=
  ⟨.pure .nat, by decide⟩
#guard match Effect4.Codegen.emitTypedModule "main" typedBadTable with
  | .error (.formation why) => why.ty = duplicate
  | _ => false
#guard Api.printDecl "main" pureProgram badTable = none
#guard match Api.replayChecked pureProgram 10 [] [] badTable with
  | .inr (.formation why) => why.ty = duplicate
  | _ => false
#guard match Api.replayChecked pureProgram 10 [Api.evaluate] [] badTable with
  | .inr (.formation why) => why.ty = duplicate
  | _ => false

def source : TypeScript.Module :=
  { header := [], imports := [.named ["Effect"] "effect"], decls := [.const
      { doc := [], name := "main", value := .call (.ident "Effect.succeed") [.int 1],
        exported := true, type := some (.name ["Effect", "Effect"] [.name ["number"] [], .name ["never"] [], .name ["never"] []]) }] }
#guard match Effect4.Codegen.admitModule "main" source badTable with
  | .error (.formation why) => why.ty = duplicate
  | _ => false

-- Positive controls: none of the new checks is an unconditional refusal.
#guard (admitProgram pureProgram ⟨validTable, []⟩).isOk
#guard (Effect4.Codegen.emitModule "main" pureProgram validTable).isOk
#guard (Effect4.Codegen.admitModule "main" source validTable).isOk
#guard match Api.replayChecked pureProgram 10 [Api.evaluate] [] validTable with
  | .inl run => run.exit = some (.success (.nat 1))
  | _ => false
#guard match admitProgram pureProgram ⟨[row .nat .int], []⟩ with
  | .error (.uninhabited _) => true
  | _ => false

-- Inference traverses names and positions, including seed widening under join.
#guard Ty.infer []
    (.record [("a", false, .var 0), ("b", false, .var 1)])
    (.record [("b", false, .string), ("a", false, .nat)]) = [(0, .nat), (1, .string)]
#guard Ty.infer [] (.map (.var 0) (.var 1)) (.map .string .nat) =
  [(0, .string), (1, .nat)]
#guard Ty.infer [] (.tuple [.var 0, .bool, .var 1]) (.tuple [.string, .bool, .nat]) =
  [(0, .string), (1, .nat)]
#guard Ty.infer [] (.app "Box" [.var 0]) (.app "Box" [.nat]) = [(0, .nat)]
#guard Ty.infer [] (.app "Box" [.var 0]) (.app "Other" [.nat]) = []
#guard Ty.infer [(0, .nat)] (.record [("a", false, .var 0)])
    (.record [("a", false, .unknown)]) true = [(0, .unknown), (0, .nat)]

#guard (.map (.var 0) (.var 1) : Ty).templateAdmissible
#guard (.record [("a", false, .var 0)] : Ty).templateAdmissible
#guard (.tuple [.var 0, .bool, .nat] : Ty).templateAdmissible
#guard (.app "Box" [.var 0] : Ty).templateAdmissible
#guard !(.record [("a", false, .union .nat (.var 0))] : Ty).templateAdmissible

-- Open keys are deferred at the raw table, then checked on actual substitution.
def mapTemplate : Row := row (.map (.var 0) (.var 1)) (.var 1)
#guard Formation.checkInput pureProgram [mapTemplate] = none
#guard rowTy mapTemplate (.map .string .nat) = some (.pure .nat)
#guard rowTy mapTemplate (.map .nat .nat) = none
#guard rowTy (row (.var 0) (.map (.var 0) .nat)) .string = some (.pure (.map .string .nat))
#guard rowTy (row (.var 0) (.map (.var 0) .nat)) .nat = none
#guard rowTy { row (.var 0) .unit with error := .map (.var 0) .nat } .nat = none

-- Diagnostics distinguish a matched request with a malformed output from mismatch.
#guard match Api.explain (.perform (.external 0) (.lit (.nat 1)))
    [row (.var 0) (.map (.var 0) .nat)] with
  | some ⟨[], .instantiatedFormation "query" why⟩ =>
    why.path = ["row", "answer", "type", "0"] && why.ty = .map .nat .nat
  | _ => false
#guard checkRow (row .nat (.map .nat .nat)) .string = .error .requestNotSubtype

-- Normalization may close an open key. It must not bypass actual formation.
def erasedParameter : Row := row (.map (.union .unknown (.var 0)) .nat) .unit
#guard Formation.checkInput pureProgram [erasedParameter] = none
#guard erasedParameter.normalizeTypes.request = .map .unknown .nat
#guard rowTy erasedParameter.normalizeTypes (.map .unknown .nat) = none
#guard rowTy (row (.map .nat .nat) .unit) (.map .nat .nat) = none

-- New term metadata is visible in every surrounding program family.
def recordAnnotation : Term := .record [("x", true, duplicate)] [] .nil
#guard (Formation.checkInput (.succeed recordAnnotation : NativeEff) []).isSome
#guard (Formation.checkInput (.failCause (.die recordAnnotation) : NativeEff) []).isSome
#guard (Formation.checkInput (.gen (.cons (.ret recordAnnotation) .nil) : NativeEff) []).isSome
#guard (Formation.checkInput (.withFiber (.interruptAll (.lit .unit) (some recordAnnotation)) : NativeEff) []).isSome
#guard (Formation.checkInput (.provideLayer (.effect ⟨⟨0⟩, ⟨0⟩⟩ (.succeed recordAnnotation)) false
  (.succeed (.lit .unit)) : NativeEff) []).isSome
#guard (Formation.checkInput (.succeed (.app "some" (.cons recordAnnotation .nil)) : NativeEff) []).isSome
#guard match Api.replayChecked (.succeed recordAnnotation) 10 [] with
  | .inr (.formation why) => why.ty = duplicate
  | _ => false
#guard match Effect4.Codegen.emitModule "main" (.succeed recordAnnotation) [] with
  | .error (.formation why) => why.ty = duplicate
  | _ => false

-- Certificates expose the independent raw judgment.
example (admitted : AdmittedProgram pureProgram ⟨validTable, []⟩) :
    Formation.InputFormed pureProgram validTable := admitted.formed
example (emission : Effect4.Codegen.ModuleEmission pureProgram validTable "main") :
    Formation.InputFormed pureProgram validTable := emission.formed

example {fuel : Nat} {tape : List Api.Decision} {inspection : Api.Inspection}
    (accepted : Api.replayChecked pureProgram fuel tape [] validTable = .inl inspection) :
    Formation.InputFormed pureProgram validTable := Api.replayChecked_formed accepted

#print axioms Api.replayChecked_formation
#print axioms Api.replayChecked_formed
#print axioms Formation.checkInput
#print axioms Formation.checkInput_eq_none_iff
#print axioms rowTy_instantiated_formed
#print axioms rowTy_eq_some_iff
#print axioms checkRow_formation_iff
#print axioms checkRow_request_iff
#print axioms Ty.infer_closed
#print axioms Ty.infer_widensSub
#print axioms Ty.infer_widens
#print axioms Effect4.Codegen.ModuleEmission.recheck
#print axioms Effect4.Codegen.ModuleReading.recheck

end Test.Program.FormationContract
