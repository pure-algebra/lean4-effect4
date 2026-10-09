import Test.Program.StreamArray
import Effect4.Emit

open Effect4 Effect4.Program Effect4.Program.Authoring Effect4.Modules
namespace StreamDefsTargetProbe

def header (request answer : Ty) : TypeScript.ConstDecl :=
  { doc := [], name := "minimal"
    value := .lambda [{name := "a0", type := Codegen.Types.ofTy request}]
      (.ident "unused")
      (some (.name ["Effect", "Effect"]
        [(Codegen.Types.ofTy answer).getD (.name ["unknown"] []),
         .name ["never"] [], .name ["never"] []])) }

#guard Codegen.Classes.ReadableTy (.list .nat)
#guard !Codegen.Classes.ReadableTy (.refOf (.list .nat))
#eval Codegen.Classes.ReadableTy (Program.Stream.pulledTy .nat .unit)
#eval (Codegen.Types.ofTy (Program.Stream.pulledTy .nat .unit)).bind Codegen.Classes.readTyChecked
#guard (Program.readDefHead (header (.list .nat) (.list .nat))).isOk
#guard (Program.readDefHead (header (.list .nat) (.refOf (.list .nat)))).map Prod.fst ==
  .error (.shape "definition")
#guard (Program.readDefHead (header (.refOf (.list .nat)) .unit)).map Prod.fst ==
  .error (.shape "definition")
#guard (Program.readDefHead (header .unit (Program.Stream.pulledTy .nat .unit))).isOk

def diagnose : Option (List (String × Except Program.ReadRefusal DefDecl)) := do
  let built ← (Api.Author.build (Test.Program.StreamArray.numbers.module
    (Stream.runCollect (Test.Program.StreamArray.numericSource Test.Program.StreamArray.input)))).toOption
  let emitted ← (Api.emitModule "main" built.program built.table).toOption
  let leading := Program.defsPrefix emitted.module.decls.dropLast
  pure (leading.1.map fun c => (c.name, (Program.readDefHead c).map Prod.fst))

#eval diagnose
#guard diagnose == some [
  ("e4$arrays$openArray", .error (.shape "definition")),
  ("e4$arrays$pull", .error (.shape "definition")),
  ("e4$arrays$close", .error (.shape "definition"))]

-- Research-only top-level experiment. The existing reader reads the Ref argument.
-- This does not supply a recursive reader or bypass public module admission.
def candidateType (x : TypeScript.TypeRef) : Option Ty := do
  let raw ← match x with
    | .name ["Ref", "Ref"] [arg] =>
      (Codegen.Classes.readTyChecked arg).map Ty.refOf
    | _ => Codegen.Classes.readTy x
  if Codegen.Types.ofTy raw = some x then some raw else none

def candidateHeader (c : TypeScript.ConstDecl) : Except ReadRefusal DefDecl :=
  match c.value with
  | .lambda [⟨parameter, some request⟩] _
      (some (.name ["Effect", "Effect"] [answer, error, .name ["never"] []])) =>
    if parameter = "a0" then
      match candidateType request, candidateType answer, candidateType error with
      | some request, some answer, some error => .ok {name := c.name, request, answer, error}
      | _, _, _ => .error (.shape "definition")
    else .error (.shape "definition")
  | _ => .error (.shape "definition")

#guard candidateType (.name ["Ref", "Ref"] [.name ["ReadonlyArray"] [.name ["number"] []]]) ==
  some (.refOf (.list .nat))
#guard candidateType (.name ["Ref", "Ref"] []) == none
#guard candidateType (.name ["Ref", "Ref"] [.name ["number"] [], .name ["number"] []]) == none
#guard candidateType (.name ["Other", "Ref"] [.name ["number"] []]) == none
#guard candidateType (.name ["Ref"] [.name ["number"] []]) == none
#guard candidateType (.name ["Ref", "Ref"] [.name ["unknown"] []]) == none
#guard candidateType (.name ["Ref", "Ref"] [.name ["ReadonlyArray"] [.name ["unknown"] []]]) == none
#guard (candidateHeader (header (.list .nat) (.refOf (.list .nat)))).isOk
#guard (candidateHeader (header (.refOf (.list .nat)) (Program.Stream.pulledTy .nat .unit))).isOk
#guard (candidateHeader (header (.refOf (.list .nat)) .unit)).isOk

def candidateDeclarations : Option (List (String × Except ReadRefusal DefDecl)) := do
  let built ← (Api.Author.build (Test.Program.StreamArray.numbers.module
    (Stream.runCollect (Test.Program.StreamArray.numericSource Test.Program.StreamArray.input)))).toOption
  let emitted ← (Api.emitModule "main" built.program built.table).toOption
  pure ((Program.defsPrefix emitted.module.decls.dropLast).1.map
    fun c => (c.name, candidateHeader c))

#eval candidateDeclarations
#guard candidateDeclarations == some [
  ("e4$arrays$openArray", .ok {name := "e4$arrays$openArray", request := .list .nat, answer := .refOf (.list .nat)}),
  ("e4$arrays$pull", .ok {name := "e4$arrays$pull", request := .refOf (.list .nat), answer := (Program.Stream.pulledTy .nat .unit).normalize}),
  ("e4$arrays$close", .ok {name := "e4$arrays$close", request := .refOf (.list .nat), answer := .unit})]

-- The recursive production extension would additionally read lists holding Refs.
-- This narrow top-level experiment deliberately leaves that case unanswered.
#guard candidateType (.name ["ReadonlyArray"] [.name ["Ref", "Ref"] [.name ["number"] []]]) == none
end StreamDefsTargetProbe
