import Tools.Code.Module
import Lean.Data.Json

/-! Five finite map callers exercise the shared binding inventory and real module generator.
The historical CP-01 probe remains independent evidence. No target execution is claimed. -/

open Effect4 Effect4.Program Effect4.Codegen Tools.Code

namespace CodegenBindingsPacket

-- Keep these five programs identical to the historical CP-01 callers.
def mapTerm : Term := .app "mapSet" (.cons (.app "mapEmpty" .nil)
  (.cons (.lit (.str "k")) (.cons (.lit (.nat 7)) .nil)))

def cases : List (String × NativeEff) :=
  [("scalar", .succeed (.lit (.nat 7))),
   ("emptyMap", .succeed (.app "mapEmpty" .nil)),
   ("populatedMap", .succeed mapTerm),
   ("mapLookup", .succeed (.app "mapGet" (.cons mapTerm (.cons (.lit (.str "k")) .nil)))),
   ("mapKeys", .succeed (.app "mapKeys" (.cons mapTerm .nil)))]

def utilityImport (imports : List TypeScript.Import) : Bool :=
  imports.any fun imported => match imported with
    | .all name _ _ => ["Readonly", "Record"].contains name
    | .named bindings _ _ => bindings.any fun binding =>
      ["Readonly", "Record"].contains binding.imported ||
        ["Readonly", "Record"].contains binding.localName

def importJson : TypeScript.Import → Lean.Json
  | .all name path typeOnly => Lean.Json.mkObj
      [("path", .str path), ("namespace", .str name), ("typeOnly", .bool typeOnly)]
  | .named bindings path typeOnly => Lean.Json.mkObj
      [("path", .str path), ("typeOnly", .bool typeOnly),
       ("bindings", .arr (bindings.map fun binding => Lean.Json.mkObj
         [("imported", .str binding.imported), ("local", .str binding.localName),
          ("typeOnly", .bool binding.typeOnly)]).toArray)]

end CodegenBindingsPacket

open CodegenBindingsPacket

def main (args : List String) : IO Unit := do
  let [folder] := args | throw (IO.userError "usage: Emit OUT")
  let out : System.FilePath := folder
  IO.FS.createDirAll (out / "corpus")
  let mut rows := #[]
  for (name, program) in cases do
    let emission ← match Api.emitModule "main" program [] with
      | .error why => throw (IO.userError s!"{name}: emission refused: {reprStr why}")
      | .ok emission => pure emission
    let imports := importsOf emission.module
    if utilityImport imports then
      throw (IO.userError s!"{name}: a global utility type was imported")
    let checked := { emission.module with imports }
    let reading ← match admitModule "main" checked [] allowedOrigins with
      | .error why => throw (IO.userError s!"{name}: structured admission refused: {surfaceText why}")
      | .ok reading => pure reading
    unless reading.program == program do
      throw (IO.userError s!"{name}: structured reading recovered another program")
    let generated := generate Ts.width "corpus" name program
    match generated.reads with
    | .error why => throw (IO.userError s!"{name}: generator admission refused: {why}")
    | .ok _ => pure ()
    let text ← match generated.module with
      | .error why => throw (IO.userError s!"{name}: generation refused: {why}")
      | .ok text => pure text
    let file := name ++ ".ts"
    IO.FS.writeFile (out / "corpus" / file) text
    rows := rows.push (Lean.Json.mkObj
      [("id", .str name), ("file", .str ("corpus/" ++ file)),
       ("structuredAdmission", .bool true), ("sameProgram", .bool true),
       ("utilityImports", .bool false), ("imports", .arr (imports.map importJson).toArray)])
    IO.println s!"{name}: structured admission and original-program equality pass; no utility imports"
  IO.FS.writeFile (out / "manifest.json")
    ((Lean.Json.mkObj [("format", .str "effect4-codegen-bindings-v1"),
      ("cases", .arr rows)]).pretty 100 ++ "\n")
