import Tools.Code.Module
import Effect4.Store.Domain.ProgramWire

open Effect4 Effect4.Program Effect4.Codegen Tools.Code

namespace CodePlaneProbe

def mapTerm : Term := .app "mapSet" (.cons (.app "mapEmpty" .nil)
  (.cons (.lit (.str "k")) (.cons (.lit (.nat 7)) .nil)))

def cases : List (String × NativeEff) :=
  [("scalar", .succeed (.lit (.nat 7))),
   ("emptyMap", .succeed (.app "mapEmpty" .nil)),
   ("populatedMap", .succeed mapTerm),
   ("mapLookup", .succeed (.app "mapGet" (.cons mapTerm (.cons (.lit (.str "k")) .nil)))),
   ("mapKeys", .succeed (.app "mapKeys" (.cons mapTerm .nil)))]

def changedBreak : Doc := .group (.text "a" ++ .line " + " " -" ++ .text "b")

#guard changedBreak.flat 0 == "a + b"
#guard changedBreak.layout 0 == "a -\nb"
#guard undo (changedBreak.go 0 0 0 .broken [] 0).1 == "a + b"

end CodePlaneProbe

open CodePlaneProbe

def main (args : List String) : IO Unit := do
  let [out] := args | throw (IO.userError "usage: Probe OUT")
  let out : System.FilePath := out
  IO.FS.createDirAll (out / "corpus")
  for (name, program) in cases do
    let g := generate 120 "corpus" name program
    IO.println s!"{name}: type={g.type}; reads={reprStr g.reads}"
    match Api.emitModule "main" program [] with
    | .error why => throw (IO.userError (reprStr why))
    | .ok emission =>
      IO.println s!"freeNames={reprStr (freeNames emission.module)}"
      match g.module with
      | .error why => throw (IO.userError why)
      | .ok text => IO.FS.writeFile (out / "corpus" / (name ++ ".ts")) text
  let mut accepted := 0
  let mut equal := 0
  for (name, program) in Effect4.Program.Wire.Corpus.all do
    match Api.emitModule "main" program [] with
    | .error why => IO.println s!"corpus {name}: emission-refused {reprStr why}"
    | .ok emission =>
      let checked := { emission.module with imports := importsOf emission.module }
      match admitModule "main" checked [] allowedOrigins with
      | .error why => IO.println s!"corpus {name}: reading-refused {surfaceText why}"
      | .ok reading =>
        accepted := accepted + 1
        let same := reading.program == program
        if same then equal := equal + 1
        IO.println s!"corpus {name}: accepted; same-program={same}"
  IO.println s!"corpus counts: accepted={accepted}; same-program={equal}"
  IO.println s!"custom-break flat={reprStr (changedBreak.flat 0)}; layout={reprStr (changedBreak.layout 0)}"
