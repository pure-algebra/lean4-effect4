import Effect4.Program.Wire
import Tools.ProgramStructure
import Tools.ProfileJson

/-! Join fixture identities to actual first-order programs. The constructor name is looked
up by the canonical program's ordinal in the shared source description. Expected A/E/R
comes from the current checker, never from a copied TypeScript head table. -/
open Lean Meta Effect4.Program

def main (args : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := `Effect4.Program.Wire }] {} 0
  let action : MetaM Lean.Json := do
    let blocks ← Tools.ProgramStructure.readBlocks
    let some family := blocks.flatten.find? (·.spec.leanName == ``Eff)
      | throwError "Eff descriptor missing"
    let mut rows := #[]
    for (name, program) in Wire.Corpus.all do
      let some t := typeOf nativeSignature program | throwError "{name}: typing refused"
      let .ctor index _ := Effect4.Store.Canonical.toVal program | throwError "{name}: expected program frame"
      let some constructor := family.constructors.find? (·.index == index)
        | throwError "{name}: unknown constructor ordinal {index}"
      rows := rows.push (Lean.Json.mkObj [
        ("query", .str ("program/" ++ name)), ("constructor", .str constructor.name.toString),
        ("program", .str name), ("path", toJson ([] : List Nat)),
        ("answer", .str t.answer.render), ("error", .str t.error.render),
        ("requires", .arr (t.requires.elems.map Tools.ProfileJson.flatKeyJson).toArray)])
    return Lean.Json.mkObj [("format", .str "effect4-typing-fixtures-v1"), ("fixtures", .arr rows)]
  let (data, _) ← action.run'.toIO { fileName := "<target-fixtures>", fileMap := default } { env }
  let out : System.FilePath := args.headD ".lake/conform/target-fixtures.json"
  if let some parent := out.parent then IO.FS.createDirAll parent
  IO.FS.writeFile out (data.pretty ++ "\n")
  return 0
