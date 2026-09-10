import Tools.GeneratedStamp
import Effect4.Program.Wire
import Tools.ProgramStructure
import OCaml5.Eff.Goldens

/-!
# EffWire — the goldens of the Eff wire

Prints, for every program of `Effect4.Program.Wire.Corpus`, the canonical bytes as hex
and the constructor-index manifest of the families the wire covers, so an implementation
of the same rule in another language (`ocaml/eff`) can be checked byte for byte.

    lake env lean --run src/OCaml5/Tools/EffWire.lean [outdir]

With an output directory: `<outdir>/<name>.hex` per program and `<outdir>/manifest.txt`;
without: everything on stdout. A tool, not a library: it only calls the wire.
-/

open Effect4.Program.Wire

def hexOfByte (b : UInt8) : String :=
  let digits := "0123456789abcdef".toList
  let hi := digits[b.toNat / 16]!
  let lo := digits[b.toNat % 16]!
  String.ofList [hi, lo]

def hex (bs : List UInt8) : String := String.join (bs.map hexOfByte)

/-- The constructor order every implementation of the wire must agree on (the join of
2026-09-07 appended `provideLayer`, `service` and `provideService` to `Eff`, and added
`LayerTerm` and the `ServiceKey` fields; `ocaml/eff/test/test_lean_wire.ml` checks every line
against the OCaml library's generated tables). -/
def manifest (env : Lean.Environment) : IO String := do
  let families := Tools.ProgramStructure.allSpecs.map (·.leanName)
  let mut rows : List String := []
  for name in families do
    let names ← if Lean.isStructure env name then
      pure (Lean.getStructureFields env name).toList
    else
      match env.find? name with
      | some (.inductInfo info) => pure info.ctors
      | _ => throw (IO.userError s!"EffWire: no inductive family {name}")
    rows := rows ++ [name.getString! ++ ": " ++ " ".intercalate (names.map Lean.Name.getString!)]
  let tags := Effect4.Store.Tag.all
  return "\n".intercalate (rows ++ ["tags: " ++ " ".intercalate
    (tags.map fun (name, value) => name ++ "=" ++ toString value.toNat)])

def main (args : List String) : IO Unit := do
  Lean.initSearchPath (← Lean.findSysroot)
  let env ← Lean.importModules #[{ module := `Effect4.Program.Wire }] {} 0
  let manifest ← manifest env
  match args with
  | [dir] =>
    let stamp ← Tools.GeneratedStamp.line "src/OCaml5/Tools/EffWire.lean"
    IO.FS.createDirAll dir
    for (name, p) in Corpus.all do
      IO.FS.writeFile s!"{dir}/{name}.hex" (hex (encodeProgram p) ++ "\n")
    IO.FS.writeFile s!"{dir}/manifest.txt" (manifest ++ "\n")
    -- Identity comes from independently declared Eff values, not a name whitelist.
    let common := Corpus.all.filterMap fun (name, program) =>
      match OCaml5.Eff.Corpus.corpus.find? (·.1 == name) with
      | some (_, other) => if program == other then some name else none
      | none => none
    IO.FS.writeFile s!"{dir}/same-programs.txt" ("\n".intercalate common ++ "\n")
    Tools.GeneratedStamp.sidecar s!"{dir}/same-programs.txt" stamp
    for (name, _) in Corpus.all do
      Tools.GeneratedStamp.sidecar s!"{dir}/{name}.hex" stamp
    Tools.GeneratedStamp.sidecar s!"{dir}/manifest.txt" stamp
    IO.println s!"wrote {Corpus.all.length} goldens and manifest.txt to {dir}"
  | _ =>
    IO.println manifest
    for (name, p) in Corpus.all do
      IO.println s!"{name}\t{hex (encodeProgram p)}"
