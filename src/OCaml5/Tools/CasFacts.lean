import Lean
import OCaml5.Store.Facts

/-!
# Native store fact producer

This driver writes the files rendered by `OCaml5.Store.Facts`.
Regenerate them with `python3 scripts/generate.py --only cas`.
The renderer owns their content and checks every unit before any file is written; this driver
parses only the output directory.
-/

open Lean OCaml5.Store.Facts

def main (args : List String) : IO UInt32 := do
  let [out] := args | throw (IO.userError "CasFacts requires one output directory")
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := `Effect4.Store.Domain.Store }] {} 0
  let ctx : Core.Context := { fileName := "<cas-facts>", fileMap := default, maxHeartbeats := 0 }
  let (units, _) ← (files.run' {}).toIO ctx { env := env }
  let directory : System.FilePath := out
  IO.FS.createDirAll directory
  for (name, implementation, interface) in units do
    IO.FS.writeFile (directory / (name ++ ".ml")) implementation
    IO.FS.writeFile (directory / (name ++ ".mli")) interface
    IO.println s!"wrote {name}.ml and {name}.mli"
  return 0
