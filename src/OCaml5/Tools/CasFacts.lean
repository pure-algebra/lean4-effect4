import Lean
import OCaml5.Store.Facts

/-!
# Native store fact producer

This driver writes the files rendered by `OCaml5.Store.Facts`.
Regenerate them with `python3 scripts/generate.py --only cas`.
The renderer owns their content; this driver parses only the output directory.
-/

open Lean OCaml5.Store.Facts

def main (args : List String) : IO UInt32 := do
  let [out] := args | throw (IO.userError "CasFacts requires one output directory")
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := `Effect4.Store.Domain.Store }] {} 0
  let ctx : Core.Context := { fileName := "<cas-facts>", fileMap := default, maxHeartbeats := 0 }
  let (admission, _) ← (admissionFiles.run' {}).toIO ctx { env := env }
  let (policies, _) ← (rootPolicyFiles.run' {}).toIO ctx { env := env }
  let directory : System.FilePath := out
  IO.FS.createDirAll directory
  for (name, implementation, interface) in
      [("e4_kind", kindFiles.1, kindFiles.2), ("e4_admission", admission.1, admission.2),
       ("e4_root_policy", policies.1, policies.2), ("e4_result", resultFiles.1, resultFiles.2)] do
    IO.FS.writeFile (directory / (name ++ ".ml")) implementation
    IO.FS.writeFile (directory / (name ++ ".mli")) interface
    IO.println s!"wrote {name}.ml and {name}.mli"
  return 0
