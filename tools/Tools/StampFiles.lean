import Tools.GeneratedStamp

/-! Metadata-only driver for data producers whose outputs cannot carry comments.
The caller first runs the producer and supplies a JSON recipe with its source,
additional input files, and output files. This driver writes only sidecars.
-/

def main (args : List String) : IO Unit := do
  let [recipe] := args | throw (IO.userError "usage: StampFiles <recipe.json>")
  let json ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile recipe))
  let source ← IO.ofExcept (json.getObjValAs? String "source")
  let inputs ← IO.ofExcept (json.getObjValAs? (List String) "inputs")
  let outputs ← IO.ofExcept (json.getObjValAs? (List String) "outputs")
  let stamp ← Tools.GeneratedStamp.line source [] inputs
  for output in outputs do
    unless ← System.FilePath.pathExists output do
      throw (IO.userError s!"stamp output does not exist: {output}")
    Tools.GeneratedStamp.sidecar output stamp
