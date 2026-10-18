import OCaml5.Store.DiskOracle

/-!
# Disk comparison oracle driver

Writes the transition table of `OCaml5.Store.DiskOracle` for the qcheck-stm harness
(`ocaml/engine/cas/test/test_disk_stm.ml`). It refuses an incomplete transition graph rather than
write a partial table. Regenerate with `python3 scripts/generate.py --only cas`.
-/

def main (args : List String) : IO UInt32 := do
  let [path] := args | throw (IO.userError "CasDiskOracle requires an output file")
  let .ok text := OCaml5.Store.DiskOracle.render
    | throw (IO.userError "CasDiskOracle refuses an incomplete transition graph")
  IO.FS.writeFile path text
  IO.println s!"wrote {path}"
  return 0
