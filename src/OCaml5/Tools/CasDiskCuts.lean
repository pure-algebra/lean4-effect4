import OCaml5.Store.DiskOracle

/-!
# Interrupted-commit cut table

Renders the actual `Cas` cuts of one transaction (`Cut`) for the native kill harness. Each row is
the image an interruption at that hook must reopen to. Regenerate with
`python3 scripts/generate.py --only cas`. The finite table proves no filesystem theorem.
-/
namespace OCaml5.Store.DiskOracle
open Effect4.Store

def cutRows : Except String String := do
  let initial := Txn.mk [schema, a] [.create "docs/a" .swap (target a)]
  let (someCas : Cas) ← match Cas.empty.commit initial with
    | .error _ => .error "cut initial transaction refuses"
    | .ok (_, cas) => .ok cas
  let transaction : Txn := ⟨[a, b, t, u], [.advance "docs/a" ⟨address a, 1⟩ (target b)]⟩
  let cuts : List (String × Cut) := [
    ("before-write0", .nodes 0), ("after-write1", .nodes 1), ("after-write2", .nodes 2),
    ("after-sync", .nodes 3), ("before-publish", .nodes 3), ("after-publish", .published)]
  let rows ← cuts.mapM fun (name, cut) => match someCas.interrupted transaction cut with
    | .error _ => .error ("accepted cut refuses: " ++ name)
    | .ok cas => .ok (name ++ "\t" ++ image cas.store)
  pure ("# actual accepted Cas.interrupted images; fresh counts exclude initial duplicate A\n" ++
    String.intercalate "\n" rows ++ "\n")
end OCaml5.Store.DiskOracle

def main (args : List String) : IO UInt32 := do
  let [path] := args | throw (IO.userError "CasDiskCuts requires an output file")
  let .ok text := OCaml5.Store.DiskOracle.cutRows
    | throw (IO.userError "CasDiskCuts refuses an unaccepted cut")
  IO.FS.writeFile path text
  IO.println s!"wrote {path}"
  return 0
