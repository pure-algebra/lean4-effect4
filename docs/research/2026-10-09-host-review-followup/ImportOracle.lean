import Lean

open Lean
def main (args : List String) : IO Unit := do
  for path in args do
    let content ← IO.FS.readFile path
    let ctx := Parser.mkInputContext content path
    let (header, _, messages) ← Parser.parseHeader ctx
    let mut names : Array Json := #[]
    if let `(Parser.Module.header| $[module]? $[prelude]? $imports*) := header then
      for entry in imports do
        if let `(Parser.Module.import| $[public]? $[meta]? import $[all]? $mod) := entry then
          names := names.push (.str mod.getId.toString)
    IO.println (Json.mkObj [("path", .str path), ("imports", .arr names),
      ("headerErrors", toJson messages.hasErrors)]).compress
