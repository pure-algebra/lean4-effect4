import Lean
import OCaml5.Lcnf.Dump

/-!
# LcnfDump — print the mono-phase LCNF of constants

A thin driver over `OCaml5.Lcnf.Dump`: import `Effect4.Machine.Fibers`, then for each
constant name on the command line print the compiler's own pretty print (`ppDecl'`) and
the shape sketch (`sketch`). With `--base` first, print the base phase instead.

    lean -M4096 --run src/OCaml5/Tools/LcnfDump.lean Effect4.Machine.Dispatcher.insert

This is a tool (`IO`, `CoreM`); it is not part of any audited library.
-/

open Lean OCaml5.Lcnf

def main (args : List String) : IO Unit := do
  initSearchPath (← findSysroot)
  let (base, names) := match args with
    | "--base" :: rest => (true, rest)
    | rest => (false, rest)
  let env ← importModules #[{ module := `Effect4.Machine.Fibers }] {} 0
  let ctx : Core.Context := { fileName := "<lcnf-dump>", fileMap := default }
  let act : CoreM Unit := do
    for a in names do
      let n := a.toName
      let decl? ← if base then baseDecl? n else monoDecl? n
      match decl? with
      | none => IO.println s!"-- {n}: no {if base then "base" else "mono"} decl"
      | some d =>
        IO.println s!"-- {n}: {if base then "base" else "mono"} LCNF (ppDecl')"
        IO.println (← ppMono d).pretty
        IO.println s!"-- {n}: sketch"
        IO.println (sketch d)
        IO.println ""
  let _ ← act.toIO ctx { env := env }
