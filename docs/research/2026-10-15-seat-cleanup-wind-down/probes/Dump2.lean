import Lean
import OCaml5.Lcnf.Index

/-! Scratch probe (seat CLEANUP, S2): print persisted mono declarations, read through the
mono index as the generator reads them, and the callers of a constant among them. -/

open Lean Compiler LCNF OCaml5.Lcnf

def main (args : List String) : IO Unit := do
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := `Test.Dogfood.Scenario.Todo.Host }] {} 0
  let ctx : Core.Context := { fileName := "<dump>", fileMap := default }
  let act : CoreM Unit := do
    let mono := persistedMonoIndex env
    match args with
    | "--callers" :: target :: _ =>
      let t := target.toName
      for (n, d) in mono.toList do
        let .code body := d.value | continue
        let mut hit := false
        let (_, found) := (body.forM fun node => do
          if let .let decl _ := node then
            if let .const c _ _ := decl.value then
              if c == t then set true
          : StateM Bool Unit).run false
        hit := found
        if hit then IO.println s!"caller: {n}"
    | "--params" :: names =>
      for a in names do
        match mono.findIn? env a.toName with
        | none => IO.println s!"-- {a}: no persisted mono decl"
        | some d =>
          for prm in d.params do
            IO.println s!"{a} param {prm.binderName} : {prm.type}"
    | names =>
      for a in names do
        match mono.findIn? env a.toName with
        | none => IO.println s!"-- {a}: no persisted mono decl"
        | some d =>
          IO.println s!"-- {a}"
          IO.println (← ppDecl' d .mono).pretty
  let _ ← act.toIO ctx { env := env }
