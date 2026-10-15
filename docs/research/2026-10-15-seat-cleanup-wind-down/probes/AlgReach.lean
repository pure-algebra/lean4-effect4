import Lean
import OCaml5.Lcnf.Gen

/-! Scratch probe (seat CLEANUP, S1): which declarations of the host run's closure need the
algebra types, as real (destructed or constructed) types or as mentioned annotation types. -/

open Lean OCaml5.Lcnf

def watched : List Name :=
  [`Effect4.Program.EffAlgebra, `Effect4.Program.TermAlgebra, `Effect4.Program.CauseTermAlgebra,
   `Effect4.Program.ArgF, `Effect4.Program.TyAlgebra]

def main (argv : List String) : IO Unit := do
  initSearchPath (← findSysroot)
  let roots := argv.toArray.map String.toName
  let env ← importModules #[{ module := `Test.Dogfood.Scenario.Todo.Host }] {} 0
  let ctx : Core.Context :=
    { fileName := "<alg-reach>", fileMap := default, maxHeartbeats := 1000000 * 1000 }
  let act : MetaM Unit := do
    let (c, ex, _) ← translateClosureInferring roots 4000 {} {}
    IO.println s!"closure {c.decls.size}"
    let env ← getEnv
    let mono := persistedMonoIndex env
    for t in c.decls do
      let some d := mono.findIn? env t.leanName | continue
      let (_, st) := translateDecl env d t.userName t.ocamlName {} ex
      let real := watched.filter st.realTypes.contains
      let ment := watched.filter st.mentioned.contains
      unless real.isEmpty && ment.isEmpty do
        IO.println s!"{t.leanName}: real {real} mentioned {ment}"
        IO.println s!"    {t.signature}"
  let _ ← (act.run' {}).toIO ctx { env := env }
