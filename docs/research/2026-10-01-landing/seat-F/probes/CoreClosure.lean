import Effect4
import Effect4.Laws

/-!
Seat F probe (2026-10-01, landing item 2): which modules of the `Effects` package does the core
root `Effect4` reach, transitively, through the compiled import graph (the module data of the
loaded `.olean`s, the walk `Test/Audit/AxiomGate.lean`'s library-root gate uses)? And, for
contrast, which does `Effect4.Laws` reach?

Red control: at `dceae006` (before item 2) the core root must reach `Effects.Algebra.Program`
through `Effect4.Machine.Context`; the first run, on the unchanged tree, is that control.
-/

open Lean Elab Command

def closureOf (graph : Std.HashMap Name (Array Name)) (root : Name) : NameSet := Id.run do
  let mut reached : NameSet := {}
  let mut stack := [root]
  for _ in [0:1000000] do
    match stack with
    | [] => break
    | m :: rest =>
      stack := rest
      if reached.contains m then continue
      reached := reached.insert m
      stack := (graph.getD m #[]).toList ++ stack
  return reached

#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut graph : Std.HashMap Name (Array Name) := {}
  for (name, data) in env.header.moduleNames.zip env.header.moduleData do
    graph := graph.insert name (data.imports.map (·.module))
  for root in [`Effect4, `Effect4.Laws] do
    let reach := closureOf graph root
    let effects := reach.toList.filter fun m => (`Effects).isPrefixOf m
    let sorted := effects.toArray.qsort (·.toString < ·.toString)
    -- who imports an `Effects` module directly, inside the closure
    let importers := reach.toList.filter fun m =>
      !(`Effects).isPrefixOf m && (graph.getD m #[]).any fun i => (`Effects).isPrefixOf i
    let imp := importers.toArray.qsort (·.toString < ·.toString)
    logInfo m!"closure of {root}: {reach.size} modules; {sorted.size} of the `Effects` package: {sorted.toList}\n  importing an `Effects` module directly: {imp.toList}"
