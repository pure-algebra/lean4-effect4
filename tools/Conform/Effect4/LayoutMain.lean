import Conform.Effect4.TargetX2
import Conform.Effect4.TargetX2Fixed
import Conform.Effect4.TargetWire
import Conform.Effect4.TargetOCamlEff
import Conform.Layout.Check

/-!
# Conform.Effect4.LayoutMain — the layout checks over the four Effect4 targets

    lake env lean -M4096 --run tools/Conform/Effect4/LayoutMain.lean <outdir> [emitter-table.json …]

Reflects the closed world (`Conform.Effect4.LayoutWorld`), runs `layout.covers`,
`layout.injective` and `layout.coherent` over each of the four targets, writes one
`conform-report-v2` JSON per target into `<outdir>`, and runs the audit form of
`layout.coherent` over each recovered emitter table given on the command line.

A tool (`IO`, `Lean.Meta`), imported by nothing, outside the axiom gate.
-/

open Lean Meta
open Conform Conform.Layout

namespace Conform.Effect4

/-- One target's whole report. -/
def runTarget (T : Target) (W : World) (cfg : Conform.Layout.Config) :
    Report × Array Obligation :=
  let covers := checkCovers T W
  let (inj, obs) := checkInjective T W cfg
  let coh := checkCoherent T W cfg
  let expected := coversExpected T W + 2 * (subjects T W).size
  ({ tool := s!"conform.layout[{T.name}]"
     pins := [⟨"lean", "4.33.1"⟩, ⟨"target", T.name⟩]
     expected
     required := Conform.Layout.required T W
     rows := covers ++ inj ++ coh }, obs)

/-- The lines a reader wants on stderr: every failing row, and the whole counterexample. -/
def summarise (r : Report) : String :=
  let bad := r.failures.toList.map fun row =>
    s!"  {toString row.outcome} {row.check} {row.subject.render}\n    {row.message}"
  let (p, f, c, u) := r.counts
  s!"{r.tool}: {r.rows.size}/{r.expected} rows, {p} pass, {f} refused, {c} counterexample, \
{u} unresolved, exit {r.exitCode}\n" ++ "\n".intercalate bad

def targetsOf (W : World) : List Target :=
  [targetX2 W, targetX2Fixed W, targetWire W, targetOCamlEff W]

end Conform.Effect4

def main (argv : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  let outDir : System.FilePath := (argv.head?.getD "/tmp/conform-layout")
  let tableFiles := argv.tail
  IO.FS.createDirAll outDir
  let env ← importModules #[{ module := `Conform.Effect4.TargetOCamlEff },
                            { module := `Conform.Effect4.TargetX2Fixed },
                            { module := `Conform.Effect4.TargetWire }] {} 0
  let ctx : Core.Context := { fileName := "<conform-layout>", fileMap := default }
  let act : MetaM UInt32 := do
    let reading ← Conform.Effect4.readEffect4World
    let W := reading.world
    IO.println s!"world: {W.types.size} types, {W.types.foldl (fun n t => n + t.ctors.length) 0} \
constructors"
    unless reading.unspellable.isEmpty do
      IO.println s!"field types not spelled ({reading.unspellable.size}):"
      for u in reading.unspellable do IO.println s!"  {u}"
    let cfg : Conform.Layout.Config := {}
    let mut worst : UInt32 := 0
    for T in Conform.Effect4.targetsOf W do
      let (report, obs) := Conform.Effect4.runTarget T W cfg
      let sorted := report.sorted
      let json ← match sorted.withObligations Conform.Layout.registry obs with
        | .ok j => pure j
        | .error e => throwError e
      IO.FS.writeFile (outDir / s!"layout-{T.name}.json") (json.pretty ++ "\n")
      IO.eprintln (Conform.Effect4.summarise sorted)
      if sorted.exitCode > worst then worst := sorted.exitCode
    for f in tableFiles do
      let tbl ← Conform.Layout.EmitterTable.load f
      -- an emitter table is audited against the target whose name it carries as a prefix
      let some T := (Conform.Effect4.targetsOf W).find? fun t => tbl.name.startsWith t.name
        | throwError s!"{f}: no target's name is a prefix of the table name `{tbl.name}`"
      let rows := Conform.Layout.auditCoherence T tbl
      let report : Report :=
        { tool := s!"conform.layout.audit[{tbl.name}]"
          pins := [⟨"lean", "4.33.1"⟩, ⟨"target", T.name⟩]
          expected := (auditRequired tbl).size, required := auditRequired tbl, rows }
      IO.FS.writeFile (outDir / s!"audit-{tbl.name}.json") (report.sorted.toJson.pretty ++ "\n")
      IO.eprintln (Conform.Effect4.summarise report.sorted)
      if report.exitCode > worst then worst := report.exitCode
    return worst
  let (code, _) ← (act.run' {}).toIO ctx { env := env }
  return code
