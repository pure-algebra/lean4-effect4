import Conform.Effect4.TargetLeanNative

/-!
# Conform.Effect4.NativeMain — the fifth target's report

    lake env lean -M4096 --run tools/Conform/Effect4/NativeMain.lean <outdir>

Writes two files into `<outdir>`:

* `layout-lean-native.json` — one `conform-report-v2` carrying six checks over the
  `lean-native` target: the three the other four targets are judged by (`layout.covers`,
  `layout.injective`, `layout.coherent`) and the three this target adds
  (`native.tag`, `native.fields`, `native.limits`);
* `native-layout.json` — the raw answer of `getCtorLayout`/`hasTrivialStructure?` for every
  type of the world, so a reader can check the rules against the compiler without rerunning it.

This driver writes **no file any other driver writes**, so it cannot move a byte of the
eleven reports `docs/research/type-tooling/layout/reproduce.sh` produces.

A tool (`IO`, `Lean.Meta`), imported by nothing, outside the axiom gate.
-/

open Lean Meta
open Conform Conform.Layout

namespace Conform.Effect4

/-- Every check this report carries, and what it expects to cover. -/
def runNative (T : Target) (W : World) (natives : Array Native.TypeNative)
    (cfg : Conform.Layout.Config) : Report × Array Obligation :=
  let covers := checkCovers T W
  let (inj, obs) := checkInjective T W cfg
  let coh := checkCoherent T W cfg
  let tags := Native.checkTags T.name W natives
  let fields := Native.checkFields T.name W natives
  let lims := Native.checkLimits T.name Native.limits natives
  let L := Native.limits
  ({ tool := s!"conform.layout[{T.name}]"
     pins := [⟨"lean", "4.33.1"⟩, ⟨"target", T.name⟩,
              ⟨"maxCtorFields", toString L.maxCtorFields⟩,
              ⟨"maxCtorScalarsSize", toString L.maxCtorScalarsSize⟩,
              ⟨"maxCtorTag", toString L.maxCtorTag⟩,
              ⟨"usizeSize", toString L.usizeSize⟩]
     expected := coversExpected T W + 2 * (subjects T W).size + Native.expected W natives
     required := Conform.Layout.required T W ++ Native.required T.name W natives
     rows := covers ++ inj ++ coh ++ tags ++ fields ++ lims }, obs)

/-- The lines a reader wants on stderr: the counts, then every failing row. -/
def summariseNative (r : Report) : String :=
  let bad := r.failures.toList.map fun row =>
    s!"  {toString row.outcome} {row.check} {row.subject.render}\n    {row.message}"
  let (p, f, c, u) := r.counts
  s!"{r.tool}: {r.rows.size}/{r.expected} rows, {p} pass, {f} refused, {c} counterexample, \
{u} unresolved, exit {r.exitCode}\n" ++ "\n".intercalate bad

end Conform.Effect4

def main (argv : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  let outDir : System.FilePath := (argv.head?.getD "/tmp/conform-layout")
  IO.FS.createDirAll outDir
  let env ← importModules #[{ module := `Conform.Effect4.TargetLeanNative }] {} 0
  let ctx : Core.Context := { fileName := "<conform-layout-native>", fileMap := default }
  let act : MetaM UInt32 := do
    let reading ← Conform.Effect4.readEffect4World
    let W := reading.world
    let natives ← Conform.Effect4.readLeanNative W
    let L := Conform.Layout.Native.limits
    IO.println s!"world: {W.types.size} types, \
{W.types.foldl (fun n t => n + t.ctors.length) 0} constructors; runtime limits: \
maxCtorFields {L.maxCtorFields}, maxCtorScalarsSize {L.maxCtorScalarsSize}, \
maxCtorTag {L.maxCtorTag}, usizeSize {L.usizeSize}"
    let unavailable := natives.flatMap (·.unavailable)
    unless unavailable.isEmpty do
      IO.println s!"constructors with no compiled layout ({unavailable.size}):"
      for u in unavailable do IO.println s!"  {u}"
    let trivial := natives.filter (·.trivialCtor.isSome)
    IO.println s!"trivial structures ({trivial.size}): \
{", ".intercalate (trivial.toList.map (·.type.toString))}"
    IO.FS.writeFile (outDir / "native-layout.json")
      ((Lean.toJson natives).pretty ++ "\n")
    let T := Conform.Effect4.targetLeanNative W natives
    let cfg : Conform.Layout.Config := {}
    let (report, obs) := Conform.Effect4.runNative T W natives cfg
    let sorted := report.sorted
    let json ← match sorted.withObligations Conform.Layout.registry obs with
      | .ok j => pure j
      | .error e => throwError e
    IO.FS.writeFile (outDir / s!"layout-{T.name}.json") (json.pretty ++ "\n")
    IO.eprintln (Conform.Effect4.summariseNative sorted)
    IO.eprintln s!"obligations: {obs.size}"
    return sorted.exitCode
  let (code, _) ← (act.run' {}).toIO ctx { env := env }
  return code
