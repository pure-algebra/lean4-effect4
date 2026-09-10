import Lean
import Conform.Core.Report
import Conform.Core.Policy
import Conform.Lcnf.Cases
import Conform.Manifest.Mirror
import Conform.Lcnf.Rules

/-!
# Conform.Cli.Audit — the driver

    lake env lean -M4096 --run tools/Conform/Cli/Audit.lean --config <config.json> \
      [--out <report.json>] [--dump-scan <scan.json>] [--rules] [--rules-out <rules.json>] \
      [--seed-policy <policy.json>]

One `Conform.Report` on stdout (or `--out`), the human lines on stderr, and the report's own exit
code as the process's: `0` only when every subject passed and none is missing, `1` on a refusal or
a counterexample, `2` when a subject is unresolved or a row is missing.

**What it does.** Reads a configuration file (strictly — an unknown key is a refusal at load),
imports exactly the modules that file names, and then runs, in order:

* **A1/A2** the case-site audit (`Conform.Lcnf.Cases`): the whole environment under the configured
  roots is walked for `cases` nodes on the configured families, and each site is judged against the
  policy the configuration names.
* **A3** the cross-language mirrors (`Conform.Manifest.Mirror`): each configured mirror file is
  read back to a constructor list and compared, names and order, with the environment's.
* **A4** the rule extraction (`Conform.Lcnf.Rules`), behind `--rules` because it writes a table
  rather than a verdict.

**The environment it reads.** `importModules` on the configuration's `imports`, exactly as
`tools/Effect4Gen/Main.lean` does: the audit's environment is the environment those modules'
`.olean`s carry, which is what a *consumer* of the library sees — including `PhaseExt.lean`'s
export filter (a non-public declaration keeps no code, a non-transparent one keeps an `extern`
stub). The report's pins record how many constants that was.

**Generic.** This module names no Effect4 declaration. Everything specific reaches it through
`--config`; `tools/Conform/Effect4/` holds the first such configuration.
-/

namespace Conform.Cli

open Lean

/-! ## The configuration -/

/-- What one run audits. `imports` decides the environment; `roots` decide which constants the
scan walks; the three file paths are optional, and a section whose file is absent from the
configuration simply does not run (it contributes no rows and no `expected`). -/
structure Config where
  /-- The report's `tool` field. -/
  tool : String
  /-- The modules to import before reading the environment. -/
  imports : Array Name
  /-- Name prefixes the scan walks; empty means every constant in the environment. -/
  roots : Array Name
  /-- Which declaration list the case-site scan walks: `constants` (the environment's, the
  conservative denominator) or `monoExtension` (the compiler's own, which also reaches
  `f._redArg` and friends). See `Conform.Lcnf.ScanSource`. -/
  source : Conform.Lcnf.ScanSource
  /-- The case-site policy (A2). -/
  casesPolicy : Option System.FilePath
  /-- The mirror list (A3). -/
  mirrors : Option System.FilePath
  /-- The rule-extraction configuration (A4). -/
  rules : Option System.FilePath
  /-- Extra `Pin`s the configuration wants in the report (a target version, a corpus revision). -/
  pins : Array (String × String)
deriving Inhabited

namespace Config

open Conform.Policy

def read (j : Json) : Policy.Reader Config := do
  let get ← object j
    ["tool", "imports", "roots", "source", "casesPolicy", "mirrors", "rules", "pins", "note"]
  let tool ← field get "tool" string
  let imports ← field get "imports" fun a => array a Policy.name
  let roots ← field get "roots" fun a => array a Policy.name
  let source ← field? get "source" fun v =>
    enum v [("constants", Conform.Lcnf.ScanSource.constants)
           , ("monoExtension", Conform.Lcnf.ScanSource.monoExtension)]
  let casesPolicy ← field? get "casesPolicy" string
  let mirrors ← field? get "mirrors" string
  let rules ← field? get "rules" string
  let pins ← field? get "pins" fun a => array a fun p => do
    let g ← object p ["name", "value"]
    let n ← field g "name" string
    let v ← field g "value" string
    pure (n, v)
  if imports.isEmpty then fail "`imports` is empty: there would be no environment to audit"
  return { tool, imports, roots, source := source.getD .constants
         , casesPolicy := casesPolicy.map fun (s : String) => (s : System.FilePath)
         , mirrors := mirrors.map fun (s : String) => (s : System.FilePath)
         , rules := rules.map fun (s : String) => (s : System.FilePath)
         , pins := pins.getD #[] }

def load (file : System.FilePath) : IO Config := Policy.load file read

end Config

/-! ## Inputs, hashed

A report is comparable with another report only when it says what it read. Every file the run
opened becomes a `Conform.Input` with its SHA-256, computed by the same route the tree's other
stamps use (`tools/Tools/GeneratedStamp.lean`): `shasum -a 256` over the bytes, no FFI. -/

def sha256 (text : String) : IO String := do
  let out ← try
      IO.Process.output { cmd := "sha256sum" } (some text)
    catch _ =>
      IO.Process.output { cmd := "shasum", args := #["-a", "256"] } (some text)
  unless out.exitCode == 0 do throw (IO.userError s!"sha256: {out.stderr}")
  let digest := (out.stdout.splitOn " ").head!
  unless digest.length == 64 do throw (IO.userError "sha256: unexpected output")
  return digest

def inputOf (name : String) (file : System.FilePath) : IO Input := do
  return { name, sha256 := (← sha256 (← IO.FS.readFile file)) }

/-! ## Arguments -/

structure Args where
  config : System.FilePath := ""
  out : Option System.FilePath := none
  dumpScan : Option System.FilePath := none
  seedPolicy : Option System.FilePath := none
  rulesOut : Option System.FilePath := none
  withRules : Bool := false
deriving Inhabited

partial def parseArgs : List String → Args → Except String Args
  | [], a => if a.config == "" then .error "--config is required" else .ok a
  | "--config" :: v :: rest, a => parseArgs rest { a with config := v }
  | "--out" :: v :: rest, a => parseArgs rest { a with out := some v }
  | "--dump-scan" :: v :: rest, a => parseArgs rest { a with dumpScan := some v }
  | "--seed-policy" :: v :: rest, a => parseArgs rest { a with seedPolicy := some v }
  | "--rules-out" :: v :: rest, a => parseArgs rest { a with rulesOut := some v, withRules := true }
  | "--rules" :: rest, a => parseArgs rest { a with withRules := true }
  | x :: _, _ => .error s!"unexpected argument `{x}`"

/-! ## The run -/

private def writeJson (path : System.FilePath) (j : Json) : IO Unit := do
  if let some dir := path.parent then IO.FS.createDirAll dir
  IO.FS.writeFile path (j.pretty ++ "\n")

/-- Everything the run produces: the rows, how many subjects it set out to cover, and the pins and
inputs it accumulated. -/
structure Acc where
  rows : Array Row := #[]
  expected : Nat := 0
  pins : List Pin := []
  inputs : List Input := []

def run (args : Args) (cfg : Config) : CoreM (Report × Option Json) := do
  let mut acc : Acc := {}
  acc := { acc with
    pins := acc.pins ++ [{ name := "lean", value := Lean.versionString }]
      ++ cfg.pins.toList.map fun (n, v) => { name := n, value := v } }
  acc := { acc with inputs := acc.inputs ++ [← inputOf "config" args.config] }
  -- A1/A2 -----------------------------------------------------------------------------------
  let mut scan? : Option Conform.Lcnf.Scan := none
  match cfg.casesPolicy with
  | none => pure ()
  | some file =>
    let policy ← Conform.Lcnf.CasesPolicy.load file
    let scan ← Conform.Lcnf.scan
      { roots := cfg.roots, families := policy.familyNames, source := cfg.source }
    scan? := some scan
    let (rows, expected) := Conform.Lcnf.check scan policy
    acc := { acc with
      rows := acc.rows ++ rows
      expected := acc.expected + expected
      pins := acc.pins ++ scan.pins
      inputs := acc.inputs ++ [← inputOf "casesPolicy" file] }
    if let some p := args.dumpScan then writeJson p scan.toJson
    if let some p := args.seedPolicy then
      writeJson p (Conform.Lcnf.CasesPolicy.toJson (Conform.Lcnf.seed scan))
  -- A3 --------------------------------------------------------------------------------------
  match cfg.mirrors with
  | none => pure ()
  | some file =>
    let spec ← Conform.Manifest.MirrorSpec.load file
    let (rows, expected, files) ← Conform.Manifest.check spec
    acc := { acc with
      rows := acc.rows ++ rows
      expected := acc.expected + expected
      inputs := acc.inputs ++ [← inputOf "mirrors" file] ++ (← files.toList.mapM fun f =>
        inputOf s!"mirror:{f}" f) }
  -- A4 --------------------------------------------------------------------------------------
  let mut rules? : Option Json := none
  if args.withRules then
    match cfg.rules with
    | none =>
      acc := { acc with
        rows := acc.rows.push (Row.unresolved "rules.extract"
          { kind := "config", path := ["rules"] }
          "--rules was given but the configuration names no `rules` file")
        expected := acc.expected + 1 }
    | some file =>
      let spec ← Conform.Lcnf.RulesSpec.load file
      let (table, rows, expected) ← Conform.Lcnf.extract spec
      rules? := some table
      acc := { acc with
        rows := acc.rows ++ rows
        expected := acc.expected + expected
        inputs := acc.inputs ++ [← inputOf "rules" file] }
      if let some p := args.rulesOut then writeJson p table
  -- A run that checked nothing is not a passing run. Without this a configuration whose only
  -- section is A4, invoked without `--rules`, would print `0/0 subjects, exit 0`.
  if acc.expected == 0 then
    acc := { acc with
      rows := acc.rows.push (Row.unresolved "conform.run"
        { kind := "config", path := [args.config.toString] }
        "this run selected no check: the configuration names no section, or the only section it \
         names is behind a flag that was not given (`--rules`)")
      expected := 1 }
  let report : Report :=
    { tool := cfg.tool, pins := acc.pins, inputs := acc.inputs
    , expected := acc.expected, rows := acc.rows }
  return (report, rules?)

end Conform.Cli

open Lean Conform Conform.Cli in
/-- A configuration or policy that does not load leaves **no report at all**, which is exit `2`
(`Report.exitCode`'s "not even a verdict"), not exit `1`: nothing was checked. The message is the
reader's, which already carries the JSON path. -/
def main (argv : List String) : IO UInt32 := do
  let args ← match parseArgs argv {} with
    | .ok a => pure a
    | .error e => do IO.eprintln s!"conform-audit: {e}"; return 2
  let cfg ← try Config.load args.config catch e => do
    IO.eprintln s!"conform-audit: {e.toString}"
    return 2
  initSearchPath (← findSysroot)
  let env ← importModules (cfg.imports.map fun m => { module := m }) {} 0
  let ctx : Lean.Core.Context := { fileName := "<conform-audit>", fileMap := default }
  let result : Except String Report ← try
      let ((report, _), _) ← (run args cfg).toIO ctx { env }
      pure (.ok report)
    catch e => pure (.error e.toString)
  match result with
  | .error e => do IO.eprintln s!"conform-audit: {e}"; return 2
  | .ok report => report.emit args.out
