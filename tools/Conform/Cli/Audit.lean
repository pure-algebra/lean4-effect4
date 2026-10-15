import Lean
import Conform.Core.Report
import Conform.Core.Policy
import Conform.Manifest.Mirror

/-!
# Conform.Cli.Audit — the mirror census driver

    lake env lean -M4096 --run tools/Conform/Cli/Audit.lean --config <config.json> [--out <report.json>]

One `Conform.Report` on stdout (or `--out`), the human lines on stderr, and the report's own exit
code as the process's: `0` only when every subject passed and none is missing, `1` on a refusal or
a counterexample, `2` when a subject is unresolved or a row is missing.

**What it does.** Reads a configuration file (strictly — an unknown key is a refusal at load),
imports exactly the modules that file names, and runs the cross-language mirrors
(`Conform.Manifest.Mirror`): each configured mirror file is read back to a constructor list and
compared, names and order, with the environment's. The case-site audit and the rule extraction
it once ran went on 2026-10-15 (`docs/research/2026-10-15-lowering-state/README.md`, K4): decisions
row 375 cleared the case policy, and no lane ran either.

**The environment it reads.** `importModules` on the configuration's `imports`, exactly as
`tools/Effect4Gen/Main.lean` does: the audit's environment is the environment those modules'
`.olean`s carry, which is what a *consumer* of the library sees. The report's pins record the
Lean version and the configuration's own pins.

**Generic.** This module names no Effect4 declaration. Everything specific reaches it through
`--config`; `tools/Conform/Effect4/` holds the first such configuration.
-/

namespace Conform.Cli

open Lean

/-! ## The configuration -/

/-- What one run audits. `imports` decides the environment. -/
structure Config where
  /-- The report's `tool` field. -/
  tool : String
  /-- The modules to import before reading the environment. -/
  imports : Array Name
  /-- The mirror list. -/
  mirrors : System.FilePath
  /-- Extra `Pin`s the configuration wants in the report (a target version, a corpus revision). -/
  pins : Array (String × String)
deriving Inhabited

namespace Config

open Conform.Policy

def read (j : Json) : Policy.Reader Config := do
  let get ← object j ["tool", "imports", "mirrors", "pins", "note"]
  let tool ← field get "tool" string
  let imports ← field get "imports" fun a => array a Policy.name
  let mirrors ← field get "mirrors" string
  let pins ← field? get "pins" fun a => array a fun p => do
    let g ← object p ["name", "value"]
    let n ← field g "name" string
    let v ← field g "value" string
    pure (n, v)
  if imports.isEmpty then fail "`imports` is empty: there would be no environment to audit"
  return { tool, imports, mirrors := (mirrors : System.FilePath), pins := pins.getD #[] }

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
deriving Inhabited

/-- Total: every recursive call drops at least one element, so no `partial` and no `termination_by`
are needed — the compiler sees the structural recursion. -/
def parseArgs : List String → Args → Except String Args
  | [], a => if a.config == "" then .error "--config is required" else .ok a
  | "--config" :: v :: rest, a => parseArgs rest { a with config := v }
  | "--out" :: v :: rest, a => parseArgs rest { a with out := some v }
  | x :: _, _ => .error s!"unexpected argument `{x}`"

/-! ## The run -/

def run (args : Args) (cfg : Config) : CoreM Report := do
  let spec ← Conform.Manifest.MirrorSpec.load cfg.mirrors
  let (rows, expected, files) ← Conform.Manifest.check spec
  let pins := [{ name := "lean", value := Lean.versionString : Pin }]
    ++ cfg.pins.toList.map fun (n, v) => { name := n, value := v }
  let inputs := [← inputOf "config" args.config, ← inputOf "mirrors" cfg.mirrors]
    ++ (← files.toList.mapM fun f => inputOf s!"mirror:{f}" f)
  -- A run that checked nothing is not a passing run: a mirror list with no entry is unresolved.
  if expected == 0 then
    return { tool := cfg.tool, pins, inputs, expected := 1
           , required := #[⟨"conform.run", ⟨"config", [args.config.toString]⟩⟩]
           , rows := #[Row.unresolved "conform.run" { kind := "config", path := [args.config.toString] }
               "the mirror list names no mirror"] }
  return { tool := cfg.tool, pins, inputs, expected
         , required := Conform.Manifest.required spec, rows }

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
  -- `importModules`, not `withImportModules`: the latter is `unsafe` (it frees the imported
  -- regions when its action returns), and this driver exits the moment the report is written, so
  -- the only thing that would buy is an `unsafe def main`. Measured: the kernel refuses the safe
  -- `main` that calls it — `(kernel) invalid declaration, it uses unsafe declaration`.
  let env ← importModules (cfg.imports.map fun m => { module := m }) {} 0
  let ctx : Lean.Core.Context := { fileName := "<conform-audit>", fileMap := default }
  let result : Except String Report ← try
      let (report, _) ← (run args cfg).toIO ctx { env }
      pure (.ok report)
    catch e => pure (.error e.toString)
  match result with
  | .error e => do IO.eprintln s!"conform-audit: {e}"; return 2
  | .ok report => report.emit args.out
