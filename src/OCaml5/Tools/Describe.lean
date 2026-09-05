import Lean
import Effect4.Machine.Fibers
import Effect4.Machine.Stores
import Effect4.Machine.Layer
import Effect4.Machine.Context

/-!
# Describe — carrier descriptions read off the Lean environment

The step `OCaml5/Ml/Reflect.lean` names as "later": instead of a caller populating
`StructDesc`/`InductiveDesc` by hand from a Lean file, this driver reads the declaration
out of the environment and prints the description in the same `where` syntax the hand
descriptions under `OCaml5/Avatar/` use, so `OCaml5.Avatar.Check` can diff the two.

Only the Lean-derived half is printed: name, site, parameters, fields (or constructors and
their argument names) with their types as `LTy`. The decisions — `isMutable`, `hole`,
`erased`, `substitute` fields, `Subst` entries, comments — stay in a per-carrier overlay,
which is exactly the part a human is supposed to write.

    lake env lean --run src/OCaml5/Tools/Describe.lean Effect4.Machine.RunFiber ...
    lake env lean --run src/OCaml5/Tools/Describe.lean --module OCaml5.Avatar.Derived.Stores refKey=Effect4.Machine.RefKey … > src/OCaml5/Avatar/Derived/Stores.lean

This is a tool (`IO`, `Lean.Meta`); it is not part of any audited library.
-/

open Lean Meta

/-- The head of a Lean type as `Render.lean` spells it: relative to `Effect4.Machine`. -/
def shortHead (n : Name) : String :=
  let s := n.toString
  let strip (pre : String) (s : String) : String :=
    if s.startsWith pre then (s.drop pre.length).toString else s
  -- The module namespaces the hand descriptions leave implicit, longest first.
  ["Effect4.Machine.Env.Context.", "Effect4.Machine.Env.", "Effect4.Machine.Layers.",
   "Effect4.Machine.", "Effect4."].foldl (fun acc pre => strip pre acc) s

/-- Render an `Expr` as the `LTy` constructor text the descriptions use. -/
partial def lty (e : Expr) : MetaM String := do
  let e ← instantiateMVars e
  match e with
  | .fvar id => return s!".nm \"{(← id.getUserName)}\""
  | .sort _ => return ".nm \"Type\""
  | _ =>
    let fn := e.getAppFn
    let args := e.getAppArgs
    match fn with
    | .const n _ =>
      let h := shortHead n
      if args.isEmpty then
        return s!".nm \"{h}\""
      else
        let as ← args.mapM lty
        let inner := ", ".intercalate as.toList
        match h, args.size with
        | "Option", 1 => return s!".opt ({as[0]!})"
        | "List", 1 => return s!".lst ({as[0]!})"
        | "Array", 1 => return s!".arr ({as[0]!})"
        | _, _ => return s!".app \"{h}\" [{inner}]"
    | .fvar id => return s!".app \"{(← id.getUserName)}\" [{", ".intercalate (← args.mapM lty).toList}]"
    | _ => return s!".nm \"<{e.ctorName}>\""

def site (env : Environment) (n : Name) : String :=
  match env.getModuleIdxFor? n with
  | some idx =>
    let m := env.header.moduleNames[idx.toNat]!.toString
    let file := (m.splitOn ".").getLast!
    match declRangeExt.find? env n with
    | some r => s!"{file}.lean:{r.range.pos.line}"
    | none => s!"{file}.lean"
  | none => "<local>"

/-- The Lean name as the descriptions spell it: the last component (`Supervision.ObserverMode`
keeps its namespace only when it is not the module's own). -/
def descName (n : Name) : String := (n.componentsRev.head!.toString)

def describeStructure (n : Name) (info : InductiveVal) (defName : Option String) : MetaM Unit := do
  let env ← getEnv
  let ctor := info.ctors.head!
  let ctorInfo ← getConstInfoCtor ctor
  forallTelescope ctorInfo.type fun xs _ => do
    let params := xs[:info.numParams].toArray
    let fields := xs[info.numParams:].toArray
    let pnames ← params.mapM fun p => do return s!"\"{(← p.fvarId!.getUserName)}\""
    IO.println s!"def {defName.getD (descName n).toLower} : StructDesc where"
    IO.println s!"  leanName := \"{descName n}\""
    IO.println s!"  site := \"{site env n}\""
    IO.println "  subst := []"
    IO.println s!"  leanParams := [{", ".intercalate pnames.toList}]"
    IO.println "  fields :="
    let mut lines := #[]
    for f in fields do
      let nm ← f.fvarId!.getUserName
      let ty ← lty (← inferType f)
      lines := lines.push s!"\{ leanName := \"{nm}\", leanTy := {ty} }"
    IO.println s!"    [{",\n     ".intercalate lines.toList}]"
    IO.println ""

def describeInductive (n : Name) (info : InductiveVal) (defName : Option String) : MetaM Unit := do
  let env ← getEnv
  IO.println s!"def {defName.getD (descName n).toLower} : InductiveDesc where"
  IO.println s!"  leanName := \"{descName n}\""
  IO.println s!"  site := \"{site env n}\""
  IO.println "  subst := []"
  let mut first := true
  let mut ctorLines := #[]
  for c in info.ctors do
    let ci ← getConstInfoCtor c
    let line ← forallTelescope ci.type fun xs _ => do
      let params := xs[:info.numParams].toArray
      if first then
        let pnames ← params.mapM fun p => do return s!"\"{(← p.fvarId!.getUserName)}\""
        IO.println s!"  leanParams := [{", ".intercalate pnames.toList}]"
        IO.println "  ctors :="
      let args := xs[info.numParams:].toArray
      let mut as := #[]
      for a in args do
        let nm ← a.fvarId!.getUserName
        let ty ← lty (← inferType a)
        as := as.push s!"\{ leanName := \"{nm}\", leanTy := {ty} }"
      let short := (c.toString.splitOn ".").getLast!
      return s!"\{ leanName := \"{short}\", args := [{", ".intercalate as.toList}] }"
    first := false
    ctorLines := ctorLines.push line
  IO.println s!"    [{",\n     ".intercalate ctorLines.toList}]"
  IO.println ""

def describe (n : Name) (defName : Option String := none) : MetaM Unit := do
  let env ← getEnv
  match env.find? n with
  | some (.inductInfo info) =>
    if isStructure env n then describeStructure n info defName
    else describeInductive n info defName
  | some _ => IO.println s!"-- {n}: not an inductive"
  | none => IO.println s!"-- {n}: not found"

/-- `--find Short`: every inductive under `Effect4` whose last component is `Short`, with its
site, so a hand description's `leanName` + `site` can be mapped to one full Lean name. -/
def find (short : String) : MetaM Unit := do
  let env ← getEnv
  let mut hits : Array (Name × String) := #[]
  for (n, ci) in env.constants.map₁.toList do
    if n.getRoot == `Effect4 && (n.componentsRev.head!.toString) == short then
      if let .inductInfo _ := ci then hits := hits.push (n, site env n)
  for (n, s) in hits.qsort (fun a b => a.1.toString < b.1.toString) do
    IO.println s!"{short}\t{n}\t{s}"

/-- `--module Ns a=Full.Name b=Full.Name …`: a whole generated module — the descriptions in
the order given, then `all : List TypeDesc` in that order, the twin list `OCaml5.Avatar.Part`
consumes. The header carries the exact command that regenerates the file. -/
def emitModule (ns : String) (pairs : List (String × Name)) : MetaM Unit := do
  let env ← getEnv
  let args := " ".intercalate (pairs.map fun (d, n) => s!"{d}={n}")
  IO.println "-- GENERATED by src/OCaml5/Tools/Describe.lean from the Lean environment. Do not edit."
  IO.println s!"-- Regenerate: lake env lean -M4096 --run src/OCaml5/Tools/Describe.lean --module {ns} {args}"
  IO.println "import OCaml5.Ml.Reflect"
  IO.println ""
  IO.println s!"namespace {ns}"
  IO.println "open OCaml5.Ml"
  IO.println ""
  for (d, n) in pairs do
    describe n (some d)
  let entries := pairs.map fun (d, n) => (if isStructure env n then ".struct " else ".induct ") ++ d
  IO.println "/-- Every description above, in order. -/"
  IO.println s!"def all : List TypeDesc := [{", ".intercalate entries}]"
  IO.println ""
  IO.println s!"end {ns}"

def main (args : List String) : IO Unit := do
  initSearchPath (← findSysroot)
  let env ← importModules
    #[{ module := `Effect4.Machine.Fibers }, { module := `Effect4.Machine.Stores },
      { module := `Effect4.Machine.Layer }, { module := `Effect4.Machine.Context },
      { module := `Effect4.Machine.Scope }, { module := `Effect4.Machine.Key }] {} 0
  let ctx : Core.Context := { fileName := "<describe>", fileMap := default }
  let act : MetaM Unit :=
    match args with
    | "--find" :: shorts => shorts.forM find
    | "--module" :: ns :: pairs => do
        let ps := pairs.filterMap fun p =>
          match p.splitOn "=" with
          | [d, n] => some (d, n.toName)
          | _ => none
        emitModule ns ps
    | names => (names.map String.toName).forM (describe ·)
  let _ ← (act.run' {}).toIO ctx { env := env }
