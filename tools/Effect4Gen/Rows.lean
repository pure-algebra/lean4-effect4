import Lean
import Tools.GeneratedStamp
import Effect4.Program.Native

/-!
# Effect4Gen.Rows — the native rows as authoring wrappers, from the row table

Reads `NativeOp.all` (`Program/Native.lean`) for each row's spelling, shape and request, and
the `NativeOp` constructor declarations for the parameters a row carries (`refUpdate f`),
and emits:

* group `Rows` → `src/Effect4/Program/Authoring/Rows.lean`: one `Src NativeOp` wrapper per
  row, named as the printed image spells it (`Ref.make`, `Deferred.await`), its request
  built as the shape says: nothing for a unit request, one term for a call, a `pair` of two
  for a tuple call. The wrapper is the operation on that request and nothing else, a
  `perform`, the one invocation form: the row's kind selects the route at the compile, so an
  authored row lands in the printer's image whatever its kind (DI-89's native half).
* group `RowsLaws` → `src/Effect4/Laws/Program/Authoring/Rows.lean`: the scope lemma of
  every wrapper, one application of `perform_scoped`.

    lake env lean -M 4096 --run tools/Effect4Gen/Rows.lean --group Rows
      --imports Effect4.Program.Authoring.Lifts --out src/Effect4/Program/Authoring/Rows.lean
      --append tools/Effect4Gen/guards/rows.lean
-/

open Lean Meta Elab
open Effect4.Program

namespace Effect4Gen.Rows

def shortName (n : Name) : String := n.componentsRev.head!.toString

def srcOf (e : Expr) : MetaM String := do
  withOptions (fun o => (o.setBool `pp.fullNames true).setBool `pp.universes false) do
    return toString (← ppExpr e)

/-- A constructor's parameters, by reflection: name and type text. -/
def ctorParams (c : Name) : MetaM (List (String × String)) := do
  let ci ← getConstInfoCtor c
  forallBoundedTelescope ci.type (ci.numParams + ci.numFields) fun xs _ => do
    let mut acc := []
    for x in xs[ci.numParams:] do
      let ty ← inferType x
      acc := acc ++ [((← x.fvarId!.getDecl).userName.toString, ← srcOf ty)]
    return acc

/-- One row's wrapper and lemma, or none when it has no spelling (the host row). -/
structure Emitted where
  namespaceParts : List String
  defName : String
  wrapper : String
  lemma : String
  receipt : String

/-- The request's parameters and how they build the request term. -/
def requestOf (row : Row) : List String × String :=
  if row.request == .unit then ([], "unit")
  else match row.shape, row.request with
    | .tupleCall, .prod _ _ => (["x0", "x1"], "(app \"pair\" [x0, x1])")
    | _, _ => (["request"], "request")

def emitOne (op : NativeOp) (params : List (String × String)) : Option Emitted :=
  let row := op.row
  if row.spelling.isEmpty then none else
  let parts := row.spelling.splitOn "."
  let defName := parts.getLast!
  let nsParts := parts.dropLast
  let (reqParams, reqTerm) := requestOf row
  let ctorArgs := String.intercalate " " (params.map (·.1))
  let opTerm := if params.isEmpty then s!".{row.name}" else s!"(.{row.name} {ctorArgs})"
  let paramText := String.intercalate " " (
    (params.map fun (n, t) => s!"({n} : {t})") ++
    (if reqParams.isEmpty then [] else [s!"({String.intercalate " " reqParams} : TermSrc)"]))
  let header := if paramText.isEmpty then s!"def {defName} : Src NativeOp :=" else s!"def {defName} {paramText} : Src NativeOp :="
  -- one invocation form; the row's kind selects the route at the compile
  let lift := "perform"
  let wrapper := s!"/-- `{row.spelling}` (`{row.cite}`). -/\n{header}\n  {lift} {opTerm} {reqTerm}\n"
  -- the lemma
  let hyps := reqParams.zipIdx.map fun (x, i) => s!"(h{i} : {x}.Scoped)"
  let implicitReq := if reqParams.isEmpty then "" else s!"\{{String.intercalate " " reqParams} : TermSrc} "
  let ctorParamText := String.intercalate " " (params.map fun (n, t) => s!"({n} : {t})")
  let lemmaParams := (if ctorParamText.isEmpty then "" else ctorParamText ++ " ") ++ implicitReq ++ String.intercalate " " hyps
  let app := String.intercalate " " ([defName] ++ params.map (·.1) ++ reqParams)
  let proof := match reqParams with
    | [] => s!"{lift}_scoped _ unit_scoped"
    | [_] => s!"{lift}_scoped _ h0"
    | _ => s!"{lift}_scoped _ (app_scoped \"pair\" (TermSrc.Scoped_cons h0 (TermSrc.Scoped_cons h1 TermSrc.Scoped_nil)))"
  let lemma := s!"theorem {defName}_scoped {lemmaParams} :\n    ({app}).Scoped :=\n  {proof}\n"
  let lemma := lemma.replace "theorem " "theorem " |>.replace "_scoped  :" "_scoped :"
  some { namespaceParts := nsParts, defName, wrapper, lemma,
         receipt := "Effect4.Program.Authoring." ++ String.intercalate "." (nsParts ++ [defName]) }

/-- Group the emitted rows by namespace, in first-seen order. -/
def grouped (rows : List Emitted) : List (List String × List Emitted) :=
  rows.foldl (init := []) fun acc r =>
    match acc.findIdx? (·.1 == r.namespaceParts) with
    | some i => acc.set i (acc[i]!.1, acc[i]!.2 ++ [r])
    | none => acc ++ [(r.namespaceParts, [r])]

def render (rows : List Emitted) (pick : Emitted → String) : String :=
  String.intercalate "\n" <| (grouped rows).map fun (ns, rs) =>
    let body := String.intercalate "\n" (rs.map pick)
    if ns.isEmpty then body
    else s!"namespace {String.intercalate "." ns}\n\n{body}\nend {String.intercalate "." ns}\n"

def emitAll : MetaM (List Emitted) := do
  let mut out := []
  for op in NativeOp.all do
    let ctorName := (`Effect4.Program.NativeOp).str op.row.name
    let params ← if (← getEnv).contains ctorName then ctorParams ctorName else pure []
    if let some e := emitOne op params then
      if !(out.any fun (o : Emitted) => o.receipt == e.receipt) then out := out ++ [e]
  return out

structure Args where
  group : String := "Rows"
  imports : List String := []
  out : Option String := none
  headerOut : Option String := none
  append : Option String := none
  types : List String := []

partial def parseArgs : List String → Args → Except String Args
  | [], a => .ok a
  | "--group" :: g :: rest, a => parseArgs rest { a with group := g }
  | "--imports" :: i :: rest, a => parseArgs rest { a with imports := (i.splitOn ",").filter (· != "") }
  | "--out" :: o :: rest, a => parseArgs rest { a with out := some o }
  | "--header-out" :: o :: rest, a => parseArgs rest { a with headerOut := some o }
  | "--append" :: p :: rest, a => parseArgs rest { a with append := some p }
  | "--" :: rest, a => parseArgs rest a
  | t :: rest, a =>
    if t.startsWith "--" then .error s!"unknown option {t}" else parseArgs rest { a with types := a.types ++ [t] }

def run (args : Args) : MetaM (Array String) := do
  let outPath := (args.headerOut.orElse (fun _ => args.out) |>.getD "<stdout>").replace "\\" "/"
  let head := "lake env lean -M 4096 --run tools/Effect4Gen/Rows.lean --group " ++ args.group
    ++ " --imports " ++ String.intercalate "," args.imports ++ " --out " ++ outPath
    ++ (match args.append with | some p => " --append " ++ p.replace "\\" "/" | none => "")
  let mut lines : Array String := #[
    "-- GENERATED by tools/Effect4Gen/Rows.lean from NativeOp.all (Program/Native.lean) and the NativeOp declarations. Do not edit.",
    "-- Regenerate (tools/Effect4Gen/Driver.lean runs this for every group; --verify refuses a diff):",
    "--   " ++ head ++ (if args.types.isEmpty then "" else " -- " ++ String.intercalate " " args.types)]
  if let some p := args.append then
    lines := lines.push s!"-- Acceptance guards appended verbatim from: {p.replace "\\" "/"}"
  lines := lines ++ (args.imports.map fun i => s!"import {i}").toArray
  lines := lines ++ #["", "set_option autoImplicit false", "", "namespace Effect4.Program.Authoring", "", "open Effect4.Program", ""]
  let rows ← emitAll
  match args.group with
  | "Rows" => lines := lines.push (render rows (·.wrapper))
  | "RowsLaws" => lines := lines.push (render rows (·.lemma))
  | g => throwError "unknown group {g}: Rows or RowsLaws"
  lines := lines ++ #["/-! ## Receipts -/", ""]
  for r in rows do
    lines := lines.push s!"#print axioms {r.receipt}{if args.group == "RowsLaws" then "_scoped" else ""}"
  lines := lines ++ #["", "end Effect4.Program.Authoring", ""]
  if let some p := args.append then
    let txt ← IO.FS.readFile p
    lines := lines ++ (txt.splitOn "\n").toArray.map (·.replace "\r" "")
  return lines

end Effect4Gen.Rows

open Effect4Gen.Rows in
def main (argv : List String) : IO Unit := do
  let args ← match parseArgs argv {} with
    | .ok a => pure a
    | .error e => throw (IO.userError e)
  if args.imports.isEmpty then
    throw (IO.userError "--imports names the modules the emitted file imports; none given")
  Lean.initSearchPath (← Lean.findSysroot)
  let env ← Lean.importModules (args.imports.map fun i => { module := i.toName }).toArray {} 0
  let ctx : Core.Context := { fileName := "<gen>", fileMap := default }
  let act : MetaM Unit := do
    let lines ← run args
    let stamp := Tools.GeneratedStamp.note "tools/Effect4Gen/Rows.lean"
    let text := "-- " ++ stamp ++ "\n" ++ String.intercalate "\n" lines.toList ++ "\n"
    match args.out with
    | some p => IO.FS.writeFile p text
    | none => IO.println text
  let _ ← (act.run' {}).toIO ctx { env := env }
