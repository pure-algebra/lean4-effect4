import Conform.Effect4.NormalizationInputs
import Conform.Effect4.CompilerControls
import Conform.Effect4.LcnfMl
import Conform.Effect4.LcnfSemantics

/-! A bounded production checkpoint for normalization, canonical construction and generator
merging. The two interpreters and compiled OCaml consume the same named input selection.
Primitives are explicit target assumptions; exhaustion remains an unresolved frontier.

**The selection.** `selection` names every fixture once, with the lanes it takes part in: the
source interpreter, the target evaluator and compiled OCaml. A fixture's name is its
declaration and the names of its inputs, never its place in a list. The driver writes the
selection to `selection.json` before it evaluates anything, and both of its reports name that
file's digest as their input. The runner (`scripts/check-conform.py`) takes its expectations
from the selection, never from a report that came back.

The name fixtures (`Conform.Effect4.LoweringNames`) take part on the target side and in the
compiled OCaml only. Their expected answers are the compiled Lean definitions' own. The source
interpreter is not their reference: it refuses a primitive applied to fewer arguments than it
takes, and one fixture is such an application. -/
namespace Conform.Effect4.Normalization
open Lean Compiler LCNF Conform Conform.Lcnf
open _root_.Effect4.Program NormalizationInputs

/-- The input types, each under a stable name. -/
def vectors : List (String × Ty) := [("never", .never), ("unit", .unit), ("nat", .nat),
  ("bool", .bool), ("handle-utf8", .handle "é🙂"), ("handle-ascii", .handle "Resource"),
  ("union-nat-never", .union .nat .never), ("option-union", .option (.union .nat .never)),
  ("list-union", .list (.union .bool .nat)),
  ("prod-union-string", .prod (.union .nat .nat) .string),
  ("union-nested", .union .bool (.union .nat .bool)),
  ("except-union", .except .string (.union .nat .never)), ("fiber", .fiberOf .nat .string)]

def roots : Array Name := #[``Ty.key, ``Ty.normalize, ``canonicalRaw, ``mergeColumns]

/-- The profile of the run. The evaluation, the report's pins and the selection read these. -/
def sourceFuel : Nat := 20000
def targetFuel : Nat := 40000
def word : Target.Word := { bits := 63 }
def phase : String := "mono"
def pins : List Pin := [⟨"input-mode", "persisted-mono"⟩, ⟨"source-fuel", toString sourceFuel⟩,
  ⟨"target-fuel", toString targetFuel⟩, ⟨"word-bits", toString word.bits⟩]

def optionS (f : α → Value) : Option α → Value
  | none => .ctor ``Option.none #[]
  | some a => .ctor ``Option.some #[f a]
def optionT (f : α → Target.TValue) : Option α → Target.TValue
  | none => .ctorV "None" #[]
  | some a => .ctorV "Some" #[f a]

def mergeS (x : Option (Option Ty × Ty × List (Nat × Nat))) : Value :=
  optionS (fun (a, e, rs) => .ctor ``Prod.mk #[optionS Conform.Effect4.LcnfSemantics.tyValue a,
    .ctor ``Prod.mk #[Conform.Effect4.LcnfSemantics.tyValue e, Value.ofList (rs.map fun (n, s) =>
      .ctor ``Prod.mk #[.nat n, .nat s])]]) x

def mergeT (x : Option (Option Ty × Ty × List (Nat × Nat))) : Target.TValue :=
  optionT (fun (a, e, rs) => .tupleV #[optionT Conform.Effect4.LcnfMl.tyT a,
    .tupleV #[Conform.Effect4.LcnfMl.tyT e, Target.TValue.ofList (rs.map fun (n, s) => .tupleV #[.int n, .int s])]]) x

structure Fixture where
  /-- The stable name: the declaration's short name, then the names of its inputs. -/
  name : String
  decl : Name
  sourceArgs : Array Value
  targetArgs : Array Target.TValue
  sourceExpected : Value
  targetExpected : Target.TValue
  /-- Actual emitted OCaml call and independently computed Lean observation. -/
  mlCheck : String

def fixtures : Array Fixture := Id.run do
  let mut out := #[]
  let g := OCaml5.Lcnf.globalName
  for (v, t) in vectors do
    let ml := (Conform.Effect4.LcnfMl.tyT t).render
    out := out.push ⟨s!"key/{v}", ``Ty.key, #[Conform.Effect4.LcnfSemantics.tyValue t], #[Conform.Effect4.LcnfMl.tyT t],
      Value.ofNatList t.key, Conform.Effect4.LcnfMl.natListT t.key,
      s!"{g ``Ty.key} ({ml}) = [{String.intercalate ";" (t.key.map toString)}]"⟩
    for (short, decl) in [("normalize", ``Ty.normalize), ("canonical", ``canonicalRaw)] do
      out := out.push ⟨s!"{short}/{v}", decl, #[Conform.Effect4.LcnfSemantics.tyValue t], #[Conform.Effect4.LcnfMl.tyT t],
        Conform.Effect4.LcnfSemantics.tyValue t.normalize, Conform.Effect4.LcnfMl.tyT t.normalize,
        s!"{g decl} ({ml}) = ({(Conform.Effect4.LcnfMl.tyT t.normalize).render})"⟩
  for (va, a) in vectors.take 8 do
    for (vb, b) in vectors.take 8 do
      let result : Option (Option Ty × Ty × List (Nat × Nat)) := mergeColumns a b
      let expected := match result with
        | none => "None"
        | some (answer, error, rows) =>
          let ans := match answer with | none => "None" | some t => s!"Some ({(Conform.Effect4.LcnfMl.tyT t).render})"
          s!"Some ({ans}, ({(Conform.Effect4.LcnfMl.tyT error).render}, [{String.intercalate ";" (rows.map fun (pair : Nat × Nat) => s!"({pair.1},{pair.2})")}]))"
      out := out.push ⟨s!"merge/{va}/{vb}", ``mergeColumns,
        #[Conform.Effect4.LcnfSemantics.tyValue a, Conform.Effect4.LcnfSemantics.tyValue b], #[Conform.Effect4.LcnfMl.tyT a, Conform.Effect4.LcnfMl.tyT b], mergeS result, mergeT result,
        s!"{g ``mergeColumns} ({(Conform.Effect4.LcnfMl.tyT a).render}) ({(Conform.Effect4.LcnfMl.tyT b).render}) = ({expected})"⟩
  return out

/-! ## The selection -/

/-- One fixture of the selection: its stable name and the lanes it takes part in. -/
structure Selected where
  name : String
  source : Bool := false
  target : Bool := false
  host : Bool := false

/-- The requested selection, in the order the lanes run it. One list names every fixture. A
normalization fixture takes part in all three lanes. A builtin control and a name fixture run
on the target evaluator and in compiled OCaml: the source interpreter has no expression of a
builtin's form, and it refuses an under-applied primitive. -/
def selection : Array Selected :=
  (fixtures.map fun f => { name := f.name, source := true, target := true, host := true }) ++
  (CompilerControls.hostChecks.map fun (id, _, _) =>
    ({ name := id, target := true, host := true } : Selected)).toArray ++
  (CompilerControls.nameChecks.map fun (id, _, _) =>
    ({ name := id, target := true, host := true } : Selected)).toArray

/-- The names of one lane, in the selection's order. -/
def lane (pick : Selected → Bool) : Array String := (selection.filter pick).map (·.name)

/-- The mutations of the source interpreter, and the one of the target program's support. -/
def sourceMutants : Array Conform.Effect4.LcnfSemantics.Mutant :=
  #[.natLitShift, .boolArmsSwapped]
def supportMutation : String := "support-body"
def controls : Array String := sourceMutants.map (·.label) ++ #[supportMutation]

-- A name is one fixture. It stands in a line of `expected.txt` and in an OCaml format string,
-- so it holds letters, digits, `/`, `-` and `_` only.
#guard (selection.map (·.name)).toList.eraseDups.length == selection.size
#guard selection.all fun s => !s.name.isEmpty &&
  s.name.all fun c => c.isAlphanum || c == '/' || c == '-' || c == '_'
#guard controls.toList.eraseDups.length == controls.size
-- The first observation that reads the UTF-8 helper, by name (`scripts/check-conform.py`).
#guard (lane (·.host)).contains "key/handle-utf8" && (lane (·.host)).contains "names/mulCap"

/-- The selection as the runner reads it (`read_selection` in `scripts/check-conform.py`). -/
def selectionJson : Json :=
  let lanes (s : Selected) : Array Json :=
    (if s.source then #[Json.str "source"] else #[]) ++
    (if s.target then #[Json.str "target"] else #[]) ++
    (if s.host then #[Json.str "host"] else #[])
  Json.mkObj [
    ("format", "conform-selection-v1"),
    ("tool", "conform.normalization"),
    ("pins", toJson pins),
    ("phase", Json.str phase),
    ("roots", Json.arr (roots.map fun n => Json.str n.toString)),
    ("fixtures", Json.arr (selection.map fun s =>
      Json.mkObj [("name", Json.str s.name), ("lanes", Json.arr (lanes s))])),
    ("controls", Json.arr (controls.map Json.str))]

/-- A lane's rows under the selection's identities: one fixture, one row, named by the
fixture. A lane that answers fewer rows than it has names leaves the report incomplete. -/
def named (rows : Array Row) (names : Array String) : Array Row :=
  (rows.zip names).map fun (row, name) => { row with subject := ⟨"fixture", [name]⟩ }

def fixtureIds (check : String) (names : Array String) : Array CheckId :=
  names.map fun name => ⟨check, ⟨"fixture", [name]⟩⟩

end Conform.Effect4.Normalization

open Lean Conform Conform.Lcnf Conform.Effect4.Normalization

def main (args : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  let out : System.FilePath := args.headD ".lake/conform/normalization"
  IO.FS.createDirAll out
  -- The request first: the selection is on disk before anything is evaluated, and each report
  -- names the digest of the bytes written here.
  let selectionText := selectionJson.pretty ++ "\n"
  IO.FS.writeFile (out / "selection.json") selectionText
  let selected : Input :=
    ⟨"selection", (_root_.Effect4.Store.sha256 selectionText.toUTF8.data.toList).hex⟩
  let imports := #[`Conform.Effect4.NormalizationInputs, `Conform.Effect4.LoweringNames]
  let env ← importModules (imports.map fun module => { module }) {} 0
  let action : CoreM UInt32 := do
    let source ← walkClosure roots { primitive := fun n => (Conform.Effect4.LcnfSemantics.tyPrims.lookup? n).isSome, cap := 4000 }
    let names := source.decls.map (·.name) ++ source.primitives ++ source.missing.map (·.name)
    let ctx := Ctx.ofClosure (← getEnv) names Conform.Effect4.LcnfSemantics.tyPrims
    let cases := fixtures.map fun f => ({
        label := f.name
        decl := f.decl
        args := f.sourceArgs
        expected := f.sourceExpected } : Case)
    let sourceRows := named (differential ctx sourceFuel "normalization.source" cases)
      (cases.map (·.label))
    let nameRoots := Conform.Effect4.CompilerControls.nameRoots
    let translated ← OCaml5.Lcnf.translateClosure (roots ++ nameRoots) 4000 {} {}
    -- No binder of a translated declaration hides a name its body means as free.
    let captures := OCaml5.Lcnf.hygieneProblems translated.decls
    unless captures.isEmpty do
      throwError "name hygiene: {captures}"
    -- The target program is the emitted module's: the prelude's support functions, then the
    -- declarations. A body the reader refuses stops the checkpoint here.
    let target ← match Conform.Effect4.LcnfMl.assemble translated.decls (word := word) with
      | .ok program => pure program
      | .error why => throwError "target program: {why}"
    let nameCases : Array Target.TCase :=
      (Conform.Effect4.LoweringNames.entries.filterMap fun (name, args) =>
        (Conform.Effect4.LoweringNames.leanAnswer name args).map fun answer => ({
          label := Conform.Effect4.CompilerControls.nameId name
          bind := OCaml5.Lcnf.globalName name
          args := args.toArray.map fun a => Target.TValue.int (Int.ofNat a)
          expected := .value (.int (Int.ofNat answer)) } : Target.TCase)).toArray
    unless nameCases.size == Conform.Effect4.LoweringNames.entries.length do
      throwError "name fixtures: an entry has no Lean answer"
    let targetCases := (fixtures.map fun f => ({
        label := f.name
        bind := OCaml5.Lcnf.globalName f.decl
        args := f.targetArgs
        expected := .value f.targetExpected } : Target.TCase)) ++ nameCases
    let targetRows := named (Target.differentialT target targetFuel "normalization.target" targetCases)
      (targetCases.map (·.label))
    -- The builtin controls on the evaluator too: each expression in the assembled program,
    -- against what the control expects, a value or a named exception.
    let host := Conform.Effect4.CompilerControls.hostChecks
    let controlRows := host.toArray.map fun (id, expression, expected) =>
      let subject : Subject := ⟨"fixture", [id]⟩
      match Conform.Effect4.CompilerControls.onTarget target targetFuel expression expected with
      | (observed, some wanted) =>
        Target.judgeT "normalization.target" subject id targetFuel observed wanted
      | (_, none) =>
        Row.refused "normalization.target" subject s!"{id}: the expected expression gave no value"
    let gen ← (OCaml5.Lcnf.generate translated.realTypes translated.mentioned {} {}).run'
    unless gen.unknown.isEmpty do
      throwError "target types: {gen.unknown}"
    unless translated.missing.isEmpty && translated.frontier.isEmpty && translated.todos.isEmpty do
      throwError "target closure missing={translated.missing} frontier={translated.frontier} holes={translated.todos}"
    let emitted ← IO.ofExcept (OCaml5.Lcnf.emit translated.decls)
    let module : OCaml5.Ml.Module := { name := "normalization", items := [gen.item, .blank] ++ emitted }
    -- One observation of the compiled module: its name and `PASS`, or its name and `FAIL` and
    -- the end of the run.
    let observe (id condition : String) : String :=
      s!"let () = if ({condition}) then Printf.printf \"{id}\\tPASS\\n\" else (Printf.eprintf \"{id}\\tFAIL\\n\"; exit 1)"
    let checks := fixtures.toList.map fun f => observe f.name f.mlCheck
    -- A control that expects a value compares; one that expects an exception catches it by
    -- its name, and any answer or any other exception fails the observation.
    let checks := checks ++ host.map fun (id, expression, expected) =>
      let rendered := OCaml5.Ml.renderExpr 0 expression
      observe id (match expected with
        | .value e => s!"({rendered}) = ({OCaml5.Ml.renderExpr 0 e})"
        | .raises exn => s!"match ({rendered}) with _ -> false | exception {exn} -> true")
    -- The name fixtures as the emitted module calls them, against Lean's own answers.
    let checks := checks ++ Conform.Effect4.CompilerControls.nameChecks.map fun (id, call, answer) =>
      observe id s!"({call}) = ({answer})"
    unless checks.length == (lane (·.host)).size do
      throwError "the compiled module has {checks.length} observations, the selection {(lane (·.host)).size}"
    IO.FS.writeFile (out / "normalization.ml") (OCaml5.Ml.render module ++ "\n" ++ String.intercalate "\n" checks ++ "\n")
    IO.FS.writeFile (out / "expected.txt")
      (String.join ((lane (·.host)).toList.map fun id => s!"{id}\tPASS\n"))
    let mutationRows := sourceMutants.map fun mutant =>
      let altered := Conform.Effect4.LcnfSemantics.mutateCtx mutant ctx
      let observed := differential altered sourceFuel "mutation" cases
      let subject : Subject := ⟨"mutation", [mutant.label]⟩
      if observed.any (·.outcome == .counterexample) then
        Row.pass "normalization.control" subject .tested "the mutated source fails a selected comparison"
      else Row.refused "normalization.control" subject "mutation did not produce a counterexample"
    -- A wrong support body must reach the target evaluator: the program assembled from an
    -- altered `lcnf_nat_mul` fails a comparison that the name fixtures select.
    let squaring := OCaml5.Lcnf.support.map fun s =>
      if s.name == "lcnf_nat_mul" then { s with body := .binop "*" (.var "a") (.var "a") } else s
    let supportSubject : Subject := ⟨"mutation", [supportMutation]⟩
    let supportRow :=
      match Conform.Effect4.LcnfMl.assemble translated.decls (word := word) (support := squaring) with
      | .error why =>
        Row.refused "normalization.control" supportSubject s!"the altered program did not assemble: {why}"
      | .ok altered =>
        if (Target.differentialT altered targetFuel "mutation" nameCases).any (·.outcome == .counterexample) then
          Row.pass "normalization.control" supportSubject .tested "the altered support body fails a selected comparison"
        else Row.refused "normalization.control" supportSubject "the altered support body produced no counterexample"
    let mutationRows := mutationRows.push supportRow
    -- The plan is the selection's, lane by lane. A lane that answers another set of fixtures
    -- leaves the report incomplete.
    let required := fixtureIds "normalization.source" (lane (·.source)) ++
      fixtureIds "normalization.target" (lane (·.target)) ++
      controls.map fun c => ⟨"normalization.control", ⟨"mutation", [c]⟩⟩
    let report : Report := {
      tool := "conform.normalization"
      expected := required.size
      required
      rows := sourceRows ++ targetRows ++ controlRows ++ mutationRows
      pins := ⟨"lean", Lean.versionString⟩ :: pins
      inputs := [selected] }
    let validity : Manifest := { leanVersion := Lean.versionString, phase, roots, imports, closure := source }
    IO.FS.writeFile (out / "closure.json") (validity.toJson.pretty ++ "\n")
    let vc ← ({ validity.toReport with inputs := [selected] }).emit (out / "validity.json")
    let code ← report.emit (out / "normalization.json")
    for row in report.failures do IO.eprintln s!"{row.subject.render}: {row.message}"
    return max vc code
  let (code, _) ← action.toIO { fileName := "<normalization>", fileMap := default } { env }
  return code
