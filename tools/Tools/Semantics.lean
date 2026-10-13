import ProofGraph.Registry
import Tools.SemanticsDisplay
import Tools.GeneratedStamp
import Effect4.Laws.Auto.Semantics
import ProofGraph.Axioms
import ProofGraph.Plan

/-! A measured report of selected claims. English claim-to-witness associations are authored;
ProofGraph checks their actual propositions. This library neither proves the descriptions nor
runs the whole-library trust gate. No main here: producers and refusal controls share it. -/
namespace Tools.Semantics
open Lean Meta Effect4.Laws.Auto

/-- One parsed row, retaining the register's attack and repair history verbatim. -/
structure CounterexampleEntry where
  id : String
  status : String
  row : String
deriving Inhabited, BEq

structure Registers where
  counterexamples : Array CounterexampleEntry := #[]
  decisions : Array (Nat × String) := #[]
deriving Inhabited

/-- Table separators inside escaped text or backtick spans are not columns. Runs of backticks
are matched by length so even a quoted single backtick does not end a double-backtick span.
The registers use whitespace-delimited columns; inline absolute values such as |n| stay text. -/
private def tableCells (line : String) : Array String := Id.run do
  let mut cells : Array String := #[]
  let mut cell := ""
  let mut fence := 0
  let mut ticks := 0
  let mut escaped := false
  let chars := line.toList.toArray
  for (c, i) in chars.toList.zipIdx do
    if escaped then
      cell := cell.push c
      escaped := false
    else if c == '\\' then
      escaped := true
      cell := cell.push c
    else if c == '`' then
      ticks := ticks + 1
      cell := cell.push c
    else
      if ticks > 0 then
        if fence == 0 then fence := ticks
        else if fence == ticks then fence := 0
        ticks := 0
      let separator := (i == 0 || (chars[i-1]?.getD ' ').isWhitespace) &&
        (i+1 == chars.size || (chars[i+1]?.getD ' ').isWhitespace)
      if c == '|' && fence == 0 && separator then
        cells := cells.push cell.trimAscii.toString
        cell := ""
      else cell := cell.push c
  cells := cells.push cell.trimAscii.toString
  return (cells.toList.drop 1 |>.dropLast).toArray

private def registerId (id : String) : Bool :=
  match (id.splitOn "-").reverse with
  | digits :: "CE" :: domain =>
    match domain.reverse with
    | "E4" :: parts =>
      !parts.isEmpty && parts.all (fun part => !part.isEmpty && part.toList.all (fun c =>
        ('A' ≤ c && c ≤ 'Z') || ('0' ≤ c && c ≤ '9'))) &&
        digits.length == 3 && digits.toList.all (fun c => '0' ≤ c && c ≤ '9')
    | _ => false
  | _ => false

private def statuses := ["SEEDED", "PINNED", "RESERVED", "MOVED", "REPAIRED", "RETIRED"]

/-- Parse only live register rows. Collect every malformed or duplicate row before returning. -/
def parseRegisters (counterexamplesText decisionsText : String) : Except (Array String) Registers := Id.run do
  let mut errors : Array String := #[]
  let mut result : Registers := {}
  for (line, i) in counterexamplesText.splitOn "\n" |>.zipIdx do
    if line.startsWith "| `E4-" then
      let cells := tableCells line
      let rawId := cells[0]?.getD ""
      let id := rawId.replace "`" ""
      let status := (((cells[1]?.getD "").splitOn " ").head!.splitOn ";").head!
      if cells.size < 3 || !rawId.endsWith "`" || !registerId id || !statuses.contains status then
        errors := errors.push s!"counterexamples:{i+1}: malformed register row {id}"
      else if result.counterexamples.any (·.id == id) then
        errors := errors.push s!"counterexamples:{i+1}: duplicate id {id}"
      else result := { result with counterexamples := result.counterexamples.push { id, status, row := line } }
  for (line, i) in decisionsText.splitOn "\n" |>.zipIdx do
    if line.startsWith "| " then
      let cells := tableCells line
      if let some row := (cells[0]?.getD "").toNat? then
        let who := cells[4]?.getD ""
        if cells.size != 6 || who.isEmpty then
          errors := errors.push s!"decisions:{i+1}: malformed decision row {row}"
        else if result.decisions.any (·.1 == row) then
          errors := errors.push s!"decisions:{i+1}: duplicate row {row}"
        else result := { result with decisions := result.decisions.push (row, who) }
  return if errors.isEmpty then .ok result else .error errors

private def nonblank (s : String) : Bool := !s.trimAscii.toString.isEmpty

def roleName (r : Role) : String := match r with
  | .inversion => "inversion" | .canonicalForms => "canonicalForms"
  | .weakening => "weakening" | .substitution => "substitution"
  | .progress => "progress" | .preservation => "preservation"
  | .monotonicity => "monotonicity" | .transitivity => "transitivity"
  | .antisymmetry => "antisymmetry" | .decidability => "decidability"
  | .adequacy => "adequacy" | .simulation => "simulation"
  | .compatibility => "compatibility" | .fundamentalProperty => "fundamentalProperty"

/-! ## The report as data

`buildReport` measures once and returns a `Report`. Its JSON (`Report.toJson`, schema eight) and its
document (`Report.document`, `Tools/SemanticsDocument.lean`) are both read from this value, so no
output parses another. -/

/-- A declaration as the report shows it: its printed statement, the axioms it reaches and the
planned goals it rests on, both sorted by name, and its docstring, the author's explanation. -/
structure DeclarationEntry where
  name : Name
  module : Name
  levels : List Name
  statement : String
  axioms : List Name
  restsOn : List Name
  doc : Option String := none
  deriving Inhabited

/-- No axiom outside the semantic ceiling. `buildReport` refuses a declaration that reaches one, so
a report's entries all answer yes; the field stays in the JSON as the check it states. -/
def DeclarationEntry.withinCeiling (d : DeclarationEntry) : Bool :=
  (ProofGraph.disallowedAxioms d.axioms.toArray).isEmpty

/-- A register row that a claim cites, with the refuting theorem when the row refutes the claim. -/
structure RegisterRow where
  id : String
  registerStatus : String
  record : String
  witness : Option DeclarationEntry := none
  deriving Inhabited

/-- A claim's evidence, derived from its pointer (decisions row 203), never authored. -/
inductive Evidence where
  /-- the pointer is a planned goal: the status `goal` (decisions row 366, point 7: one word for a
  planned goal, on every page and in the report) -/
  | goal (goal : DeclarationEntry)
  /-- a theorem that rests on planned goals (its `restsOn`) -/
  | modulo (witness : DeclarationEntry)
  | proved (witness : DeclarationEntry)
  | refuted (row : RegisterRow)
  | absent (reason : String)
  | assumed (source reason : String)
  deriving Inhabited

/-- The evidence's word in the report. -/
def Evidence.tag : Evidence → String
  | .goal _ => "goal" | .modulo _ => "modulo" | .proved _ => "proved"
  | .refuted _ => "refuted" | .absent _ => "absent" | .assumed _ _ => "assumed"

/-- The declaration the evidence prints: the goal, the witness, or the refuting theorem. -/
def Evidence.declaration? : Evidence → Option DeclarationEntry
  | .goal d | .modulo d | .proved d => some d
  | .refuted row => row.witness
  | .absent _ | .assumed _ _ => none

/-- A registry claim with its derived evidence and the register rows that contest it. -/
structure ClaimEntry where
  claim : Claim
  evidence : Evidence
  contestedBy : List RegisterRow
  deriving Inhabited

/-- An applicability decision with the owner its decisions row names. -/
structure CutEntry where
  cut : Cut
  who : String

/-- A plan node as the report shows it (`ProofGraph.Node`, with its kind, module, placement and
statement). -/
structure NodeEntry where
  name : Name
  goal : Bool
  standing : String
  restsOn : List Name
  module : Name
  placement : Option Placement
  statement : String
  axioms : List Name
  nearest : List Name
  lemmas : Nat
  definitions : Nat
  /-- the node's docstring: for a planned goal, why its proof waits -/
  doc : Option String := none
  deriving Inhabited

/-- A requirement with its derived status, its top and placed nodes with theirs, and its next goals. -/
structure RequirementEntry where
  requirement : Requirement
  proved : Bool
  top : List (Name × String)
  placed : List (Name × String)
  next : List Name
  deriving Inhabited

/-- The plan section (`ProofGraph.Plan`). -/
structure PlanEntry where
  requirements : List RequirementEntry
  nodes : List NodeEntry
  next : List Name
  /-- the goals that no requirement reaches -/
  unplacedGoals : List Name
  deriving Inhabited

/-- An acceptance program's stage, as its battery's `Reach` literal states it. -/
structure Stage where
  refused : List (String × String)
  admitted : Bool
  answer : String
  printed : Bool
  readBack : Bool

/-- An acceptance program (decisions row 206): its stage and the requirements it waits on. -/
structure AcceptanceEntry where
  program : Name
  stage : Stage
  waitsOn : List String

/-- An eligible theorem with the concept it is placed at, by a tag or by its module. -/
structure PlacedTheorem where
  name : Name
  module : Name
  concept : String
  tagged : Bool

/-- The placement census: the placed theorems, and the unplaced ones counted by module. -/
structure PlacementEntry where
  declarations : List PlacedTheorem
  unplacedByModule : List (Name × Nat)
  deriving Inhabited

/-- The measured report. -/
structure Report where
  toolchain : String
  roots : List Name
  concepts : List Concept
  claims : List ClaimEntry
  cuts : List CutEntry
  plan : PlanEntry
  acceptance : List AcceptanceEntry
  placement : PlacementEntry
  deriving Inhabited

/-! ## Its JSON (schema eight: six with each declaration's and node's docstring, and a planned
goal's status `goal`, once `wanted`) -/

private def text (s : String) : Json := Lean.toJson s
private def names (ns : List Name) : Json := Lean.toJson (ns.map Name.toString)
private def obj := Json.mkObj

def DeclarationEntry.toJson (d : DeclarationEntry) : Json := obj [
  ("name", text d.name.toString), ("module", text d.module.toString),
  ("levels", names d.levels), ("statement", text d.statement),
  ("axioms", names d.axioms), ("restsOn", names d.restsOn),
  ("withinSemanticAxiomCeiling", Lean.toJson d.withinCeiling),
  ("doc", match d.doc with | some s => text s | none => .null)]

def RegisterRow.toJson (r : RegisterRow) : Json := obj [
  ("id", text r.id), ("registerStatus", text r.registerStatus), ("record", text r.record),
  ("witness", match r.witness with | some d => d.toJson | none => .null)]

def Evidence.toJson : Evidence → Json
  | .goal d => obj [("_tag", text "goal"), ("by", text "goal"), ("goal", d.toJson)]
  | .modulo d => obj [("_tag", text "modulo"), ("by", text "theorem"), ("witness", d.toJson),
      ("restsOn", names d.restsOn)]
  | .proved d => obj [("_tag", text "proved"), ("by", text "theorem"), ("witness", d.toJson),
      ("goal", .null)]
  | .refuted row => obj [("_tag", text "refuted"), ("counterexample", row.toJson)]
  | .absent reason => obj [("_tag", text "absent"), ("reason", text reason)]
  | .assumed source reason => obj [("_tag", text "assumed"), ("source", text source), ("reason", text reason)]

def ClaimEntry.toJson (c : ClaimEntry) : Json := obj [
  ("id", text c.claim.id), ("concept", text c.claim.concept), ("role", text (roleName c.claim.role)),
  ("title", text c.claim.title), ("status", c.evidence.toJson),
  ("contestedBy", Lean.toJson (c.contestedBy.map RegisterRow.toJson)),
  ("literature", Lean.toJson (c.claim.literature.map fun r =>
    obj [("work", text r.work), ("locator", text r.locator), ("relation", text r.relation)]))]

private def nodeStatus (n : Name × String) : Json := obj [("name", text n.1.toString), ("status", text n.2)]

def PlanEntry.toJson (p : PlanEntry) : Json := obj [
  ("requirements", Lean.toJson (p.requirements.map fun r => obj [
    ("id", text r.requirement.id), ("title", text r.requirement.title),
    ("status", text (if r.proved then "proved" else "open")),
    ("openParts", Lean.toJson (r.requirement.openParts.map fun part =>
      obj [("text", text part.text), ("state", text part.state.word), ("on", text part.state.on)])),
    ("top", Lean.toJson (r.top.map nodeStatus)), ("placed", Lean.toJson (r.placed.map nodeStatus)),
    ("next", names r.next)])),
  ("nodes", Lean.toJson (p.nodes.map fun n => obj [
    ("name", text n.name.toString), ("kind", text (if n.goal then "goal" else "theorem")),
    ("status", text n.standing), ("restsOn", names n.restsOn),
    ("module", text n.module.toString),
    ("placement", match n.placement with
      | some p => obj [("concept", text p.concept),
          ("requirement", match p.requirement with | some r => text r | none => .null)]
      | none => .null),
    ("statement", text n.statement), ("axioms", names n.axioms),
    ("doc", match n.doc with | some s => text s | none => .null),
    ("broughtIn", obj [("nearest", names n.nearest),
      ("lemmas", Lean.toJson n.lemmas), ("definitions", Lean.toJson n.definitions)])])),
  ("next", names p.next), ("unplacedGoals", names p.unplacedGoals)]

def AcceptanceEntry.toJson (a : AcceptanceEntry) : Json := obj [
  ("program", text a.program.toString),
  ("stage", obj [
    ("refused", Lean.toJson (a.stage.refused.map fun (part, verdict) =>
      obj [("part", text part), ("verdict", text verdict)])),
    ("admitted", Lean.toJson a.stage.admitted), ("answer", text a.stage.answer),
    ("printed", Lean.toJson a.stage.printed), ("readBack", Lean.toJson a.stage.readBack)]),
  ("waitsOn", Lean.toJson a.waitsOn)]

/-- The tags a concept's claims are counted by. -/
def evidenceTags : List String := ["proved", "modulo", "goal", "refuted", "absent", "assumed"]

/-- The report's producer line and its declared inputs. -/
def producer : String := Tools.GeneratedStamp.note "tools/Drivers/Semantics.lean (make gen-semantics)"
def command : String := "make gen-semantics"
def inputs : List String := ["tools/ProofGraph/Registry.lean", "tools/Tools/Semantics.lean",
  "tools/Drivers/Semantics.lean", "tools/Tools/SemanticsDisplay.lean",
  "tools/Tools/SemanticsDocument.lean", "tools/Tools/Document.lean", "tools/Tools/Document/Json.lean",
  "src/Effect4/Laws/Auto/Semantics.lean",
  "Test/Counterexamples/REGISTER.md", "docs/core/decisions.md", "lean-toolchain"]
/-- The placement universe, in words. -/
def placementUniverse : String :=
  "theorems of the registry's concept-named modules; auxiliary names and planned goals excluded"

def Report.toJson (r : Report) : Json := obj [
  ("format", text "effect4-semantics-report"), ("schemaVersion", Lean.toJson (8 : Nat)),
  ("producer", text producer), ("command", text command), ("inputs", Lean.toJson inputs),
  ("provenance", obj [("toolchain", text r.toolchain), ("roots", names r.roots),
    ("policy", obj [("gate", text "Test/Audit/AxiomGate.lean"),
      ("ceiling", Lean.toJson (["propext", "Quot.sound"] : List String))])]),
  ("concepts", Lean.toJson (r.concepts.map fun concept =>
    let members := r.claims.filter (·.claim.concept == concept.id)
    obj [("id", text concept.id), ("title", text concept.title),
      ("defaultModules", names concept.defaultModules),
      ("counts", obj (("claims", Lean.toJson members.length) :: evidenceTags.map fun tag =>
        (tag, Lean.toJson (members.filter (·.evidence.tag == tag)).length)))])),
  ("claims", Lean.toJson (r.claims.map ClaimEntry.toJson)),
  ("cuts", Lean.toJson (r.cuts.map fun c => obj [("concept", text c.cut.concept),
    ("decisionRow", Lean.toJson c.cut.decisionRow), ("excluded", text c.cut.excluded),
    ("reason", text c.cut.reason), ("who", text c.who)])),
  ("plan", r.plan.toJson),
  ("acceptance", Lean.toJson (r.acceptance.map AcceptanceEntry.toJson)),
  ("placement", obj [
    ("universe", text placementUniverse),
    ("declarations", Lean.toJson (r.placement.declarations.map fun d => obj [
      ("name", text d.name.toString), ("module", text d.module.toString), ("concept", text d.concept),
      ("placement", text (if d.tagged then "tagged" else "inherited"))])),
    ("unplacedCount", Lean.toJson (r.placement.unplacedByModule.foldl (fun total row => total + row.2) 0)),
    ("unplacedByModule", Lean.toJson (r.placement.unplacedByModule.map fun (mod, count) =>
      obj [("module", text mod.toString), ("count", Lean.toJson count)]))])]

/-! ## Measuring it -/

/-- What the report computes once and reads many times: the axioms each constant reaches
(`ProofGraph.AxiomMemo`), and each declaration's printed statement, which a claim's witness and
its plan node both print. -/
structure Memo where
  axioms : IO.Ref ProofGraph.AxiomMemo
  statements : IO.Ref (Std.HashMap Name String)
  /-- the loaded modules' names, computed once: `EnvironmentHeader.moduleNames` builds its array
  on every call -/
  modules : Array Name

/-- The module that declares `name`: `semanticsModule`'s answer, read from the module names
computed once. -/
private def moduleOf (memo : Memo) (env : Environment) (name : Name) : Name :=
  match env.getModuleIdxFor? name with
  | some idx => memo.modules[idx.toNat]!
  | none => env.mainModule

/-- The printed statement of a declaration, printed once. -/
private def statementOf (memo : Memo) (name : Name) : MetaM String := do
  if let some printed := (← memo.statements.get)[name]? then return printed
  let printed ← Display.expression (← getConstInfo name).type
  memo.statements.modify (·.insert name printed)
  return printed

private def declaration (memo : Memo) (name : Name) : MetaM DeclarationEntry := do
  let ci ← getConstInfo name
  let env ← getEnv
  unless (env.getModuleIdxFor? name).isSome do
    throwError "{name}: witness module is not loaded"
  let printed ← statementOf memo name
  -- goals are leaves of the walk (decisions row 203): a theorem that rests on one reaches its
  -- name, never its `sorry`
  let (reached, table) := (ProofGraph.reachedWithGoals env name).run (← memo.axioms.get)
  memo.axioms.set table
  let some (reached, goals) := reached | throwError "{name}: axiom collection exhausted its step budget"
  let axioms := reached.qsort (·.toString < ·.toString)
  let disallowed := ProofGraph.disallowedAxioms axioms
  unless disallowed.isEmpty do throwError "{name}: disallowed axioms {disallowed}"
  return { name, module := moduleOf memo env name, levels := ci.levelParams, statement := printed,
           axioms := axioms.toList, restsOn := (goals.qsort (·.toString < ·.toString)).toList,
           doc := ← findDocString? env name }

private def witness (memo : Memo) (name : Name) : MetaM DeclarationEntry := do
  -- `ProofRef.validate`'s checks at the theorem's own proposition, with the axioms memoized
  let t ← match (← getEnv).find? name with
    | some (.thmInfo t) => pure t
    | some _ => throwError "{name}: not a theorem"
    | none => throwError "Unknown constant `{name}`"
  if t.type.hasMVar || t.type.hasFVar then throwError "{name}: open proposition"
  declaration memo name

private def counterexample (index : Registers) (id : String) : MetaM CounterexampleEntry := do
  let some row := index.counterexamples.find? (·.id == id)
    | throwError "unknown counterexample id {id}"
  unless registerId row.id do throwError "invalid counterexample id {id}"
  unless statuses.contains row.status do throwError "invalid register status for {id}"
  unless nonblank row.row do throwError "missing register context for {id}"
  return row

private def evidence (memo : Memo) (index : Registers) : Pointer → MetaM Evidence
  | .witness name => do
    -- the standing is derived (decisions row 203): an open goal, a theorem that rests on goals,
    -- or a theorem that reaches none
    let d ← witness memo name
    if ProofGraph.isGoal (← getEnv) name then return .goal d
    return if d.restsOn.isEmpty then .proved d else .modulo d
  | .refutedBy id name => do
    let status ← counterexample index id
    if status.status == "RETIRED" then throwError "retired counterexample id {id}"
    if ProofGraph.isGoal (← getEnv) name then throwError "{name}: a refutation is a planned goal"
    let d ← witness memo name
    unless d.restsOn.isEmpty do throwError "{name}: a refutation rests on planned goals"
    return .refuted { id, registerStatus := status.status, record := status.row, witness := some d }
  | .absent reason => do
    unless nonblank reason do throwError "blank absent reason"
    return .absent reason
  | .assumed source reason => do
    unless nonblank source && nonblank reason do throwError "blank assumed source or reason"
    return .assumed source reason

/-- The plan section: the requirements with their derived statuses, every node with its standing,
its placement and what its proof brings in, the edges to its nearest nodes, and the next goals
(`ProofGraph.Plan`). A requirement's nodes are its registry top nodes and the declarations placed
at it (`placed`, decisions row 207). -/
private def planEntry (memo : Memo) (plan : ProofGraph.Plan) (requirements : List Requirement)
    (placed : Array (Name × String)) : MetaM PlanEntry := do
  let env ← getEnv
  let placedAt (r : Requirement) : List Name := (placed.filter (·.2 == r.id)).toList.map (·.1)
  let nodesOf (r : Requirement) : List Name := r.top ++ (placedAt r).filter (!r.top.contains ·)
  let tops := requirements.foldl (init := #[]) fun acc r => acc ++ (nodesOf r).toArray
  let mut nodes : Array NodeEntry := #[]
  for n in plan.nodes do
    nodes := nodes.push {
      name := n.name, goal := ProofGraph.isGoal env n.name,
      standing := n.standing.word, restsOn := n.restsOn.toList, module := moduleOf memo env n.name,
      placement := semanticsAttribute.getParam? env n.name, statement := ← statementOf memo n.name,
      axioms := (n.axioms.qsort (·.toString < ·.toString)).toList, nearest := n.nearest.toList,
      lemmas := n.lemmas, definitions := n.definitions, doc := ← findDocString? env n.name }
  let index : Std.HashMap Name ProofGraph.Node := plan.nodes.foldl (fun m n => m.insert n.name n) {}
  let word (n : Name) : String := ((index[n]?).map (·.standing.word)).getD "missing"
  let reqs : List RequirementEntry := requirements.map fun r =>
    { requirement := r, proved := r.openParts.isEmpty && (nodesOf r).all (word · == "proved"),
      top := r.top.map fun n => (n, word n), placed := (placedAt r).map fun n => (n, word n),
      next := (plan.next (nodesOf r).toArray).toList }
  let next := plan.next tops
  -- a goal no requirement reaches is planned work without a place in the requirements
  let unplaced := (plan.nodes.filter fun n => ProofGraph.isGoal env n.name && !next.contains n.name).map (·.name)
  return { requirements := reqs, nodes := nodes.toList, next := next.toList, unplacedGoals := unplaced.toList }

/-! ## The acceptance programs (decisions row 206)

Each battery of `Test/Dogfood` declares the stage its program reaches (`stage : Reach`, tied to
the measurement by a guard) and the requirements it waits on (`waitsOn`). The report reads both
literals from the battery, so the battery owns them. -/

/-- A list literal's elements, as the elaborator writes `[a, b]`. -/
private def listLit? : Expr → Option (List Expr)
  | .app (.app (.app (.const ``List.cons _) _) hd) tl => (listLit? tl).map (hd :: ·)
  | .app (.const ``List.nil _) _ => some []
  | .mdata _ e => listLit? e
  | _ => none

private def strLit? : Expr → Option String
  | .lit (.strVal s) => some s
  | .mdata _ e => strLit? e
  | _ => none

private def boolLit? : Expr → Option Bool
  | .const ``Bool.true _ => some true
  | .const ``Bool.false _ => some false
  | .mdata _ e => boolLit? e
  | _ => none

/-- A `Test.Dogfood.Reach` literal: the refused parts with their verdicts, and the four stages.
`none` if the value is not such a literal. -/
private def stage? (e : Expr) : Option Stage := do
  let e := e.consumeMData
  guard (e.getAppFn.constName? == some `Test.Dogfood.Reach.mk && e.getAppNumArgs == 5)
  let args := e.getAppArgs
  let refused ← (← listLit? args[0]!).mapM fun pair => do
    let pair := pair.consumeMData
    guard (pair.getAppFn.constName? == some ``Prod.mk && pair.getAppNumArgs == 4)
    return (← strLit? pair.getAppArgs[2]!, ← strLit? pair.getAppArgs[3]!)
  let some answer := args[2]!.consumeMData.constName? | none
  guard (answer.getPrefix == `Test.Dogfood.Answer)
  return { refused, admitted := ← boolLit? args[1]!, answer := answer.getString!,
           printed := ← boolLit? args[3]!, readBack := ← boolLit? args[4]! }

/-- One acceptance program: its stage and the requirements it waits on, read from its battery. -/
private def acceptanceEntry (battery : Name) (requirements : List String) :
    MetaM (Except String AcceptanceEntry) := do
  let env ← getEnv
  let some (.defnInfo stage) := env.find? (battery ++ `stage)
    | return .error s!"acceptance {battery}: no `stage` definition"
  let some (.defnInfo waits) := env.find? (battery ++ `waitsOn)
    | return .error s!"acceptance {battery}: no `waitsOn` definition"
  let some ids := (listLit? waits.value).bind (·.mapM strLit?)
    | return .error s!"acceptance {battery}: `waitsOn` is not a list of string literals"
  for id in ids do
    unless requirements.contains id do
      return .error s!"acceptance {battery}: unknown requirement {id}"
  let some reach := stage? stage.value
    | return .error s!"acceptance {battery}: `stage` is not a `Reach` literal"
  return .ok { program := battery, stage := reach, waitsOn := ids }

/-- Validate and collect all located refusals. No status is accepted from authored input. -/
def buildReport (registry : Registry) (registers : Registers) (toolchain : String) :
    MetaM (Except (Array String) Report) := do
  let env ← getEnv
  let memo : Memo :=
    { axioms := ← IO.mkRef {}, statements := ← IO.mkRef {}, modules := env.header.moduleNames }
  let mut errors : Array String := #[]
  unless nonblank toolchain do errors := errors.push "provenance: blank toolchain"
  let mut ids : List String := []
  let mut defaults : List Name := []
  let mut roots : List Name := []
  for root in registry.roots do
    if roots.contains root then errors := errors.push s!"roots: duplicate module {root}"
    roots := root :: roots
    unless (env.getModuleIdx? root).isSome do errors := errors.push s!"roots: module {root} is not loaded"
  if roots.isEmpty then errors := errors.push "roots: empty extraction roots"
  for concept in registry.concepts do
    unless semanticsId concept.id do errors := errors.push s!"concept {concept.id}: invalid id"
    unless nonblank concept.title do errors := errors.push s!"concept {concept.id}: blank title"
    if ids.contains concept.id then errors := errors.push s!"concept {concept.id}: duplicate id"
    ids := concept.id :: ids
    for mod in concept.defaultModules do
      if defaults.contains mod then errors := errors.push s!"concept {concept.id}: duplicate default module {mod}"
      defaults := mod :: defaults
      unless (env.getModuleIdx? mod).isSome do
        errors := errors.push s!"concept {concept.id}: default module {mod} is not loaded"
  let mut claimIds : List String := []
  let mut goals : List Name := []
  let mut claims : Array ClaimEntry := #[]
  for claim in registry.claims do
    let location := s!"claim {claim.id}"
    unless semanticsId claim.id do errors := errors.push s!"{location}: invalid id"
    unless nonblank claim.title do errors := errors.push s!"{location}: blank title"
    if claimIds.contains claim.id then errors := errors.push s!"{location}: duplicate id"
    claimIds := claim.id :: claimIds
    unless ids.contains claim.concept do errors := errors.push s!"{location}: unknown concept {claim.concept}"
    if let .witness goal := claim.pointer then
      if ProofGraph.isGoal env goal then
        if goals.contains goal then errors := errors.push s!"{location}: duplicate goal {goal}"
        goals := goal :: goals
    for ref in claim.literature do
      unless nonblank ref.work && nonblank ref.locator &&
          ["definitionUsed", "proofTechnique", "adaptedResult", "analogy", "excludedFeature"].contains ref.relation do
        errors := errors.push s!"{location}: invalid literature reference"
    try
      let ev ← evidence memo registers claim.pointer
      let mut contests : Array RegisterRow := #[]
      let mut contestIds : List String := []
      for id in claim.contestedBy do
        if contestIds.contains id then throwError "duplicate contested counterexample id {id}"
        contestIds := id :: contestIds
        let status ← counterexample registers id
        contests := contests.push { id, registerStatus := status.status, record := status.row }
      claims := claims.push { claim, evidence := ev, contestedBy := contests.toList }
    catch ex => errors := errors.push s!"{location}: {← ex.toMessageData.toString}"
  let mut cuts : Array CutEntry := #[]
  for cut in registry.cuts do
    let location := s!"cut {cut.concept} row {cut.decisionRow}"
    unless ids.contains cut.concept do errors := errors.push s!"{location}: unknown concept"
    unless nonblank cut.excluded && nonblank cut.reason do errors := errors.push s!"{location}: blank exclusion or reason"
    match registers.decisions.find? (·.1 == cut.decisionRow) with
    | none => errors := errors.push s!"{location}: unknown decision row"
    | some (_, who) => cuts := cuts.push { cut, who }
  -- A registry that fails its own checks is refused before the environment is scanned.
  if !errors.isEmpty then return .error errors
  -- Tags outside the committed population must still refer to a known concept, and a placement
  -- at a requirement to a requirement of the registry (decisions row 207). A declaration placed
  -- at a requirement is one of its nodes, beside the registry's top nodes.
  -- the attribute's own entries, module by module, never a scan of every constant
  let mut tags : Array (Name × Placement) := #[]
  for i in [0:memo.modules.size] do
    tags := tags ++ semanticsAttribute.ext.getModuleEntries env i
  for entry in (semanticsAttribute.ext.getState env).2 do
    tags := tags.push entry
  let mut placed : Array (Name × String) := #[]
  for (name, placement) in tags do
    unless ids.contains placement.concept do
      errors := errors.push s!"tag {name}: unknown concept {placement.concept}"
    if let some req := placement.requirement then
      if registry.requirements.any (·.id == req) then placed := placed.push (name, req)
      else errors := errors.push s!"tag {name}: unknown requirement {req}"
  placed := placed.qsort (·.1.toString < ·.1.toString)
  let mut placements : Array PlacedTheorem := #[]
  let mut unplaced : Array (Name × Nat) := #[]
  -- the eligible theorems (`semanticsTheorems`' population) of the concept-named modules only:
  -- every other module's theorems are skipped by the placement universe anyway
  let mut eligible : Array Name := #[]
  for mod in defaults do
    let some i := env.getModuleIdx? mod | continue
    for name in env.header.moduleData[i.toNat]!.constNames do
      if (env.find? name) matches some (.thmInfo _) && !ProofGraph.isAuxiliary env name &&
          !ProofGraph.isGoal env name then
        eligible := eligible.push name
  for name in eligible.qsort (·.toString < ·.toString) do
    let mod := moduleOf memo env name
    let tagged := (semanticsAttribute.getParam? env name).map (·.concept)
    let inherited := registry.concepts.find? (·.defaultModules.contains mod)
    match tagged.orElse (fun _ => inherited.map (·.id)) with
    | some id => placements := placements.push { name, module := mod, concept := id, tagged := tagged.isSome }
    | none =>
      let old := (unplaced.find? (·.1 == mod)).map (·.2) |>.getD 0
      unplaced := (unplaced.filter (·.1 != mod)).push (mod, old + 1)
  -- A requirement with neither a node nor an open part would read as proved over nothing, and a
  -- plan-scope prefix that matches no loaded module adds no goal silently: both are refused.
  let mut reqIds : List String := []
  for req in registry.requirements do
    if reqIds.contains req.id then errors := errors.push s!"requirement {req.id}: duplicate id"
    reqIds := req.id :: reqIds
    if req.top.isEmpty && req.openParts.isEmpty && !placed.any (·.2 == req.id) then
      errors := errors.push s!"requirement {req.id}: no top node, no placed node and no open part"
    -- a part that waits names what it waits on
    for part in req.openParts do
      if part.state.word != "untriaged" && part.state.word != "proposed" && part.state.on.isEmpty then
        errors := errors.push s!"requirement {req.id}: an open part waits on nothing"
  for pre in registry.planScope do
    unless memo.modules.any (pre.isPrefixOf ·) do
      errors := errors.push s!"plan scope {pre}: matches no loaded module"
  -- The plan (`ProofGraph.Plan`): the requirements' top and placed nodes, the claims' witnesses
  -- and every planned goal of the plan scope are the nodes; the edges are read from their proofs.
  let mut plan : PlanEntry := default
  try
    let mut named := registry.requirements.foldl (init := #[]) fun acc r => acc ++ r.top.toArray
    for (n, _) in placed do
      unless named.contains n do named := named.push n
    for claim in registry.claims do
      if let .witness w := claim.pointer then
        unless named.contains w do named := named.push w
    let built ← ProofGraph.buildPlan registry.planScope named memo.axioms
    plan ← planEntry memo built registry.requirements placed
  catch ex => errors := errors.push s!"plan: {← ex.toMessageData.toString}"
  -- The acceptance programs (decisions row 206): each battery's own stage and requirements.
  let mut acceptance : Array AcceptanceEntry := #[]
  for battery in registry.acceptance do
    match ← acceptanceEntry battery (registry.requirements.map (·.id)) with
    | .ok row => acceptance := acceptance.push row
    | .error why => errors := errors.push why
  if !errors.isEmpty then return .error errors
  return .ok {
    toolchain, roots := registry.roots, concepts := registry.concepts,
    claims := claims.toList, cuts := cuts.toList, plan, acceptance := acceptance.toList,
    placement := {
      declarations := placements.toList,
      unplacedByModule := (unplaced.qsort (·.1.toString < ·.1.toString)).toList } }

/-- Load exactly the declared roots after registering the attribute in this process. -/
def loadReport (registry : Registry) : IO (Except (Array String) Report) := do
  let counterexamples ← IO.FS.readFile "Test/Counterexamples/REGISTER.md"
  let decisions ← IO.FS.readFile "docs/core/decisions.md"
  let registers ← match parseRegisters counterexamples decisions with
    | .ok value => pure value
    | .error errors => return .error errors
  let toolchain := (← IO.FS.readFile "lean-toolchain").trimAscii.toString
  initSearchPath (← findSysroot)
  try
    let env ← importModules (registry.roots.toArray.map fun mod => { module := mod }) {} 0
    let ctx : Core.Context :=
      { fileName := "<semantics-report>", fileMap := default
        options := ({} : Options).set `maxHeartbeats (4000000 : Nat) }
    let (report, _) ← ((do
      try
        buildReport registry registers toolchain
      catch error => return .error #[← error.toMessageData.toString]).run' {}).toIO ctx { env := env }
    return report
  catch ex => return .error #[s!"roots: {ex}"]

end Tools.Semantics
