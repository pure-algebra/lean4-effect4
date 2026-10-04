import Tools.SemanticsRegistry
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

private def text (s : String) : Json := toJson s
private def names (ns : List Name) : Json := toJson (ns.map Name.toString)
private def obj := Json.mkObj
private def nonblank (s : String) : Bool := !s.trimAscii.toString.isEmpty

def roleName (r : Role) : String := match r with
  | .inversion => "inversion" | .canonicalForms => "canonicalForms"
  | .weakening => "weakening" | .substitution => "substitution"
  | .progress => "progress" | .preservation => "preservation"
  | .monotonicity => "monotonicity" | .transitivity => "transitivity"
  | .antisymmetry => "antisymmetry" | .decidability => "decidability"
  | .adequacy => "adequacy" | .simulation => "simulation"
  | .compatibility => "compatibility" | .fundamentalProperty => "fundamentalProperty"

private def declaration (memo : IO.Ref ProofGraph.AxiomMemo) (name : Name)
    (proposition : Option Expr := none) : MetaM Json := do
  let ci ← getConstInfo name
  let env ← getEnv
  unless (env.getModuleIdxFor? name).isSome do
    throwError "{name}: witness module is not loaded"
  let printed ← Display.expression (proposition.getD ci.type)
  -- goals are leaves of the walk (decisions row 203): a theorem that rests on one reaches its
  -- name, never its `sorry`
  let (reached, table) := (ProofGraph.reachedWithGoals env name).run (← memo.get)
  memo.set table
  let some (reached, goals) := reached | throwError "{name}: axiom collection exhausted its step budget"
  let axioms := reached.qsort (·.toString < ·.toString)
  let disallowed := ProofGraph.disallowedAxioms axioms
  unless disallowed.isEmpty do throwError "{name}: disallowed axioms {disallowed}"
  return obj [
    ("name", text name.toString), ("module", text (semanticsModule env name).toString),
    ("levels", names ci.levelParams), ("statement", text printed),
    ("axioms", names axioms.toList),
    ("restsOn", names (goals.qsort (·.toString < ·.toString)).toList),
    ("withinSemanticAxiomCeiling", toJson (ProofGraph.disallowedAxioms axioms).isEmpty)]

private def witness (memo : IO.Ref ProofGraph.AxiomMemo) (name : Name) : MetaM Json := do
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

private def claimStatus (memo : IO.Ref ProofGraph.AxiomMemo) (index : Registers) (pointer : Pointer) :
    MetaM (String × Json) := do
  match pointer with
  | .witness name =>
    -- the standing is derived (decisions row 203): an open goal, a theorem that rests on goals,
    -- or a theorem that reaches none
    let evidence ← witness memo name
    let env ← getEnv
    if ProofGraph.isGoal env name then
      return ("wanted", obj [("_tag", text "wanted"), ("by", text "goal"), ("goal", evidence)])
    let goals := ((evidence.getObjValAs? (Array String) "restsOn").toOption.getD #[])
    unless goals.isEmpty do
      return ("modulo", obj [("_tag", text "modulo"), ("by", text "theorem"),
        ("witness", evidence), ("restsOn", toJson goals)])
    return ("proved", obj [("_tag", text "proved"), ("by", text "theorem"),
      ("witness", evidence), ("goal", .null)])
  | .refutedBy id name =>
    let status ← counterexample index id
    if status.status == "RETIRED" then throwError "retired counterexample id {id}"
    if ProofGraph.isGoal (← getEnv) name then throwError "{name}: a refutation is a planned goal"
    let evidence ← witness memo name
    unless ((evidence.getObjValAs? (Array String) "restsOn").toOption.getD #[]).isEmpty do
      throwError "{name}: a refutation rests on planned goals"
    return ("refuted", obj [("_tag", text "refuted"), ("counterexample", obj [
      ("id", text id), ("registerStatus", text status.status), ("record", text status.row), ("witness", evidence)])])
  | .absent reason =>
    unless nonblank reason do throwError "blank absent reason"
    return ("absent", obj [("_tag", text "absent"), ("reason", text reason)])
  | .assumed source reason =>
    unless nonblank source && nonblank reason do throwError "blank assumed source or reason"
    return ("assumed", obj [("_tag", text "assumed"), ("source", text source), ("reason", text reason)])

private def literatureJson (r : LiteratureRef) : Json :=
  obj [("work", text r.work), ("locator", text r.locator), ("relation", text r.relation)]

/-- The plan's report section: the requirements with their derived statuses, every node with its
standing, its placement and what its proof brings in, the edges to its nearest nodes, and the next
goals (`ProofGraph.Plan`). A requirement's nodes are its registry top nodes and the declarations
placed at it (`placed`, decisions row 207). -/
private def planJson (plan : ProofGraph.Plan) (requirements : List Requirement)
    (placed : Array (Name × String)) : MetaM Json := do
  let env ← getEnv
  let placedAt (r : Requirement) : List Name := (placed.filter (·.2 == r.id)).toList.map (·.1)
  let nodesOf (r : Requirement) : List Name := r.top ++ (placedAt r).filter (!r.top.contains ·)
  let tops := requirements.foldl (init := #[]) fun acc r => acc ++ (nodesOf r).toArray
  let mut nodes : Array Json := #[]
  for n in plan.nodes do
    let placement := match semanticsAttribute.getParam? env n.name with
      | some p => obj [("concept", text p.concept),
          ("requirement", match p.requirement with | some r => text r | none => .null)]
      | none => .null
    nodes := nodes.push (obj [("name", text n.name.toString),
      ("kind", text (if ProofGraph.isGoal env n.name then "goal" else "theorem")),
      ("status", text n.standing.word),
      ("restsOn", names n.restsOn.toList),
      ("module", text (semanticsModule env n.name).toString),
      ("placement", placement),
      ("statement", text (← Display.expression (← getConstInfo n.name).type)),
      ("axioms", names (n.axioms.qsort (·.toString < ·.toString)).toList),
      ("broughtIn", obj [("nearest", names n.nearest.toList),
        ("lemmas", toJson n.lemmas), ("definitions", toJson n.definitions)])])
  let word (n : Name) : String := ((plan.find? n).map (·.standing.word)).getD "missing"
  let status (n : Name) : Json := obj [("name", text n.toString), ("status", text (word n))]
  let reqs := requirements.toArray.map fun r =>
    let proved := r.openParts.isEmpty && (nodesOf r).all (word · == "proved")
    obj [("id", text r.id), ("title", text r.title), ("status", text (if proved then "proved" else "open")),
      ("openParts", toJson r.openParts),
      ("top", toJson (r.top.map status)),
      ("placed", toJson ((placedAt r).map status)),
      ("next", names (plan.next (nodesOf r).toArray).toList)]
  let next := plan.next tops
  -- a goal no requirement reaches is planned work without a place in the requirements
  let unplaced := (plan.nodes.filter fun n => ProofGraph.isGoal env n.name && !next.contains n.name).map (·.name)
  return obj [("requirements", toJson reqs), ("nodes", toJson nodes),
    ("next", names next.toList), ("unplacedGoals", names unplaced.toList)]

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

/-- A `Test.Dogfood.Reach` literal as JSON: the refused parts with their verdicts, and the four
stages. `none` if the value is not such a literal. -/
private def reachJson? (e : Expr) : Option Json := do
  let e := e.consumeMData
  guard (e.getAppFn.constName? == some `Test.Dogfood.Reach.mk && e.getAppNumArgs == 5)
  let args := e.getAppArgs
  let refused ← (← listLit? args[0]!).mapM fun pair => do
    let pair := pair.consumeMData
    guard (pair.getAppFn.constName? == some ``Prod.mk && pair.getAppNumArgs == 4)
    return obj [("part", text (← strLit? pair.getAppArgs[2]!)),
      ("verdict", text (← strLit? pair.getAppArgs[3]!))]
  let some answer := args[2]!.consumeMData.constName? | none
  guard (answer.getPrefix == `Test.Dogfood.Answer)
  return obj [("refused", toJson refused), ("admitted", toJson (← boolLit? args[1]!)),
    ("answer", text answer.getString!), ("printed", toJson (← boolLit? args[3]!)),
    ("readBack", toJson (← boolLit? args[4]!))]

/-- One acceptance program: its stage and the requirements it waits on, read from its battery. -/
private def acceptanceJson (battery : Name) (requirements : List String) :
    MetaM (Except String Json) := do
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
  let some reach := reachJson? stage.value
    | return .error s!"acceptance {battery}: `stage` is not a `Reach` literal"
  return .ok (obj [("program", text battery.toString), ("stage", reach), ("waitsOn", toJson ids)])

/-- Validate and collect all located refusals. No status is accepted from authored input. -/
def buildReport (registry : Registry) (registers : Registers) (toolchain : String) :
    MetaM (Except (Array String) Json) := do
  let env ← getEnv
  let memo ← IO.mkRef ({} : ProofGraph.AxiomMemo)
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
  let mut rows : Array (String × String × Json) := #[]
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
      let (tag, status) ← claimStatus memo registers claim.pointer
      let mut contests : Array Json := #[]
      let mut contestIds : List String := []
      for id in claim.contestedBy do
        if contestIds.contains id then throwError "duplicate contested counterexample id {id}"
        contestIds := id :: contestIds
        let status ← counterexample registers id
        contests := contests.push (obj [("id", text id), ("registerStatus", text status.status),
          ("record", text status.row), ("witness", .null)])
      let item := obj [("id", text claim.id), ("concept", text claim.concept),
        ("role", text (roleName claim.role)), ("title", text claim.title), ("status", status),
        ("contestedBy", toJson contests), ("literature", toJson (claim.literature.map literatureJson))]
      rows := rows.push (claim.concept, tag, item)
    catch ex => errors := errors.push s!"{location}: {← ex.toMessageData.toString}"
  let mut cuts : Array Json := #[]
  for cut in registry.cuts do
    let location := s!"cut {cut.concept} row {cut.decisionRow}"
    unless ids.contains cut.concept do errors := errors.push s!"{location}: unknown concept"
    unless nonblank cut.excluded && nonblank cut.reason do errors := errors.push s!"{location}: blank exclusion or reason"
    match registers.decisions.find? (·.1 == cut.decisionRow) with
    | none => errors := errors.push s!"{location}: unknown decision row"
    | some (_, who) =>
      cuts := cuts.push (obj [("concept", text cut.concept), ("decisionRow", toJson cut.decisionRow),
        ("excluded", text cut.excluded), ("reason", text cut.reason), ("who", text who)])
  -- A registry that fails its own checks is refused before the environment is scanned.
  if !errors.isEmpty then return .error errors
  -- Tags outside the committed population must still refer to a known concept, and a placement
  -- at a requirement to a requirement of the registry (decisions row 207). A declaration placed
  -- at a requirement is one of its nodes, beside the registry's top nodes.
  let mut placed : Array (Name × String) := #[]
  for (name, _) in env.constants.toList do
    if let some placement := semanticsAttribute.getParam? env name then
      unless ids.contains placement.concept do
        errors := errors.push s!"tag {name}: unknown concept {placement.concept}"
      if let some req := placement.requirement then
        if registry.requirements.any (·.id == req) then placed := placed.push (name, req)
        else errors := errors.push s!"tag {name}: unknown requirement {req}"
  placed := placed.qsort (·.1.toString < ·.1.toString)
  let mut placements : Array Json := #[]
  let mut unplaced : Array (Name × Nat) := #[]
  for name in semanticsTheorems env do
    let mod := semanticsModule env name
    if !defaults.contains mod then continue
    let tagged := (semanticsAttribute.getParam? env name).map (·.concept)
    let inherited := registry.concepts.find? (·.defaultModules.contains mod)
    let concept := tagged.orElse (fun _ => inherited.map (·.id))
    match concept with
    | some id => placements := placements.push (obj [("name", text name.toString),
        ("module", text mod.toString), ("concept", text id),
        ("placement", text (if tagged.isSome then "tagged" else "inherited"))])
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
  for pre in registry.planScope do
    unless env.header.moduleNames.any (pre.isPrefixOf ·) do
      errors := errors.push s!"plan scope {pre}: matches no loaded module"
  -- The plan (`ProofGraph.Plan`): the requirements' top and placed nodes, the claims' witnesses
  -- and every planned goal of the plan scope are the nodes; the edges are read from their proofs.
  let mut plan : Json := .null
  try
    let mut named := registry.requirements.foldl (init := #[]) fun acc r => acc ++ r.top.toArray
    for (n, _) in placed do
      unless named.contains n do named := named.push n
    for claim in registry.claims do
      if let .witness w := claim.pointer then
        unless named.contains w do named := named.push w
    let built ← ProofGraph.buildPlan registry.planScope named memo
    plan ← planJson built registry.requirements placed
  catch ex => errors := errors.push s!"plan: {← ex.toMessageData.toString}"
  -- The acceptance programs (decisions row 206): each battery's own stage and requirements.
  let mut acceptance : Array Json := #[]
  for battery in registry.acceptance do
    match ← acceptanceJson battery (registry.requirements.map (·.id)) with
    | .ok row => acceptance := acceptance.push row
    | .error why => errors := errors.push why
  let concepts := registry.concepts.map fun concept =>
    let members := rows.filter (·.1 == concept.id)
    let counts := ("claims", toJson members.size) ::
      (["proved", "modulo", "wanted", "refuted", "absent", "assumed"].map fun tag =>
        (tag, toJson (members.filter (·.2.1 == tag)).size))
    obj [("id", text concept.id), ("title", text concept.title),
      ("defaultModules", names concept.defaultModules), ("counts", obj counts)]
  if !errors.isEmpty then return .error errors
  unplaced := unplaced.qsort (·.1.toString < ·.1.toString)
  return .ok <| obj [
    ("format", text "effect4-semantics-report"), ("schemaVersion", toJson (6 : Nat)),
    ("producer", text (Tools.GeneratedStamp.note "tools/Drivers/Semantics.lean (make gen-semantics)")),
    ("command", text "make gen-semantics"),
    ("inputs", toJson (["tools/Tools/SemanticsRegistry.lean", "tools/Tools/Semantics.lean",
      "tools/Drivers/Semantics.lean", "tools/Tools/SemanticsDisplay.lean",
      "src/Effect4/Laws/Auto/Semantics.lean",
      "Test/Counterexamples/REGISTER.md", "docs/core/decisions.md", "lean-toolchain"] : List String)),
    ("provenance", obj [("toolchain", text toolchain), ("roots", names registry.roots),
      ("policy", obj [("gate", text "Test/Audit/AxiomGate.lean"),
        ("ceiling", toJson (["propext", "Quot.sound"] : List String))])]),
    ("concepts", toJson concepts), ("claims", toJson (rows.map (·.2.2))), ("cuts", toJson cuts), ("plan", plan),
    ("acceptance", toJson acceptance),
    ("placement", obj [
      ("universe", text "theorems of the registry's concept-named modules; auxiliary names and planned goals excluded"),
      ("declarations", toJson placements),
      ("unplacedCount", toJson (unplaced.foldl (fun total row => total + row.2) 0)),
      ("unplacedByModule", toJson (unplaced.map fun (mod, count) =>
        obj [("module", text mod.toString), ("count", toJson count)]))])]

/-- Load exactly the declared roots after registering the attribute in this process. -/
def loadReport (registry : Registry) : IO (Except (Array String) Json) := do
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

private def field (j : Json) (name : String) : String := (j.getObjValAs? String name).toOption.getD ""
private def array (j : Json) (name : String) : Array Json := (j.getObjValAs? (Array Json) name).toOption.getD #[]
private def nested (j : Json) (name : String) : Json := (j.getObjVal? name).toOption.getD .null
private def codeFence (s : String) : String :=
  let (_, longest) := s.toList.foldl (fun (run, longest) c =>
    let run := if c == '`' then run + 1 else 0
    (run, max longest run)) (0, 0)
  String.ofList (List.replicate (max 3 (longest + 1)) '`')

private def cell (s : String) : String := s.replace "|" "\\|" |>.replace "\n" " "

/-- Display a validated report. Generated statements/statuses have one owner; handwritten
language explanations live in docs/core. Code fences are longer than any statement run. -/
private def shortName (name : String) : String := (name.splitOn ".").getLast!

/-- The acceptance section (decisions row 206): one row per program, its stage as its battery
declares it, and the programs each requirement keeps waiting. -/
private def renderAcceptance (programs : Array Json) : String := Id.run do
  if programs.isEmpty then return ""
  let shortProgram (p : Json) : String := shortName (field p "program")
  let yes (j : Json) (name : String) : String :=
    match j.getObjValAs? Bool name with | .ok true => "yes" | .ok false => "no" | .error _ => "?"
  let strings (j : Json) (name : String) : List String :=
    (array j name).toList.map fun s => s.getStr?.toOption.getD ""
  let mut out := "\n## Acceptance programs\n\nThe rc.112 probe programs as acceptance tests (decisions row 206; `Test/Dogfood/README.md`). Each row is the `stage` its battery declares, which a guard ties to the battery's own measurement, and the requirements it `waitsOn`. A slice that moves a program edits both.\n\n"
  out := out ++ "| Program | Admitted | Answer | Printed | Read back | Refused parts | Waits on |\n| --- | --- | --- | --- | --- | --- | --- |\n"
  for p in programs do
    let stage := nested p "stage"
    let refused := (array stage "refused").toList.map fun r => s!"{field r "part"} ({field r "verdict"})"
    let refusedText := if refused.isEmpty then "—" else String.intercalate "; " refused
    out := out ++ s!"| `{shortProgram p}` | {yes stage "admitted"} | {field stage "answer"} | {yes stage "printed"} | {yes stage "readBack"} | {cell refusedText} | {String.intercalate ", " (strings p "waitsOn")} |\n"
  let ids := (programs.toList.flatMap (strings · "waitsOn")).eraseDups
  let ordered := ids.toArray.qsort fun a b => (a.drop 1).toNat! < (b.drop 1).toNat!
  out := out ++ "\nThe programs each requirement keeps waiting:\n\n"
  for id in ordered do
    let waiting := programs.toList.filter (strings · "waitsOn" |>.contains id)
    out := out ++ s!"- {id}: {String.intercalate ", " (waiting.map fun p => s!"`{shortProgram p}`")}\n"
  return out

/-- The plan section: the requirements table, the next goals, the loose premises, and one Mermaid
diagram per requirement over the nodes it reaches. -/
private def renderPlan (plan : Json) : String := Id.run do
  if plan == .null then return ""
  let nodes := array plan "nodes"
  let strings (j : Json) : List String := (j.getArr?.toOption.getD #[]).toList.map fun n =>
    n.getStr?.toOption.getD ""
  let nodeOf (name : String) : Option Json := nodes.find? (field · "name" == name)
  let statusOf (name : String) : String := ((nodeOf name).map (field · "status")).getD "missing"
  let nearestOf (name : String) : List String :=
    ((nodeOf name).map fun n => strings (nested (nested n "broughtIn") "nearest")).getD []
  let ticked (names : List String) : String :=
    if names.isEmpty then "—" else String.intercalate ", " (names.map fun n => s!"`{shortName n}`")
  let mut out := "\n## Plan\n\nThe requirements and their nodes. A node is a planned goal (a theorem whose body is `sorry`, declared by `proof_goal`) or a theorem a requirement names. Its status is derived from its proof, with goals as leaves (`tools/ProofGraph/Plan.lean`, decisions row 203): goal, modulo (proved from the goals it rests on), or proved. An edge goes from a node to the nodes its proof reaches first.\n\n"
  out := out ++ "A requirement's nodes are its top nodes, named by the registry, and the declarations placed at it (`@[semantics \"concept\" (requirement := Rn)]`, decisions row 207). A requirement is proved when every node is proved and no open part remains. An open part is one not yet stated as a goal.\n\n"
  out := out ++ "| Requirement | Status | Top nodes | Placed nodes | Next goals |\n| --- | --- | --- | --- | --- |\n"
  let listed (items : Array Json) : String :=
    if items.isEmpty then "—" else String.intercalate ", " (items.toList.map fun t =>
      s!"`{shortName (field t "name")}` ({field t "status"})")
  for req in array plan "requirements" do
    out := out ++ s!"| {field req "id"} | {field req "status"} | {listed (array req "top")} | {listed (array req "placed")} | {ticked (strings (nested req "next"))} |\n"
  let next := strings (nested plan "next")
  out := out ++ s!"\n**Next goals** ({next.length}): {ticked next}\n"
  let unplaced := strings (nested plan "unplacedGoals")
  unless unplaced.isEmpty do
    out := out ++ s!"\n**Goals no requirement reaches** ({unplaced.length}): {ticked unplaced}\n"
  for req in array plan "requirements" do
    -- the nodes the requirement's top and placed nodes reach through their nearest nodes
    let mut reach : List String := []
    let mut todo := ((array req "top") ++ (array req "placed")).toList.map (field · "name")
    for _ in [0:nodes.size + 1] do
      let some n := todo.head? | break
      todo := todo.tail
      if reach.contains n then continue
      reach := reach ++ [n]
      todo := todo ++ nearestOf n
    out := out ++ s!"\n### {field req "id"}: {field req "title"}\n\n"
    for part in strings (nested req "openParts") do
      out := out ++ s!"- Open: {part}\n"
    out := out ++ "\n```mermaid\nflowchart LR\n"
    for (n, i) in reach.zipIdx do
      out := out ++ s!"  n{i}[\"{shortName n}<br/>{statusOf n}\"]\n"
    for (n, i) in reach.zipIdx do
      for d in nearestOf n do
        if let some j := reach.idxOf? d then out := out ++ s!"  n{i} --> n{j}\n"
    out := out ++ "```\n\n| Node | Status | Rests on | Nearest nodes | Lemmas | Definitions |\n| --- | --- | --- | --- | --- | --- |\n"
    for n in reach do
      let some node := nodeOf n | continue
      let b := nested node "broughtIn"
      let count (key : String) := ((b.getObjValAs? Nat key).toOption.getD 0)
      out := out ++ s!"| `{shortName n}` | {statusOf n} | {ticked (strings (nested node "restsOn"))} | {ticked (nearestOf n)} | {count "lemmas"} | {count "definitions"} |\n"
  return out

def renderMarkdown (report : Json) : String := Id.run do
  let inputs := String.intercalate ", " ((array report "inputs").toList.map fun value => value.getStr?.toOption.getD "")
  let mut out := s!"<!-- {field report "producer"}\nformat: {field report "format"} v{(nested report "schemaVersion").compress}\ncommand: {field report "command"}\ninputs: {inputs}\n-->\n# Semantics evidence\n\n"
  out := out ++ "Selected evidence only. English associations are authored; inherited placement is provisional. The semantic axiom ceiling is not a whole-library gate verdict.\n\n"
  for concept in array report "concepts" do
    out := out ++ s!"## {field concept "id"}\n\n{field concept "title"}\n\n"
    out := out ++ "| Claim | Role | Status | Evidence | Evidence at the ceiling | Contested by |\n| --- | --- | --- | --- | --- | --- |\n"
    for claim in (array report "claims").filter (field · "concept" == field concept "id") do
      let status := nested claim "status"
      let tag := field status "_tag"
      let evidence := match tag with
        | "proved" | "modulo" => nested status "witness"
        | "wanted" => nested status "goal"
        | "refuted" => nested (nested status "counterexample") "witness"
        | _ => .null
      let contests := String.intercalate ", " ((array claim "contestedBy").toList.map fun r => field r "id")
      let ceiling := if evidence == .null then "—" else
        if (evidence.getObjValAs? Bool "withinSemanticAxiomCeiling").toOption == some true then "yes" else "no"
      let restsOn := ((nested status "restsOn").getArr?.toOption.getD #[]).toList.map fun n =>
        shortName (n.getStr?.toOption.getD "")
      let evidenceText := if evidence == .null then field status "reason"
        else if restsOn.isEmpty then field evidence "name"
        else s!"{field evidence "name"}, modulo {String.intercalate ", " restsOn}"
      out := out ++ s!"| {cell (field claim "id")} | {field claim "role"} | {tag} | {cell evidenceText} | {ceiling} | {cell contests} |\n"
    out := out ++ "\n### Printed statements\n\n"
    for claim in (array report "claims").filter (field · "concept" == field concept "id") do
      let status := nested claim "status"
      let evidence := if field status "_tag" == "wanted" then nested status "goal"
        else if field status "_tag" == "refuted" then nested (nested status "counterexample") "witness"
        else nested status "witness"
      if evidence != .null then
        let statement := field evidence "statement"
        let fence := codeFence statement
        out := out ++ s!"**{field claim "id"}**\n\n{fence}lean\n{statement}\n{fence}\n\n"
      for reference in array claim "literature" do
        out := out ++ s!"Literature: {cell (field reference "work")}, {cell (field reference "locator")} — {cell (field reference "relation")}\n\n"
  out := out ++ "## Register context\n\nThese are authored links to historical attacks. Read each full row: a leading status word may coexist with a later repair. It does not by itself refute the currently printed proposition. Source: [counterexample register](../Test/Counterexamples/REGISTER.md).\n\n"
  for claim in array report "claims" do
    let status := nested claim "status"
    let refs := if field status "_tag" == "refuted" then
        (array claim "contestedBy").push (nested status "counterexample")
      else array claim "contestedBy"
    for reference in refs do
      let row := field reference "record"
      let fence := codeFence row
      out := out ++ s!"**{field claim "id"}: {field reference "id"}**\n\n{fence}text\n{row}\n{fence}\n\n"
  out := out ++ "## Applicability decisions\n\n| Concept | Row | Who | Excluded |\n| --- | --- | --- | --- |\n"
  for cut in array report "cuts" do
    out := out ++ s!"| {field cut "concept"} | {(nested cut "decisionRow").compress} | {cell (field cut "who")} | {cell (field cut "excluded")} |\n"
  let placement := nested report "placement"
  let declarations := array placement "declarations"
  let tagged := declarations.filter (field · "placement" == "tagged")
  let inherited := declarations.filter (field · "placement" == "inherited")
  out := out ++ s!"\n## Placement\n\n{field placement "universe"}\n\nTagged: {tagged.size}; inherited (provisional): {inherited.size}; unplaced: {(nested placement "unplacedCount").compress}.\n"
  out := out ++ renderPlan (nested report "plan")
  out := out ++ renderAcceptance (array report "acceptance")
  return out
end Tools.Semantics
