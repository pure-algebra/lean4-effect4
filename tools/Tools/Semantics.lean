import Tools.SemanticsRegistry
import Tools.SemanticsDisplay
import Tools.GeneratedStamp
import Effect4.Laws.Auto.Semantics
import ProofGraph.Ledger
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
  let (reached, table) := (ProofGraph.reachedAxioms env name).run (← memo.get)
  memo.set table
  let some reached := reached | throwError "{name}: axiom collection exhausted its step budget"
  let axioms := reached.qsort (·.toString < ·.toString)
  let disallowed := ProofGraph.disallowedAxioms axioms
  unless disallowed.isEmpty do throwError "{name}: disallowed axioms {disallowed}"
  return obj [
    ("name", text name.toString), ("module", text (semanticsModule env name).toString),
    ("levels", names ci.levelParams), ("statement", text printed),
    ("axioms", names axioms.toList),
    ("withinSemanticAxiomCeiling", toJson (ProofGraph.disallowedAxioms axioms).isEmpty)]

private def witness (memo : IO.Ref ProofGraph.AxiomMemo) (name : Name) : MetaM Json := do
  -- `ProofRef.validate`'s checks at the theorem's own proposition, with the axioms memoized
  let t ← match (← getEnv).find? name with
    | some (.thmInfo t) => pure t
    | some _ => throwError "{name}: not a theorem"
    | none => throwError "Unknown constant `{name}`"
  if t.type.hasMVar || t.type.hasFVar then throwError "{name}: open proposition"
  if (← ProofGraph.readGoal name).isSome then
    throwError "{name}: obligation marker requires a goal pointer"
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
    let evidence ← witness memo name
    return ("proved", obj [("_tag", text "proved"), ("by", text "theorem"),
      ("witness", evidence), ("goal", .null)])
  | .goal name =>
    let some goal ← ProofGraph.readGoal name | throwError "{name}: not an obligation"
    let env ← getEnv
    let checked := name ++ `checked
    let wanted := name ++ `wanted
    if env.contains checked && env.contains wanted then throwError "{name}: stale placeholder (both checked and wanted)"
    if env.contains checked then
      discard <| ProofGraph.check #[goal] #[⟨name, .proved checked⟩] 0
      return ("proved", obj [("_tag", text "proved"), ("by", text "ledger"),
        ("witness", ← declaration memo checked), ("goal", ← declaration memo name (some goal.proposition))])
    if env.contains wanted then
      discard <| ProofGraph.check #[goal] #[⟨name, .wanted wanted⟩] 1
      return ("wanted", obj [("_tag", text "wanted"),
        ("goal", ← declaration memo name (some goal.proposition)), ("placeholder", text wanted.toString)])
    throwError "{name}: missing proof or placeholder"
  | .refutedBy id name =>
    let status ← counterexample index id
    if status.status == "RETIRED" then throwError "retired counterexample id {id}"
    let evidence ← witness memo name
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

/-- The plan's report section: the requirements with their derived statuses, the nodes reachable
from their top nodes and every ledger goal, the checked and unchecked edges, the loose premises and
the next goals (`ProofGraph.Plan`). -/
private def planJson (plan : ProofGraph.Plan) (requirements : List Requirement) (scopes : List Name) :
    MetaM Json := do
  let env ← getEnv
  let tops := requirements.foldl (init := #[]) fun acc r => acc ++ r.top.toArray
  let reach := plan.reachable tops
  let goals := (plan.nodes.filter (·.isGoal)).map (·.name)
  let shown := plan.nodes.filter fun n => reach.contains n.name || n.isGoal
  let mut nodes : Array Json := #[]
  for n in shown do
    let brought ← ProofGraph.broughtIn scopes plan n
    nodes := nodes.push (obj [("name", text n.name.toString),
      ("kind", text (if n.isGoal then "goal" else "theorem")),
      ("status", text (plan.status n.name).word),
      ("module", text (semanticsModule env n.name).toString),
      ("broughtIn", obj [("nearest", toJson (brought.nearest.map Name.toString)),
        ("lemmas", toJson brought.lemmas), ("definitions", toJson brought.definitions)])])
  let edges := plan.edges.map fun e => obj [("target", text e.target.toString),
    ("reduction", text e.reduction.toString), ("checked", toJson e.checked),
    ("premises", toJson (e.premises.map fun m => obj [("premise", text m.premise),
      ("node", match m.node with | some d => text d.toString | none => .null),
      ("byHypothesis", toJson m.byHypothesis)]))]
  let reqs := requirements.toArray.map fun r =>
    let statuses := r.top.map plan.status
    let word := if statuses.all (· == .proved) then "proved"
      else if statuses.any (· == .ready) then "ready"
      else if statuses.any (· == .reduced) then "reduced" else "declared"
    obj [("id", text r.id), ("title", text r.title), ("status", text word),
      ("top", toJson (r.top.map fun n =>
        obj [("name", text n.toString), ("status", text (plan.status n).word)])),
      ("reachable", toJson ((plan.reachable r.top.toArray).map Name.toString)),
      ("next", toJson ((plan.next r.top.toArray).map Name.toString))]
  let loose := plan.loose.map fun (t, r, premise) =>
    obj [("target", text t.toString), ("reduction", text r.toString), ("premise", text premise)]
  return obj [("requirements", toJson reqs), ("nodes", toJson nodes), ("edges", toJson edges),
    ("loose", toJson loose), ("next", toJson ((plan.next (tops ++ goals)).map Name.toString))]

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
    if let .goal goal := claim.pointer then
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
  -- Tags outside the committed population must still refer to a known concept.
  for (name, _) in env.constants.toList do
    if let some concept := semanticsAttribute.getParam? env name then
      unless ids.contains concept do errors := errors.push s!"tag {name}: unknown concept {concept}"
  let mut placements : Array Json := #[]
  let mut unplaced : Array (Name × Nat) := #[]
  for name in semanticsTheorems env do
    let mod := semanticsModule env name
    if !defaults.contains mod then continue
    let tagged := semanticsAttribute.getParam? env name
    let inherited := registry.concepts.find? (·.defaultModules.contains mod)
    let concept := tagged.orElse (fun _ => inherited.map (·.id))
    match concept with
    | some id => placements := placements.push (obj [("name", text name.toString),
        ("module", text mod.toString), ("concept", text id),
        ("placement", text (if tagged.isSome then "tagged" else "inherited"))])
    | none =>
      let old := (unplaced.find? (·.1 == mod)).map (·.2) |>.getD 0
      unplaced := (unplaced.filter (·.1 != mod)).push (mod, old + 1)
  -- The plan (`ProofGraph.Plan`): the ledger goals of the plan scope, the claims' witnesses and
  -- the requirements' top nodes are the nodes; the authored reductions become checked edges.
  let mut plan : Json := .null
  try
    let mut nodes ← (← ProofGraph.goalsIn registry.planScope).mapM fun g => ProofGraph.Node.ofGoal g
    let mut named : Array Name := #[]
    for claim in registry.claims do
      if let .witness w := claim.pointer then named := named.push w
    for req in registry.requirements do named := named ++ req.top.toArray
    for n in named do
      unless nodes.any (·.name == n) do nodes := nodes.push (← ProofGraph.Node.ofName n)
    let built ← ProofGraph.buildPlan nodes
      (registry.reductions.toArray.map fun r => (r.target, r.reduction))
    plan ← planJson built registry.requirements registry.planScope
  catch ex => errors := errors.push s!"plan: {← ex.toMessageData.toString}"
  let concepts := registry.concepts.map fun concept =>
    let members := rows.filter (·.1 == concept.id)
    let counts := ("claims", toJson members.size) ::
      (["proved", "wanted", "refuted", "absent", "assumed"].map fun tag =>
        (tag, toJson (members.filter (·.2.1 == tag)).size))
    obj [("id", text concept.id), ("title", text concept.title),
      ("defaultModules", names concept.defaultModules), ("counts", obj counts)]
  if !errors.isEmpty then return .error errors
  unplaced := unplaced.qsort (·.1.toString < ·.1.toString)
  return .ok <| obj [
    ("format", text "effect4-semantics-report"), ("schemaVersion", toJson (4 : Nat)),
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
    ("placement", obj [
      ("universe", text "theorems of the registry's concept-named modules; auxiliary names, ledger goals and their checked witnesses excluded"),
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

/-- The plan section: the requirements table, the next goals, the loose premises, and one Mermaid
diagram per requirement over the nodes it reaches. -/
private def renderPlan (plan : Json) : String := Id.run do
  if plan == .null then return ""
  let nodes := array plan "nodes"
  let statusOf (name : String) : String :=
    ((nodes.find? (field · "name" == name)).map (field · "status")).getD "declared"
  let mut out := "\n## Plan\n\nThe requirements that have plan nodes. A node is a ledger goal or a proved theorem; an edge is an authored reduction whose implication from its premise nodes to its target the kernel checked within the semantic ceiling (`tools/ProofGraph/Plan.lean`). Statuses are derived: declared, reduced, ready, proved. A loose premise is one no node discharges; it keeps its target from being ready.\n\n"
  out := out ++ "| Requirement | Status | Top nodes | Next goals |\n| --- | --- | --- | --- |\n"
  for req in array plan "requirements" do
    let tops := String.intercalate ", " ((array req "top").toList.map fun t =>
      s!"`{shortName (field t "name")}` ({field t "status"})")
    let next := (nested req "next").getArr?.toOption.getD #[]
    let nextText := if next.isEmpty then "—" else
      String.intercalate ", " (next.toList.map fun n => s!"`{shortName (n.getStr?.toOption.getD "")}`")
    out := out ++ s!"| {field req "id"} | {field req "status"} | {tops} | {nextText} |\n"
  let next := (nested plan "next").getArr?.toOption.getD #[]
  out := out ++ s!"\n**Next goals** ({next.size}): {String.intercalate ", " (next.toList.map fun n => n.getStr?.toOption.getD "")}\n"
  let loose := array plan "loose"
  unless loose.isEmpty do
    out := out ++ s!"\n**Loose premises** ({loose.size}):\n\n"
    for l in loose do
      out := out ++ s!"- `{shortName (field l "target")}` via `{shortName (field l "reduction")}`: `{cell (field l "premise")}`\n"
  for req in array plan "requirements" do
    let reach := ((nested req "reachable").getArr?.toOption.getD #[]).toList.map fun n => n.getStr?.toOption.getD ""
    out := out ++ s!"\n### {field req "id"}: {field req "title"}\n\n```mermaid\nflowchart LR\n"
    for (n, i) in reach.zipIdx do
      out := out ++ s!"  n{i}[\"{shortName n}<br/>{statusOf n}\"]\n"
    for e in array plan "edges" do
      let some src := reach.idxOf? (field e "target") | continue
      for m in array e "premises" do
        let dst := field m "node"
        if let some j := reach.idxOf? dst then
          let arrow := if (e.getObjValAs? Bool "checked").toOption == some true then "-->" else "-.->"
          out := out ++ s!"  n{src} {arrow}|\"{shortName (field e "reduction")}\"| n{j}\n"
    out := out ++ "```\n\n| Node | Status | Nearest nodes | Lemmas | Definitions |\n| --- | --- | --- | --- | --- |\n"
    for n in reach do
      let some node := nodes.find? (field · "name" == n) | continue
      let b := nested node "broughtIn"
      let nearest := ((nested b "nearest").getArr?.toOption.getD #[]).toList.map fun d =>
        s!"`{shortName (d.getStr?.toOption.getD "")}`"
      let count (key : String) := ((b.getObjValAs? Nat key).toOption.getD 0)
      out := out ++ s!"| `{shortName n}` | {statusOf n} | {if nearest.isEmpty then "—" else String.intercalate ", " nearest} | {count "lemmas"} | {count "definitions"} |\n"
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
        | "proved" => nested status "witness"
        | "wanted" => nested status "goal"
        | "refuted" => nested (nested status "counterexample") "witness"
        | _ => .null
      let contests := String.intercalate ", " ((array claim "contestedBy").toList.map fun r => field r "id")
      let ceiling := if evidence == .null then "—" else
        if (evidence.getObjValAs? Bool "withinSemanticAxiomCeiling").toOption == some true then "yes" else "no"
      let evidenceText := if evidence == .null then field status "reason" else field evidence "name"
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
  return out
end Tools.Semantics
