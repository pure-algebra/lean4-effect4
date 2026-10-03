import Tools.SemanticsRegistry
import Tools.SemanticsDisplay
import Tools.GeneratedStamp
import Effect4.Laws.Auto.Semantics
import ProofGraph.Ledger

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

private def declaration (name : Name) (proposition : Option Expr := none) : MetaM Json := do
  let ci ← getConstInfo name
  let env ← getEnv
  unless (env.getModuleIdxFor? name).isSome do
    throwError "{name}: witness module is not loaded"
  let printed ← Display.expression (proposition.getD ci.type)
  let axioms := (← collectAxioms name).qsort (·.toString < ·.toString)
  let disallowed := ProofGraph.disallowedAxioms axioms
  unless disallowed.isEmpty do throwError "{name}: disallowed axioms {disallowed}"
  return obj [
    ("name", text name.toString), ("module", text (semanticsModule env name).toString),
    ("levels", names ci.levelParams), ("statement", text printed),
    ("axioms", names axioms.toList),
    ("withinSemanticAxiomCeiling", toJson (ProofGraph.disallowedAxioms axioms).isEmpty)]

private def witness (name : Name) : MetaM Json := do
  let ci ← getConstInfo name
  let reference : ProofGraph.ProofRef := ⟨name, ci.levelParams, ci.type⟩
  if let .error why ← reference.validate then throwError "{why}"
  if (← ProofGraph.readGoal name).isSome then
    throwError "{name}: obligation marker requires a goal pointer"
  declaration name

private def counterexample (index : Registers) (id : String) : MetaM CounterexampleEntry := do
  let some row := index.counterexamples.find? (·.id == id)
    | throwError "unknown counterexample id {id}"
  unless registerId row.id do throwError "invalid counterexample id {id}"
  unless statuses.contains row.status do throwError "invalid register status for {id}"
  unless nonblank row.row do throwError "missing register context for {id}"
  return row

private def claimStatus (index : Registers) (pointer : Pointer) : MetaM (String × Json) := do
  match pointer with
  | .witness name =>
    let evidence ← witness name
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
        ("witness", ← declaration checked), ("goal", ← declaration name (some goal.proposition))])
    if env.contains wanted then
      discard <| ProofGraph.check #[goal] #[⟨name, .wanted wanted⟩] 1
      return ("wanted", obj [("_tag", text "wanted"),
        ("goal", ← declaration name (some goal.proposition)), ("placeholder", text wanted.toString)])
    throwError "{name}: missing proof or placeholder"
  | .refutedBy id name =>
    let status ← counterexample index id
    if status.status == "RETIRED" then throwError "retired counterexample id {id}"
    let evidence ← witness name
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

/-- Validate and collect all located refusals. No status is accepted from authored input. -/
def buildReport (registry : Registry) (registers : Registers) (toolchain : String) :
    MetaM (Except (Array String) Json) := do
  let env ← getEnv
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
      let (tag, status) ← claimStatus registers claim.pointer
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
    ("format", text "effect4-semantics-report"), ("schemaVersion", toJson (3 : Nat)),
    ("producer", text (Tools.GeneratedStamp.note "tools/Drivers/Semantics.lean (make gen-semantics)")),
    ("command", text "make gen-semantics"),
    ("inputs", toJson (["tools/Tools/SemanticsRegistry.lean", "tools/Tools/Semantics.lean",
      "tools/Drivers/Semantics.lean", "tools/Tools/SemanticsDisplay.lean",
      "src/Effect4/Laws/Auto/Semantics.lean",
      "Test/Counterexamples/REGISTER.md", "docs/core/decisions.md", "lean-toolchain"] : List String)),
    ("provenance", obj [("toolchain", text toolchain), ("roots", names registry.roots),
      ("policy", obj [("gate", text "Test/Audit/AxiomGate.lean"),
        ("ceiling", toJson (["propext", "Quot.sound"] : List String))])]),
    ("concepts", toJson concepts), ("claims", toJson (rows.map (·.2.2))), ("cuts", toJson cuts),
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
  return out
end Tools.Semantics
