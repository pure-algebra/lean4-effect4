import Tools.Semantics
import Tools.Document

/-!
# Tools.SemanticsDocument — the semantics report as a document

`Report.document` reads the measured report (`Tools.Semantics.Report`) and builds one
`Tools.Document.Document`; the Markdown committed as `generated/semantics.md` and the HTML page
under `.lake/gen/semantics-report/` are its folds. It displays the report's evidence and assigns
none: every status, statement and edge is the report's.

Each claim keeps its title, its evidence's declaration and module, the goals it rests on, an
absence's reason, an assumption's source and every register record it cites. Each
applicability decision keeps its reason.
-/

namespace Tools.Semantics
open Lean Tools.Document

/-! ## Names as the plan section prints them -/

/-- A list without its repeats, each name at its first place, as `List.eraseDups` gives it, with
a hash set in place of a scan of the names kept so far. -/
def dedup (names : List String) : List String :=
  (names.foldl (init := (#[], ({} : Std.HashSet String))) fun (kept, seen) n =>
    if seen.contains n then (kept, seen) else (kept.push n, seen.insert n)).1.toList

/-- The names that a list of names reaches through `nearestOf`, breadth first, and the names
still queued when the bound ran out. A name is queued once: when it is neither reached nor
queued. So each step reaches one new name, and a bound of the count of distinct names is
enough. A queue that is not empty at the end is answered, never dropped. Before 2026-10-05 the
loop queued a name at every edge into it, and the repeated visits spent the bound: a node
below a shared dependency could be left out (Codex's dogfooding review). -/
def reachThrough (nearestOf : String → List String) (bound : Nat) (start : List String) :
    List String × List String := Id.run do
  let mut reach : Array String := #[]
  let mut todo : Array String := (dedup start).toArray
  -- the queue is `todo` from `head` on; `known` is every name reached or queued
  let mut head := 0
  let mut known : Std.HashSet String := Std.HashSet.ofArray todo
  for _ in [0:bound] do
    let some n := todo[head]? | break
    head := head + 1
    reach := reach.push n
    for d in nearestOf n do
      unless known.contains d do
        known := known.insert d
        todo := todo.push d
  return (reach.toList, (todo.extract head todo.size).toList)

/-- A name by the fewest of its last components that no other name of a list shares. One
component is enough for most names, and `shortName` is that case. Two modules that state a step
of one name need more: `Effect4.Queue.Model.takeStep_types` and
`Effect4.Semaphore.Model.takeStep_types` print as `Queue.Model.takeStep_types` and
`Semaphore.Model.takeStep_types`. A name whose every run of last components another name
shares prints in full. The list is the names that one requirement's row and section print, so a
name is told from the names beside it and no further (seat SEM's receipt, item 10, row 6). -/
def displayName (among : List String) (name : String) : String := Id.run do
  let parts := name.splitOn "."
  let others := (among.eraseDups.filter (· != name)).map (·.splitOn ".")
  for count in [1:parts.length] do
    let tail := parts.drop (parts.length - count)
    unless others.any (fun other => other.drop (other.length - count) == tail) do
      return String.intercalate "." tail
  return name

/-- `displayName among` for every name of `among` at once, as a table. Each run of last components
of each distinct name is counted once, so a name's display is its shortest run that only it ends
in: the count is one. A component holds no dot, so a run is told by its spelling. The answer is
data, not a closure: a definition that returns a closure is compiled with the closure's argument
as one more parameter, and its tables would be built again at every call. -/
def displayNames (among : List String) : Std.HashMap String String :=
  let distinct := dedup among
  let runs (name : String) : List String :=
    let parts := name.splitOn "."
    (List.range parts.length).map fun k => String.intercalate "." (parts.drop k)
  let counts : Std.HashMap String Nat := distinct.foldl (init := {}) fun m name =>
    (runs name).foldl (fun m run => m.insert run (m.getD run 0 + 1)) m
  let shown : Std.HashMap String String := distinct.foldl (init := {}) fun m name =>
    -- the runs from the longest, so the last one counted once is the shortest; the whole name
    -- is no candidate, as in `displayName`
    let unique := ((runs name).drop 1).filter (counts.getD · 0 == 1)
    m.insert name (unique.getLast?.getD name)
  shown

/-- A name as `displayNames` shows it, and by `displayName` when the table lacks it. -/
def shownIn (table : Std.HashMap String String) (among : List String) (name : String) : String :=
  match table[name]? with
  | some shown => shown
  | none => displayName among name


/-! ## The document -/

private def code (n : Name) : Inline := .code n.toString

/-- Names as code, separated by commas; a dash for none. -/
private def codes (shown : String → String) (ns : List String) : Line :=
  if ns.isEmpty then [.text "—"] else
    List.intercalate [.text ", "] (ns.map fun n => [.code (shown n)])

private def claimKey (id : String) : String := "claim:" ++ id

/-- A claim's evidence in one cell: its declaration, with the goals it rests on, or the reason
that stands in for one. -/
private def evidenceCell (e : Evidence) : Line :=
  match e with
  | .modulo d => [code d.name, .text ", modulo "] ++
      List.intercalate [.text ", "] (d.restsOn.map fun g => [.code (g.getString!)])
  | .absent reason => [.text reason]
  | .assumed source _ => [.text "assumed: ", .text source]
  | e => (e.declaration?.map fun d => [code d.name]).getD []

/-- A register record a claim cites, as its id, status and verbatim row. -/
private def recordBlocks (r : RegisterRow) : List Block :=
  [.para [.text "Register record ", .code r.id, .text s!" ({r.registerStatus})"], .code "text" r.record]

/-- A claim's own part: its title, what its table row leaves out (the evidence's module, an
assumption's reason, the literature), its statement and the register records it cites. -/
private def claimPart (c : ClaimEntry) : Block :=
  let e := c.evidence
  let fields : List (String × Line) :=
    (e.declaration?.map fun d => ("Module", [code d.module])).toList ++
    (match e with | .assumed _ reason => [("Reason", [.text reason])] | _ => []) ++
    c.claim.literature.map fun l =>
      ("Literature", [.text l.work, .text ", ", .text l.locator, .text s!" ({l.relation})"])
  let records := (match e with | .refuted row => [row] | _ => []) ++ c.contestedBy
  .part (claimKey c.claim.id) c.claim.id <|
    [.para [.text c.claim.title]] ++ (if fields.isEmpty then [] else [.fields fields]) ++
    (e.declaration?.map fun d => [Block.code "lean" d.statement]).getD [] ++
    records.flatMap recordBlocks

/-- A concept's part: its title, its claims' table, then each claim's part. -/
private def conceptPart (concept : Concept) (claims : List ClaimEntry) : Block :=
  .part ("concept:" ++ concept.id) concept.id <|
    [.para [.text concept.title],
     .table ["Claim", "Role", "Status", "Evidence", "Contested by"] (claims.map fun c =>
       [[.ref (claimKey c.claim.id) c.claim.id], [.text (roleName c.claim.role)], [.status c.evidence.tag],
        evidenceCell c.evidence, codes id (c.contestedBy.map (·.id))])] ++
    claims.map claimPart

private def applicabilityPart (cuts : List CutEntry) : Block :=
  .part "applicability" "Applicability decisions"
    [.table ["Concept", "Row", "Who", "Excluded", "Reason"] (cuts.map fun c =>
      [[.ref ("concept:" ++ c.cut.concept) c.cut.concept], [.text (toString c.cut.decisionRow)],
       [.text c.who], [.text c.cut.excluded], [.text c.cut.reason]])]

private def placementPart (p : PlacementEntry) : Block :=
  let tagged := (p.declarations.filter (·.tagged)).length
  let unplaced := p.unplacedByModule.foldl (fun total row => total + row.2) 0
  .part "placement" "Placement"
    [.para [.text placementUniverse],
     .para [.text s!"Tagged: {tagged}; inherited (provisional): {p.declarations.length - tagged}; unplaced: {unplaced}."]]

/-- The plan section: the requirements table, the next goals, the open parts by state, the loose
goals, then one part per requirement with its open parts, a Mermaid diagram over the nodes it
reaches, and their table. A name prints by `displayName`, among the names of its own row and
part. -/
private def planPart (plan : PlanEntry) : Block := Id.run do
  let index : Std.HashMap String NodeEntry := plan.nodes.foldl (fun m n => m.insert n.name.toString n) {}
  let statusOf (n : String) : String := ((index[n]?).map (·.standing)).getD "missing"
  let nearestOf (n : String) : List String := ((index[n]?).map (·.nearest.map Name.toString)).getD []
  let restsOnOf (n : String) : List String := ((index[n]?).map (·.restsOn.map Name.toString)).getD []
  let str (ns : List Name) : List String := ns.map Name.toString
  -- every name that a traversal can meet: the nodes, and every name a node's edge names
  let names := dedup (plan.nodes.flatMap fun n => n.name.toString :: str n.nearest)
  -- per requirement: the nodes its top and placed nodes reach, the names still queued, and every
  -- name its row and part print, traversed once
  let sections := plan.requirements.map fun req =>
    let start := str ((req.top ++ req.placed).map (·.1))
    let (reach, pending) := reachThrough nearestOf (names.length + start.length) start
    let printed := dedup (start ++ str req.next ++ reach ++ pending ++
      reach.flatMap fun n => restsOnOf n ++ nearestOf n)
    (req, reach, pending, printed)
  let listed (shown : String → String) (ns : List (Name × String)) : Line :=
    if ns.isEmpty then [.text "—"] else
      List.intercalate [.text ", "] (ns.map fun (n, s) => [.code (shown n.toString), .text " (", .status s, .text ")"])
  let rows := sections.map fun (req, _, _, printed) =>
    let shown := shownIn (displayNames printed) printed
    [[.ref ("req:" ++ req.requirement.id) req.requirement.id], [.status (if req.proved then "proved" else "open")],
     listed shown req.top, listed shown req.placed, codes shown (str req.next)]
  let next := str plan.next
  let unplaced := str plan.unplacedGoals
  let loose := shownIn (displayNames (next ++ unplaced)) (next ++ unplaced)
  let parts := plan.requirements.flatMap (·.requirement.openParts)
  let count (state : String) : Nat := (parts.filter (·.state.word == state)).length
  let mut body : List Block := [
    .para [.text "The requirements and their nodes. A node is a planned goal (a theorem whose body is ",
      .code "sorry", .text ", declared by ", .code "proof_goal", .text ") or a theorem a requirement names. ",
      .text "Its status is derived from its proof, with goals as leaves (", .code "tools/ProofGraph/Plan.lean",
      .text ", decisions row 203): goal, modulo (proved from the goals it rests on), or proved. ",
      .text "An edge goes from a node to the nodes its proof reaches first."],
    .para [.text "A requirement's nodes are its top nodes, named by the registry, and the declarations placed at it (",
      .code "@[semantics \"concept\" (requirement := Rn)]",
      .text ", decisions row 207). A requirement is proved when every node is proved and no open part remains. ",
      .text "An open part is one not yet stated as a goal."],
    .table ["Requirement", "Status", "Top nodes", "Placed nodes", "Next goals"] rows,
    .para ([.text s!"Next goals ({next.length}): "] ++ codes loose next),
    .para [.text s!"Open parts, with no planned goal ({parts.length}): not triaged {count "untriaged"}; worded as a proposed claim {count "proposed"}; waits on a ruling {count "ruling"}; needs a definition {count "definition"}; after other work {count "work"}."]]
  unless unplaced.isEmpty do
    body := body ++ [.para ([.text s!"Goals no requirement reaches ({unplaced.length}): "] ++ codes loose unplaced)]
  for (req, reach, pending, printed) in sections do
    let shown := shownIn (displayNames printed) printed
    let reached := Std.HashSet.ofList reach
    let incomplete : List Line := if pending.isEmpty then [] else
      [[.text s!"Incomplete: the traversal stopped with {pending.length} names not visited ("] ++ codes shown pending ++ [.text ")."]]
    let openLines : List Line := req.requirement.openParts.map fun part =>
      let label := match part.state.word with
        | "proposed" => "Open, worded as a proposed claim"
        | "ruling" => s!"Open, waits on a ruling ({part.state.on})"
        | "definition" => s!"Open, needs a definition ({part.state.on})"
        | "work" => s!"Open, after other work ({part.state.on})"
        | _ => "Open, not triaged"
      [.text (label ++ ": " ++ part.text)]
    -- A node's id is a hash of its name, so a new node adds lines and renumbers none.
    let nodeId := fun (n : String) => "n" ++ String.ofList (Nat.toDigits 16 ((hash n).toNat % 0x100000000))
    let mermaid := "flowchart LR\n" ++
      String.join (reach.map fun n => s!"  {nodeId n}[\"{shown n}<br/>{statusOf n}\"]\n") ++
      String.join (reach.flatMap fun n => (nearestOf n).filterMap fun d =>
        if reached.contains d then some s!"  {nodeId n} --> {nodeId d}\n" else none)
    let nodeRows := (reach.filter (index.contains ·)).map fun n =>
      [[.code (shown n)], [.status (statusOf n)], codes shown (restsOnOf n), codes shown (nearestOf n)]
    let lines := incomplete ++ openLines
    body := body ++ [.part ("req:" ++ req.requirement.id) (req.requirement.id ++ ": " ++ req.requirement.title) <|
      (if lines.isEmpty then [] else [.items lines]) ++
      [.code "mermaid" mermaid, .table ["Node", "Status", "Rests on", "Nearest nodes"] nodeRows]]
  return .part "plan" "Plan" body

/-- The acceptance section (decisions row 206): one row per program, its stage as its battery
declares it, and the programs each requirement keeps waiting. -/
private def acceptancePart (programs : List AcceptanceEntry) : List Block :=
  if programs.isEmpty then [] else
  let short (p : AcceptanceEntry) : String := p.program.getString!
  let yes (b : Bool) : Line := [.text (if b then "yes" else "no")]
  let ids := dedup (programs.flatMap (·.waitsOn))
  let ordered := ids.toArray.qsort fun a b => (a.drop 1).toNat! < (b.drop 1).toNat!
  [.part "acceptance" "Acceptance programs" [
    .para [.text "The rc.112 probe programs as acceptance tests (decisions row 206; ", .code "Test/Dogfood/README.md",
      .text "). Each row is the ", .code "stage", .text " its battery declares, which a guard ties to the battery's own measurement, and the requirements it ",
      .code "waitsOn", .text ". A slice that moves a program edits both."],
    .table ["Program", "Admitted", "Answer", "Printed", "Read back", "Refused parts", "Waits on"] (programs.map fun p =>
      [[.code (short p)], yes p.stage.admitted, [.text p.stage.answer], yes p.stage.printed, yes p.stage.readBack,
       (if p.stage.refused.isEmpty then [.text "—"] else
         [.text ("; ".intercalate (p.stage.refused.map fun (part, verdict) => s!"{part} ({verdict})"))]),
       List.intercalate [.text ", "] (p.waitsOn.map fun r => [.ref ("req:" ++ r) r])]),
    .para [.text "The programs each requirement keeps waiting:"],
    .items (ordered.toList.map fun id =>
      [.ref ("req:" ++ id) id, .text ": "] ++
        List.intercalate [.text ", "] ((programs.filter (·.waitsOn.contains id)).map fun p => [.code (short p)]))]]

/-- The report as one document. Concepts group their claims once, in the registry's order. -/
def Report.document (r : Report) : Document :=
  let byConcept : Std.HashMap String (Array ClaimEntry) :=
    r.claims.foldl (fun m c => m.insert c.claim.concept ((m.getD c.claim.concept #[]).push c)) {}
  { title := "Semantics evidence"
    producer := [producer, "format: effect4-semantics-report v6", s!"command: {command}",
      s!"inputs: {", ".intercalate inputs}"]
    body :=
      [.para [.text "Selected evidence only. English associations are authored; inherited placement is provisional. ",
        .text "Every witness is within the semantic axiom ceiling, or the report is refused; that ceiling is not a whole-library gate verdict. ",
        .text "A register record is an authored link to a historical attack: read the full row, since a leading status word may coexist with a later repair."]] ++
      r.concepts.map (fun c => conceptPart c (byConcept.getD c.id #[]).toList) ++
      [applicabilityPart r.cuts, placementPart r.placement, planPart r.plan] ++ acceptancePart r.acceptance }

end Tools.Semantics
