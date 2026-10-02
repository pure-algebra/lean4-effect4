import Tools.SemanticsRegistry
import ProofGraph.Ledger
import Tools.SemanticsDisplay

/-! A selected, context-preserving view of the existing proof environment. Features and
planning prerequisites are authored; declaration references come from kernel expressions.
No edge is evidence for its consumer. See docs/ARCHITECTURE.md, Proof and feature view. -/
namespace Tools.Semantics.ProofMap
open Lean Meta

structure Feature where
  id : String
  title : String
  concepts : List String
  «syntax» : List Name := []
  judgments : List Name := []
  rules : List Name := []
  requires : List String := []
  boundary : String
deriving Inhabited

structure Work where
  id : String
  title : String
  features : List String
  after : List String := []
  source : String
  reason : String
deriving Inhabited

structure Selection where
  features : Array Feature := #[]
  /-- (consumer goal, prerequisite goal), exactly Goal.dependencies' convention. -/
  prerequisites : Array (Name × Name) := #[]
  work : Array Work := #[]
deriving Inhabited

private def obj := Json.mkObj
private def names (xs : List Name) : Json := toJson (xs.map Name.toString)

def scope : String :=
  "Authored significant declarations grouped by language feature. Edges are direct references among those declarations, not a full proof-term census or a checked natural-deduction sketch. Body references include annotations; statement references only identify vocabulary. Omitted reference counts expose the selection boundary. Authored prerequisites do not establish conservativity or entailment."

def literature : Json := toJson ([
  obj [("work", toJson "Adams2004"), ("locator", toJson "TYPES 2003, pp. 3–5, Fig. 2; §3.4, pp. 11–12"),
    ("use", toJson "Feature = grammar, judgments and rules with prerequisites. Conservativity is a separate theorem, not inferred from a dependency diagram.")],
  obj [("work", toJson "Ballarin2004"), ("locator", toJson "TYPES 2003, §§3.2–3.5, pp. 37–41; §4, pp. 42–48"),
    ("use", toJson "Retain parameters and assumptions when a contextual fact is exported. Availability through imports is distinct from use in a proof.")],
  obj [("work", toJson "Wiedijk2004"), ("locator", toJson "TYPES 2003, §3, pp. 383–385; §5, pp. 386–387; §9.2, p. 392"),
    ("use", toJson "Select significant steps and retain links to checked detail. An open candidate sketch is not a completed proof; our metadata checker does not check natural-deduction steps.")]
] : List Json)

def empty : Json := obj [("scope", toJson scope), ("literature", literature),
  ("features", toJson (#[] : Array Json)), ("nodes", toJson (#[] : Array Json)),
  ("edges", toJson (#[] : Array Json)), ("work", toJson (#[] : Array Json))]

private def acyclic (ids : Array String) (edges : Array (String × String)) : Bool := Id.run do
  let mut remaining := ids
  for _ in [:ids.size] do
    remaining := remaining.filter fun id => edges.any fun (consumer, dependency) =>
      consumer == id && remaining.contains dependency
  return remaining.isEmpty

private def unique (where_ : String) (ids : List String) : MetaM Unit := do
  unless ids.eraseDups.length == ids.length do throwError "proof map {where_}: duplicate id"
  unless ids.all (!·.trimAscii.toString.isEmpty) do throwError "proof map {where_}: blank id"

private def printExpr (e : Expr) : MetaM String :=
  Display.expression e

private def body? : ConstantInfo → Option Expr
  | .thmInfo i => some i.value
  | .defnInfo i => some i.value
  | .opaqueInfo i => some i.value
  | _ => none

/-- Show structure premises and inductive rules without confusing their constructor
types with a defining expression. Reference extraction still reads the actual constant. -/
private def definitionText (ci : ConstantInfo) : MetaM (Option String) := do
  if let .inductInfo info := ci then
    let signatures ← info.ctors.mapM fun name => do
      return s!"{name} : {← printExpr (← getConstInfo name).type}"
    return some ("Constructor signatures\n" ++ String.intercalate "\n\n" signatures)
  return ← (body? ci).mapM printExpr

private def edge (dependency consumer : Name) (kind : String) : Json :=
  obj [("from", toJson dependency.toString), ("to", toJson consumer.toString), ("kind", toJson kind)]

/-- Validate all selected formal goals together with their authored dependency metadata.
Other references are only extracted, never invented to fill a missing proof connection. -/
def build (registry : Registry) (selection : Selection) : MetaM Json := do
  let env ← getEnv
  let features := selection.features
  let featureIds := features.map (·.id)
  unique "features" featureIds.toList
  let selected := (features.toList.flatMap fun f => f.syntax ++ f.judgments ++ f.rules).eraseDups
  let ids := selected.map Name.toString
  let mut featureEdges := #[]
  for f in features do
    unless !f.title.trimAscii.toString.isEmpty && !f.boundary.trimAscii.toString.isEmpty do
      throwError "proof map {f.id}: blank feature description"
    for concept in f.concepts do
      unless registry.concepts.any (·.id == concept) do
        throwError "proof map {f.id}: unknown concept {concept}"
    unique f.id ((f.syntax ++ f.judgments ++ f.rules).map Name.toString)
    unique s!"{f.id} prerequisites" f.requires
    for dependency in f.requires do
      unless featureIds.contains dependency do throwError "proof map {f.id}: unknown feature {dependency}"
      featureEdges := featureEdges.push (f.id, dependency)
  unless acyclic featureIds featureEdges do throwError "proof map: feature prerequisite cycle"
  let mut goals : Array ProofGraph.Goal := #[]
  let mut entries : Array ProofGraph.Entry := #[]
  let mut nodes : Array Json := #[]
  let mut edges : Array Json := #[]
  for name in selected do
    let ci ← getConstInfo name
    let mut kind := "definition"
    let mut status := "defined"
    let mut evidence : Option Name := none
    let mut proposition := ci.type
    let mut value := body? ci
    if let some goal ← ProofGraph.readGoal name then
      kind := "goal"
      proposition := goal.proposition
      let checked := name ++ `checked
      let wanted := name ++ `wanted
      if env.contains checked && env.contains wanted then
        throwError "proof map {name}: stale checked/wanted evidence"
      if env.contains checked then
        status := "proved"
        evidence := some checked
        value := body? (← getConstInfo checked)
        entries := entries.push ⟨name, .proved checked⟩
      else if env.contains wanted then
        status := "wanted"
        evidence := some wanted
        value := none
        entries := entries.push ⟨name, .wanted wanted⟩
      else throwError "proof map {name}: missing evidence or placeholder"
      goals := goals.push { goal with dependencies :=
        (selection.prerequisites.filter (·.1 == name)).map (·.2) }
    else if ci matches .thmInfo _ then
      kind := "theorem"
      status := "proved"
      evidence := some name
      let reference : ProofGraph.ProofRef := ⟨name, ci.levelParams, ci.type⟩
      if let .error why ← reference.validate then throwError "proof map: {why}"
    let axioms := (← collectAxioms (evidence.getD name)).qsort (·.toString < ·.toString)
    let premises ← forallTelescope proposition fun xs _ => do
      let mut items := #[]
      for x in xs do
        let type ← inferType x
        if ← isProp type then
          items := items.push (obj [("name", toJson (← x.fvarId!.getDecl).userName.toString),
            ("statement", toJson (← printExpr type))])
      return items
    let some moduleIdx := env.getModuleIdxFor? name
      | throwError "proof map {name}: module not loaded"
    let mod := env.header.moduleNames[moduleIdx.toNat]!
    let rel := mod.toString.replace "." "/" ++ ".lean"
    let path := if mod.getRoot == `Effect4 then "src/" ++ rel
      else if mod.getRoot == `Test then rel else "tools/" ++ rel
    let line := (← findDeclarationRanges? name).map (·.range.pos.line) |>.getD 0
    let refs := proposition.getUsedConstants ++ (value.map Expr.getUsedConstants).getD #[]
    let omitted := refs.toList.eraseDups.filter fun ref => ref != name && !selected.contains ref
    let claims := registry.claims.filterMap fun claim =>
      let pointer := match claim.pointer with
        | .witness n | .goal n | .refutedBy _ n => some n
        | _ => none
      if pointer == some name then some claim.id else none
    nodes := nodes.push <| obj [
      ("id", toJson name.toString), ("title", toJson name.getString!),
      ("kind", toJson kind), ("status", toJson status),
      ("module", toJson mod.toString), ("path", toJson path), ("line", toJson line),
      ("levels", names ci.levelParams), ("evidence", toJson (evidence.map Name.toString)),
      ("statement", toJson (← printExpr proposition)), ("premises", toJson premises),
      ("body", toJson (← if kind == "definition" then definitionText ci else pure none)),
      ("axioms", names axioms.toList), ("claims", toJson claims),
      ("omittedReferences", toJson omitted.length)]
    for dependency in selected do
      if dependency == name then continue
      if proposition.getUsedConstants.contains dependency then
        edges := edges.push (edge dependency name "statement-reference")
      if (value.map Expr.getUsedConstants).getD #[] |>.contains dependency then
        edges := edges.push (edge dependency name
          (if kind == "definition" then "definition-reference" else "proof-reference"))
  unique "ledger edges" (selection.prerequisites.toList.map fun (a,b) => s!"{a}/{b}")
  for (consumer, dependency) in selection.prerequisites do
    unless goals.any (·.id == consumer) && goals.any (·.id == dependency) do
      throwError "proof map: unknown ledger goal in {consumer} / {dependency}"
    edges := edges.push (edge dependency consumer "ledger-prerequisite")
  discard <| ProofGraph.check goals entries goals.size
  let workIds := selection.work.map (·.id)
  unique "work" (ids ++ workIds.toList)
  let mut workEdges := #[]
  for item in selection.work do
    unless [item.title, item.source, item.reason].all (!·.trimAscii.toString.isEmpty) do
      throwError "proof map {item.id}: blank work description"
    for feature in item.features do
      unless featureIds.contains feature do throwError "proof map {item.id}: unknown feature {feature}"
    for dependency in item.after do
      unless ids.contains dependency || workIds.contains dependency do
        throwError "proof map {item.id}: unknown prerequisite {dependency}"
      workEdges := workEdges.push (item.id, dependency)
  unless acyclic (ids.toArray ++ workIds) workEdges do throwError "proof map: work sequencing cycle"
  return obj [("scope", toJson scope), ("literature", literature), ("nodes", toJson nodes),
    ("edges", toJson edges), ("features", toJson (features.map fun f => obj [
      ("id", toJson f.id), ("title", toJson f.title), ("concepts", toJson f.concepts),
      ("syntax", names f.syntax), ("judgments", names f.judgments), ("rules", names f.rules),
      ("requires", toJson f.requires), ("boundary", toJson f.boundary)])),
    ("work", toJson (selection.work.map fun w => obj [
      ("id", toJson w.id), ("title", toJson w.title), ("features", toJson w.features),
      ("after", toJson w.after), ("source", toJson w.source), ("reason", toJson w.reason)]))]
end Tools.Semantics.ProofMap
