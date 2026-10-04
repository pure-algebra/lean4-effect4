import Lean
import ProofGraph.Population
import ProofGraph.Goal

/-!
Placement metadata for declarations, separate from claims and proof status: a declaration's
primary concept and, optionally, the requirement it serves (decisions row 207).

`@[semantics "store-typing" (requirement := R4)]` places a theorem or a planned goal. A goal
carries its placement as an ordinary attribute (`@[semantics …] proof_goal G : P`), so proving it
changes `proof_goal` to `theorem` and the placement stays. The semantics report reads a placed
declaration as a node of its requirement, beside the registry's top nodes. The tool-side registry
supplies module defaults for the concept; this command measures explicit tags only. This module
contains metaprogramming instrumentation, no semantic theorem.
-/
namespace Effect4.Laws.Auto
open Lean Meta Elab Command

/-- Concept and claim identifiers use the report's nonempty kebab-case alphabet. -/
def semanticsId (s : String) : Bool :=
  (s.splitOn "-").all fun part => !part.isEmpty && part.toList.all fun c =>
    ('a' ≤ c && c ≤ 'z') || ('0' ≤ c && c ≤ '9')

/-- A requirement identifier: `R` and a decimal with no leading zero (`docs/core/system-map.md`
§8). -/
def requirementId (s : String) : Bool :=
  match s.toList with
  | 'R' :: d :: ds => d != '0' && (d :: ds).all Char.isDigit
  | _ => false

/-- Where a declaration sits in the theory: its primary concept, and the requirement it serves
when it is one of that requirement's nodes. -/
structure Placement where
  concept : String
  requirement : Option String := none
  deriving BEq, Inhabited, Repr

syntax (name := semantics) &"semantics" ppSpace str (" (" &"requirement" " := " ident ")")? : attr

initialize semanticsAttribute : ParametricAttribute Placement ← do
  -- The native attribute's add hook overwrites duplicates. Its parameter reader checks the
  -- registered extension before addEntry. The cell closes that initialization dependency.
  let cell ← IO.mkRef (none : Option (ParametricAttribute Placement))
  let attr ← registerParametricAttribute {
    name := `semantics
    descr := "the declaration's primary semantic concept, and the requirement it serves"
    getParam := fun decl stx => do
      let some attr ← cell.get | throwError "semantics: attribute not initialized"
      if (attr.getParam? (← getEnv) decl).isSome then
        throwError "semantics: {decl} already has a concept"
      let some id := stx[1].isStrLit? | throwError "semantics: expected a string literal"
      unless semanticsId id do throwError "semantics: expected a nonempty kebab-case concept id"
      if stx[2].isNone then return { concept := id }
      let req := stx[2][3].getId.toString
      unless requirementId req do throwError "semantics: expected a requirement id such as R4"
      return { concept := id, requirement := some req } }
  cell.set (some attr)
  return attr

def semanticsModule (env : Environment) (name : Name) : Name :=
  match env.getModuleIdxFor? name with
  | some idx => env.header.moduleNames[idx.toNat]!
  | none => env.mainModule

/-- Eligible theorem names, sorted: the authored theorems, planned goals excluded (decisions row
203). Population selection is owned by the caller. -/
def semanticsTheorems (env : Environment) : Array Name :=
  (env.constants.toList.filterMap fun (name, ci) =>
    if ci matches .thmInfo _ && !ProofGraph.isAuxiliary env name && !ProofGraph.isGoal env name then
      some name
    else none).toArray.qsort (·.toString < ·.toString)

syntax (name := semanticsCensus) "#semantics_census" (ppSpace ident)? : command

@[command_elab semanticsCensus] def elabSemanticsCensus : CommandElab := fun stx => do
  let env ← getEnv
  let requested := stx[1].getOptional?.map (·.getId)
  if let some name := requested then
    unless name == env.mainModule || (env.getModuleIdx? name).isSome do
      throwError "semantics census: module {name} is not loaded"
  let eligible := (semanticsTheorems env).filter fun name =>
    let mod := semanticsModule env name
    match requested with
    | some wanted => mod == wanted
    | none => (`Effect4.Laws).isPrefixOf mod
  let mut tagged : Array (String × Name) := #[]
  let mut untagged : Array (Name × Name) := #[]
  for name in eligible do
    match semanticsAttribute.getParam? env name with
    | some placement => tagged := tagged.push (placement.concept, name)
    | none => untagged := untagged.push (semanticsModule env name, name)
  tagged := tagged.qsort fun a b => a.1 < b.1 || (a.1 == b.1 && a.2.toString < b.2.toString)
  untagged := untagged.qsort fun a b => a.1.toString < b.1.toString || (a.1 == b.1 && a.2.toString < b.2.toString)
  let mut report := "semantics census"
  for (concept, name) in tagged do
    let axioms ← liftCoreM <| collectAxioms name
    let axioms := axioms.qsort (·.toString < ·.toString)
    report := report ++ s!"\n{concept}\t{name}\ttheorem\t{axioms}"
  let modules := (untagged.map (·.1)).toList.eraseDups.length
  let population := requested.map Name.toString |>.getD "loaded Effect4.Laws modules"
  report := report ++ s!"\nuntagged: {untagged.size} theorems in {modules} modules (universe: {population})"
  for (mod, name) in untagged do report := report ++ s!"\n{mod}\t{name}"
  logInfo report

end Effect4.Laws.Auto
