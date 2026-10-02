import Lean

/-!
Concept placement metadata for declarations, separate from claims and proof status.
The tool-side registry supplies module defaults; this command measures explicit tags only.
This module contains metaprogramming instrumentation, no semantic theorem.
-/
namespace Effect4.Laws.Auto
open Lean Meta Elab Command

/-- Concept and claim identifiers use the report's nonempty kebab-case alphabet. -/
def semanticsId (s : String) : Bool :=
  (s.splitOn "-").all fun part => !part.isEmpty && part.toList.all fun c =>
    ('a' ≤ c && c ≤ 'z') || ('0' ≤ c && c ≤ '9')

syntax (name := semantics) &"semantics" ppSpace str : attr

initialize semanticsAttribute : ParametricAttribute String ← do
  -- The native attribute's add hook overwrites duplicates. Its parameter reader checks the
  -- registered extension before addEntry. The cell closes that initialization dependency.
  let cell ← IO.mkRef (none : Option (ParametricAttribute String))
  let attr ← registerParametricAttribute {
    name := `semantics
    descr := "the declaration's primary semantic concept"
    getParam := fun decl stx => do
      let some attr ← cell.get | throwError "semantics: attribute not initialized"
      if (attr.getParam? (← getEnv) decl).isSome then
        throwError "semantics: {decl} already has a concept"
      let some id := stx[1].isStrLit? | throwError "semantics: expected a string literal"
      unless semanticsId id do throwError "semantics: expected a nonempty kebab-case concept id"
      return id }
  cell.set (some attr)
  return attr

/-- Same auxiliary-name population as Tools.Architecture.isNoise; that executable cannot be
imported here. Kept here once for both the command and the report producer. -/
def semanticsNoise (n : Name) : Bool :=
  n.isInternal || n.hasMacroScopes || n.components.any fun c =>
    match c with
    | .str _ s =>
      s.startsWith "_" || s.startsWith "match_" || s.startsWith "proof_" || s.startsWith "eq_" ||
        s == "rec" || s == "recOn" || s == "casesOn" || s == "below" || s == "brecOn" ||
        s == "binductionOn" || s == "ibelow" || s == "noConfusion" || s == "noConfusionType" ||
        s == "inj" || s == "injEq" || s == "sizeOf_spec" || s.startsWith "instSizeOf" ||
        s == "ctorIdx" || s == "ctorElim"
    | _ => true

private def goalMarker : Expr → Bool
  | .forallE _ _ body _ => goalMarker body
  | e => e.isAppOfArity `ProofGraph.Obligation 1

def semanticsModule (env : Environment) (name : Name) : Name :=
  match env.getModuleIdxFor? name with
  | some idx => env.header.moduleNames[idx.toNat]!
  | none => env.mainModule

/-- Eligible theorem names, sorted. A checked witness is excluded only when its parent is
an actual obligation marker. Population selection is owned by the caller. -/
def semanticsTheorems (env : Environment) : Array Name :=
  (env.constants.toList.filterMap fun (name, ci) => do
    let .thmInfo info := ci | none
    if semanticsNoise name || goalMarker info.type then none else do
      if name.getString! == "checked" then
        if let some parent := env.find? name.getPrefix then
          if goalMarker parent.type then return ← none
      some name).toArray.qsort (·.toString < ·.toString)

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
    | some concept => tagged := tagged.push (concept, name)
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
