import Effect4
import Effect4.Laws
import Effect4.Laws.Auto.Traversals

/-!
Verifier of seat ORGANIZATION (2026-10-01), probe for ORG-03/ORG-04: private definitions.

The census's `definitionsUnder` (`Laws/Auto/Traversals.lean:151-167`) drops every name with
`Name.isInternal`, and a `private` definition's name is `_private.<module>.0.<name>`, which is
internal. So a private hand traversal is never a census row. This probe lists, per free object,
the person-written private definitions under `Effect4` that take a family value (the census's own
`domainOf`), and classifies each: RECURSIVE when its value names a family `brecOn`/`rec`/`below`
or reaches, through a `_unary`/`_mutual` helper, a well-founded fixpoint (a traversal);
MATCH when it only destructs one level (a family matcher, through `casesOn` or a sparse one).

Red control: `Effect4.Codegen.Types.ofNormalized` (private, reached by `Types.ofTy`) must be
listed for `Ty`.
-/

open Lean Elab Meta Command Effect4.Laws.Auto

def isCompilerMade (c : Name) : Bool :=
  isCompilerHelper c || c.components.any (fun s =>
    let t := s.toString
    t == "_unary" || t == "_mutual" || t == "splitter" || "_sparseCasesOn".isPrefixOf t ||
      "match_".isPrefixOf t || "_proof_".isPrefixOf t || "proof_".isPrefixOf t ||
      t == "_f" || t == "_sunfold" || t == "_unsafe_rec" || "eq_".isPrefixOf t || t == "_cstage1" ||
      t == "_cstage2" || t == "_redArg" || t == "_closed" || "_lambda".isPrefixOf t || t == "induct" ||
      "_spec".isPrefixOf t)

def reachesFamilyCase (env : Environment) (family : Array Name) (e : Expr) : Bool := Id.run do
  let mut seen : NameSet := {}
  let mut stack := e.getUsedConstants.toList
  let mut steps := 0
  let mut found := false
  while !stack.isEmpty && steps < 5000 && !found do
    steps := steps + 1
    match stack with
    | [] => break
    | c :: rest =>
      stack := rest
      if seen.contains c then continue
      seen := seen.insert c
      if family.contains c.getPrefix && (c.getString!.endsWith "casesOn" || c.getString! == "rec") then
        found := true
      if c.isInternalDetail || c.isInternal || isMatcherCore env c then
        if let some (.defnInfo d) := env.find? c then stack := d.value.getUsedConstants.toList ++ stack
  return found

syntax (name := censusPrivate) "#census_private " ident : command

@[command_elab censusPrivate] def elabCensusPrivate : CommandElab := fun stx => do
  let root := stx[1].getId
  let family ← liftCoreM (familyOf root)
  let env ← getEnv
  let mut out : Array String := #[]
  for (n, ci) in env.constants.map₁.toList do
    unless isPrivateName n do continue
    if isCompilerMade n then continue
    let .defnInfo d := ci | continue
    let some m := moduleOf env n | continue
    unless (`Effect4).isPrefixOf m do continue
    if (← liftTermElabM (domainOf family d.type)).isNone then continue
    let used := d.value.getUsedConstants
    let structural := used.any (fun c => family.contains c.getPrefix &&
      ["brecOn", "rec", "below", "binductionOn"].any (fun s => s.isPrefixOf c.getString!))
    let wf := used.any (fun c => (c.components.any (fun s => s.toString == "_unary" || s.toString == "_mutual")) &&
      match env.find? c with
      | some (.defnInfo h) => h.value.getUsedConstants.any (fun x => x == ``WellFounded.fix || x == ``WellFounded.Nat.fix)
      | _ => false)
    let matchOnly := !structural && !wf && reachesFamilyCase env family d.value
    let kind := if structural then "RECURSIVE(structural)" else if wf then "RECURSIVE(wf)" else if matchOnly then "MATCH" else "other"
    if kind != "other" then
      out := out.push s!"{kind}\t{m}\t{(privateToUserName? n).getD n}"
  let sorted := out.qsort (· < ·)
  let recN := (sorted.filter (fun s => s.startsWith "RECURSIVE")).size
  logInfo m!"#census_private {root}: {sorted.size} private person-written takers that destruct the family ({recN} recursive)\n{"\n".intercalate sorted.toList}"

#census_private Effect4.Program.Ty
#census_private Effect4.Program.Eff
#census_private Effect4.Program.Term
#census_private Effect4.Representation
#census_private Effect4.Store.Val
