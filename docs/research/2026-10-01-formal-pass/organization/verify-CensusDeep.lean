import Effect4
import Effect4.Laws
import Effect4.Laws.Auto.Traversals

/-!
Verifier of seat ORGANIZATION (2026-10-01), probe for ORG-04 and ORG-03.

The census (`Laws/Auto/Traversals.lean:228-233`) classes a taker by what its own value uses: a
family recursor or a family matcher makes it a traversal (`structural`, `wf`, `generated`), and
`wf` needs the value to name `WellFounded.fix`. A definition compiled through a helper the
compiler makes (`_unary`, `_mutual`, a matcher, a sparse `casesOn`, a splitter) hides both.

This probe recomputes the census's classification with the census's own helpers, then, for every
taker it would print `opaque` or `delegates`, follows ONLY compiler-made helpers (never another
person-written definition, which would be `delegates`, correctly) and reports whether that
hidden code does case analysis on the family (a family recursor or `casesOn`, including a sparse
one) and whether it reaches `WellFounded.fix` or `WellFounded.Nat.fix`.

Red controls: `Effect4.Program.Ty.sub` must be reported with a hidden `Ty` case analysis and a
well-founded fixpoint; `Effect4.Program.Ty.closed` (structural already) must not be reported.
-/

open Lean Elab Meta Command Effect4.Laws.Auto

/-- A constant the compiler or an elaborator made, not a person-written definition. -/
def isHiddenHelper (env : Environment) (c : Name) : Bool :=
  c.isInternalDetail || c.isInternal || isMatcherCore env c || isAuxRecursor env c ||
    c.components.any (fun s =>
      let t := s.toString
      t == "_unary" || t == "_mutual" || t == "splitter" || "_sparseCasesOn".isPrefixOf t ||
        "match_".isPrefixOf t || "_proof_".isPrefixOf t)

/-- A case analysis on a family member: its recursor, `casesOn`, `brecOn`, … or a sparse
`casesOn` the compiler builds over one. -/
def isFamilyCase (env : Environment) (family : Array Name) (c : Name) : Bool :=
  isFamilyRecursor env family c ||
    (family.contains c.getPrefix && "_sparseCasesOn".isPrefixOf c.getString!)

/-- Follow compiler-made helpers from `start` (bounded), collecting what they reach. -/
def hiddenReach (env : Environment) (start : Array Name) : NameSet := Id.run do
  let mut seen : NameSet := {}
  let mut stack := start.toList
  let mut steps := 0
  while !stack.isEmpty && steps < 20000 do
    steps := steps + 1
    match stack with
    | [] => break
    | c :: rest =>
      stack := rest
      if seen.contains c then continue
      seen := seen.insert c
      if isHiddenHelper env c then
        match env.find? c with
        | some (.defnInfo d) => stack := d.value.getUsedConstants.toList ++ stack
        | some (.opaqueInfo d) => stack := d.value.getUsedConstants.toList ++ stack
        | _ => pure ()
  return seen

syntax (name := censusDeep) "#census_deep " ident : command

@[command_elab censusDeep] def elabCensusDeep : CommandElab := fun stx => do
  let root := stx[1].getId
  let family ← liftCoreM (familyOf root)
  let env ← getEnv
  let defs := definitionsUnder env `Effect4
  let folds := foldsOf family defs
  let mut takers : Array (Name × Name × Expr) := #[]
  for (n, m, type, value) in defs do
    if folds.contains n then continue
    if (← liftTermElabM (domainOf family type)).isSome then takers := takers.push (n, m, value)
  let census : NameSet := takers.foldl (fun s (n, _, _) => s.insert n) {}
  let mut out : Array String := #[]
  let mut opaqueOrDelegates : Nat := 0
  for (n, m, value) in takers do
    let used := value.getUsedConstants
    let algebras := algebrasIn env folds value #[]
    let hands := used.filter fun c => c != n && census.contains c
    let recurses := used.any (isFamilyRecursor env family) || matchesFamily env family used
    let kind :=
      if !algebras.isEmpty then "fold"
      else if recurses then (if used.contains ``WellFounded.fix then "wf" else "structural/generated")
      else if !hands.isEmpty then "delegates" else "opaque"
    unless kind == "opaque" || kind == "delegates" do continue
    opaqueOrDelegates := opaqueOrDelegates + 1
    let reach := hiddenReach env (used.filter (isHiddenHelper env))
    let famCase := reach.toList.any (isFamilyCase env family)
    let wfFix := reach.contains ``WellFounded.fix || reach.contains ``WellFounded.Nat.fix
    if famCase || wfFix then
      let helpers := (used.filter (isHiddenHelper env)).toList.take 3
      out := out.push s!"{kind}\t{m}\t{n}\thiddenFamilyCase={famCase}\twfFix={wfFix}\tvia={helpers}"
  let sorted := out.qsort (· < ·)
  logInfo m!"#census_deep {root}: {takers.size} takers, {opaqueOrDelegates} printed opaque or delegates by the census's rule; {sorted.size} of those hide a family case analysis or a wf fixpoint\n{"\n".intercalate sorted.toList}"

#census_deep Effect4.Program.Ty
#census_deep Effect4.Program.Eff
#census_deep Effect4.Program.Term
#census_deep Effect4.Representation
#census_deep Effect4.Store.Val
