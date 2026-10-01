import Effect4
import Effect4.Laws
import Effect4.Laws.Auto.Exhaustive

/-! Verifier of seat TREE (2026-10-01): the proof-side census, with auxiliary bodies attributed.

A theorem proved by well-founded or structural recursion keeps little in its own constant: its
body sits in internal auxiliaries (`foo._unary`, `foo._proof_N`, `foo.match_N`'s users, …), and a
census that reads only the top-level term misses the `Ty` eliminators and the `induct`/
`fun_cases` principles used there (`sub_trans_core`, `sub_normalize_of_sub`,
`sub_antisymm_normal` are of this kind). This repeats the seat's census2 rule, then attributes
every internal-detail constant to the nearest authored theorem whose name prefixes it, the way
`Exhaustive.bodiesUnder` attributes a definition's helpers to it. Printed, not asserted. -/

open Lean Elab Command Meta
open Effect4.Laws.Auto (isCompilerHelper moduleOf)
open Effect4.Laws.Auto.Exhaustive (eliminatorsOf)

namespace ProbeU.ProofCensusBroad

/-- census2's exclusion rule, copied verbatim from `TyBillPrivateProbe.lean`. -/
def seatGenerated (name : Name) : Bool :=
  isCompilerHelper name ||
  name.components.any (fun c =>
    let s := c.toString
    "match_".isPrefixOf s || "congr_eq".isPrefixOf s || "eq_".isPrefixOf s ||
      s == "eq_def" || "induct".isPrefixOf s || s == "splitter" || s == "fun_cases" ||
      "proof_".isPrefixOf s || "_unfold".isPrefixOf s || s == "eq_cata")

def isEqnName (s : String) : Bool :=
  s == "eq_def" ||
    (("eq_".isPrefixOf s) && (s.toList.drop 3) != [] && (s.toList.drop 3).all Char.isDigit)

/-- The seat's rule with `"eq_"` narrowed to real equation lemmas. -/
def generatedNarrow (name : Name) : Bool :=
  isCompilerHelper name ||
  name.components.any (fun c =>
    let s := c.toString
    "match_".isPrefixOf s || "congr_eq".isPrefixOf s || isEqnName s ||
      "induct".isPrefixOf s || s == "splitter" || s == "fun_cases" ||
      "proof_".isPrefixOf s || "_unfold".isPrefixOf s || s == "eq_cata")

def isFunPrinciple (s : String) : Bool :=
  s == "induct" || s == "induct_unfolding" || s == "fun_cases" || s == "fun_cases_unfolding" ||
    s == "mutual_induct"

/-- The nearest name in `owners` that is `name` or a prefix of it. -/
def ownerOf (owners : NameSet) : Nat → Name → Option Name
  | 0, _ => none
  | _, .anonymous => none
  | fuel + 1, name => if owners.contains name then some name else ownerOf owners fuel name.getPrefix

elab "#verify_ty_proof_census_attributed" : command => do
  let env ← getEnv
  let tyName := ``Effect4.Program.Ty
  let elims := eliminatorsOf env #[tyName]
  let ctors : List Name :=
    match env.find? tyName with
    | some (.inductInfo iv) => iv.ctors
    | _ => []
  -- authored theorems of Effect4.* under the narrowed rule, private included
  let mut owners : NameSet := {}
  for (name, info) in env.constants.map₁.toList do
    let .thmInfo _ := info | continue
    if name.isInternalDetail && !isPrivateName name then continue
    if generatedNarrow name then continue
    let some mod := moduleOf env name | continue
    unless (`Effect4).isPrefixOf mod do continue
    owners := owners.insert name
  -- used constants per owner, auxiliaries attributed
  let mut uses : NameMap (Array Name) := {}
  for (name, info) in env.constants.map₁.toList do
    let value? : Option Expr := match info with
      | .thmInfo t => some t.value
      | .defnInfo d => some d.value
      | _ => none
    let some value := value? | continue
    let some owner := ownerOf owners 32 name | continue
    unless owner == name || name.isInternalDetail do continue
    let prev := (uses.find? owner).getD #[]
    uses := uses.insert owner (prev ++ value.getUsedConstants)
  let mut direct : Array Name := #[]
  let mut principle : Array (Name × Name) := #[]
  for (owner, used) in uses.toList do
    if used.any elims.contains then direct := direct.push owner
    for c in used do
      match c with
      | .str _ s =>
        if isFunPrinciple s then
          if let some ci := env.find? c then
            if ci.type.getUsedConstants.any ctors.contains then
              unless principle.contains (owner, c) do principle := principle.push (owner, c)
      | _ => pure ()
  let principleOwners := principle.foldl (init := (#[] : Array Name)) fun acc (n, _) =>
    if acc.contains n then acc else acc.push n
  let union := principleOwners.foldl (init := direct) fun acc n =>
    if acc.contains n then acc else acc.push n
  let seatLike := direct.filter (!seatGenerated ·)
  -- the seat's census2 itself: top-level term only, its own name rule
  let mut seatSet : Array Name := #[]
  for (name, info) in env.constants.map₁.toList do
    let .thmInfo t := info | continue
    if seatGenerated name then continue
    if name.isInternalDetail && !isPrivateName name then continue
    let some mod := moduleOf env name | continue
    unless (`Effect4).isPrefixOf mod do continue
    if t.value.getUsedConstants.any elims.contains then seatSet := seatSet.push name
  let added := union.filter (!seatSet.contains ·)
  let mut report := m!"#verify_ty_proof_census_attributed: authored theorems eliminating Ty \
    directly, auxiliaries attributed = {direct.size} (the seat's name rule on the same set: \
    {seatLike.size}); using a Ty-shaped induct/fun_cases principle = {principleOwners.size}; \
    either = {union.size}"
  report := report ++ m!"\n  census2 (recomputed) = {seatSet.size}; counted here and not in census2 = {added.size}:"
  for n in added.qsort (·.toString < ·.toString) do
    report := report ++ m!"\n    {(privateToUserName? n).getD n}"
  report := report ++ m!"\n  principle users (theorem <- principle):"
  for (n, c) in principle.qsort (fun a b => a.1.toString < b.1.toString) do
    report := report ++ m!"\n    {(privateToUserName? n).getD n} <- {c}"
  logInfo report

#verify_ty_proof_census_attributed

end ProbeU.ProofCensusBroad
