import Effect4
import Effect4.Laws
import Effect4.Laws.Auto.Exhaustive

/-! Seat TREE, data probe (2026-10-01): what `#exhaustive_gate` cannot see.

`Traversals.definitionsUnder` drops every name for which `Name.isInternal` holds
(`Laws/Auto/Traversals.lean:155`), and a `private` declaration's name
(`_private.<Module>.0.<Name>`) is internal. So a `private def` that matches on `Ty` is not in
the gate's report. This probe walks the private definitions of `Effect4.*` modules with the
gate's own matcher reader (`matchesOn`, `matcherCatchAll`) and reports them; then it repeats
the theorem census of `TyBillProbe.lean` with private theorems included and the generated
`match_N.congr_eq_K`, `brecOn.eq` lemmas excluded by name.

Printed, not asserted. Scratch, not in the tree. -/

open Lean Elab Command Meta
open Effect4.Laws.Auto (isCompilerHelper moduleOf)
open Effect4.Laws.Auto.Exhaustive (eliminatorsOf matchesOn matcherCatchAll)

namespace DataProbe.TyBillPrivate

elab "#ty_private_gate" : command => do
  let env ← getEnv
  let family : Array Name := #[``Effect4.Program.Ty]
  let elims := eliminatorsOf env family
  let mut rows : Array (String × String × String × Nat × Nat × Bool) := #[]
  for (name, info) in env.constants.map₁.toList do
    let .defnInfo d := info | continue
    unless isPrivateName name do continue
    if isMatcherCore env name || isAuxRecursor env name || isCompilerHelper name then continue
    let some mod := moduleOf env name | continue
    unless (`Effect4).isPrefixOf mod do continue
    unless d.value.getUsedConstants.any elims.contains do continue
    let hits ← liftTermElabM (matchesOn family name mod 200 d.value #[])
    let mut seen : Array (Name × Nat) := #[]
    for h in hits do
      if seen.contains (h.matcher, h.discr) then continue
      seen := seen.push (h.matcher, h.discr)
      let ca ← liftTermElabM (matcherCatchAll h.matcher h.info h.discr)
      rows := rows.push (mod.toString, (privateToUserName? name).getD name |>.toString,
        h.matcher.toString, h.discr, h.info.numAlts, ca)
  let exposed := rows.filter (!·.2.2.2.2.2)
  let mut report := m!"#ty_private_gate: {rows.size} match(es) in private definitions of Effect4.* read Ty, \
    {exposed.size} with no catch-all"
  for (m, n, mt, d, a, c) in rows do
    report := report ++ m!"\n  {n}\t{m}\t{mt}\tdiscr {d}\talts {a}\tcatchAll {c}"
  logInfo report

#ty_private_gate

/-- Lemmas the equation compiler, the match compiler and functional induction generate. -/
def generatedTheorem (name : Name) : Bool :=
  isCompilerHelper name ||
  name.components.any (fun c =>
    let s := c.toString
    "match_".isPrefixOf s || "congr_eq".isPrefixOf s || "eq_".isPrefixOf s ||
      s == "eq_def" || "induct".isPrefixOf s || s == "splitter" || s == "fun_cases" ||
      "proof_".isPrefixOf s || "_unfold".isPrefixOf s || s == "eq_cata")

elab "#ty_theorem_census2" : command => do
  let env ← getEnv
  let family : Array Name := #[``Effect4.Program.Ty]
  let elims := eliminatorsOf env family
  let recs : Array Name := #[``Effect4.Program.Ty.rec, ``Effect4.Program.Ty.recOn,
    ``Effect4.Program.Ty.brecOn]
  let mut total : Nat := 0
  let mut inducts : Nat := 0
  let mut privates : Nat := 0
  let mut privList : Array String := #[]
  for (name, info) in env.constants.map₁.toList do
    let .thmInfo t := info | continue
    if generatedTheorem name then continue
    if name.isInternalDetail && !isPrivateName name then continue
    let some mod := moduleOf env name | continue
    unless (`Effect4).isPrefixOf mod do continue
    let used := t.value.getUsedConstants
    unless used.any elims.contains do continue
    total := total + 1
    if used.any recs.contains then inducts := inducts + 1
    if isPrivateName name then
      privates := privates + 1
      privList := privList.push s!"{mod}\t{(privateToUserName? name).getD name}\t{if used.any recs.contains then "induct" else "cases"}"
  let mut report := m!"#ty_theorem_census2: {total} authored theorems (private included, generated \
    lemmas excluded) eliminate a Ty directly; {inducts} induct; {privates} are private"
  for p in privList.qsort (· < ·) do
    report := report ++ m!"\n  {p}"
  logInfo report

#ty_theorem_census2

end DataProbe.TyBillPrivate
