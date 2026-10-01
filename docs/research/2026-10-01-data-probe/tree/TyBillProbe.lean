import Effect4
import Effect4.Laws
import Effect4.Laws.Auto.Exhaustive

/-! Seat TREE, data probe (2026-10-01): the bill of a new `Ty` constructor at `bc77e97f`.

1. `#exhaustive_gate Effect4.Program.Ty` — the tree's own instrument (decisions row 61): every
   definition of an `Effect4.*` module whose `match` reads a `Ty`, and whether it has a
   catch-all. Definitions only (the instrument's header, "What it does not see").
2. `#ty_theorem_census` — this probe's addition for the proof side: every authored theorem of
   an `Effect4.*` module whose kernel term eliminates a `Ty` directly (`Ty.rec`, `Ty.recOn`,
   `Ty.brecOn`, `Ty.casesOn`, or a matcher over `Ty`), split into "inducts" (a `rec`/`brecOn`
   in the term) and "cases only". Generated equation, induction and splitter lemmas are skipped.
   Whether such a proof survives an appended constructor depends on its tactic shape; the count
   is the set that is re-elaborated with one more case, not the set that fails.

Printed, not asserted. Scratch, not in the tree. -/

open Lean Elab Command Meta

#exhaustive_gate Effect4.Program.Ty

namespace DataProbe.TyBill

/-- Generated theorems the census skips: equation lemmas, functional induction, splitters. -/
def generatedTheorem (name : Name) : Bool :=
  name.isInternalDetail || name.isInternal ||
    match name with
    | .str _ last =>
      "eq_".isPrefixOf last || last == "eq_def" || "induct".isPrefixOf last ||
        last == "splitter" || last == "fun_cases" || "match_".isPrefixOf last ||
        "proof_".isPrefixOf last || last == "eq_cata" || "_".isPrefixOf last
    | _ => false

elab "#ty_theorem_census" : command => do
  let env ← getEnv
  let family : Array Name := #[``Effect4.Program.Ty]
  let elims := Effect4.Laws.Auto.Exhaustive.eliminatorsOf env family
  let recs : Array Name := #[``Effect4.Program.Ty.rec, ``Effect4.Program.Ty.recOn,
    ``Effect4.Program.Ty.brecOn]
  let mut rows : Array (String × String × Bool) := #[]
  for (name, info) in env.constants.map₁.toList do
    if let .thmInfo t := info then
      if generatedTheorem name then continue
      let some idx := env.getModuleIdxFor? name | continue
      let mod := env.header.moduleNames[idx.toNat]!
      unless (`Effect4).isPrefixOf mod do continue
      let used := t.value.getUsedConstants
      if used.any elims.contains then
        rows := rows.push (mod.toString, name.toString, used.any recs.contains)
  let sorted := rows.qsort fun a b => a.1 < b.1 || (a.1 == b.1 && a.2.1 < b.2.1)
  let inducts := (sorted.filter (·.2.2)).size
  let mut perModule : Array (String × Nat × Nat) := #[]
  for r in sorted do
    match perModule.back? with
    | some (m, i, c) =>
      if m == r.1 then
        perModule := perModule.pop.push (m, i + (if r.2.2 then 1 else 0), c + (if r.2.2 then 0 else 1))
      else perModule := perModule.push (r.1, (if r.2.2 then 1 else 0), (if r.2.2 then 0 else 1))
    | none => perModule := perModule.push (r.1, (if r.2.2 then 1 else 0), (if r.2.2 then 0 else 1))
  let mut report := m!"#ty_theorem_census: {sorted.size} authored theorems of Effect4.* eliminate a Ty \
    directly; {inducts} induct (rec/brecOn), {sorted.size - inducts} case only\n  by module (inducts, cases only):"
  for (m, i, c) in perModule do
    report := report ++ m!"\n  {m}\t{i}\t{c}"
  report := report ++ m!"\n  theorems:"
  for (m, n, r) in sorted do
    report := report ++ m!"\n  {m}\t{n}\t{if r then "induct" else "cases"}"
  logInfo report

#ty_theorem_census

end DataProbe.TyBill
