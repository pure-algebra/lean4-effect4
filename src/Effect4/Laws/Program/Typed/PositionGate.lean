import Effect4.Laws.Auto.Positions
import Effect4.Laws.Program.Typed.TypedSources
import Effect4.Laws.Program.Typed.Sources

/-!
# Laws.Auto.PositionGate — every position has a typing source, and every source a position

`#position_gate R₁ R₂ …` runs `#position_census` on the roots and joins the result with the
hand table `Effect4.Program.Typed.sources`: a position with no row, or a row naming no
position, is an error, listed by key. A position reached from several roots is one key. With
this command in a built module, adding a value-holding field anywhere under the roots fails
the build until the field is sourced (`docs/research/2026-09-18-position-census-design.md`
§2B). It prints nothing when it passes. The census commands of `Effect4.Laws.Auto.Positions`
print the positions, the write and read sites and the edges on demand, in a scratch file.
-/

open Lean Meta Elab Command
open Effect4.Laws.Auto.Positions
open Effect4.Program.Typed

namespace Effect4.Laws.Auto.PositionGate

syntax (name := positionGate) "#position_gate " ident+ : command

@[command_elab positionGate] def elabPositionGate : CommandElab := fun stx => do
  let roots := stx[1].getArgs.map (·.getId)
  liftTermElabM do
    let rows ← Effect4.Laws.Auto.TypedSources.readRows
    let mut keys : Array String := #[]
    let mut edgeKeys : Array String := #[]
    let mut edges : Array Edge := #[]
    let mut seen : Array Expr := #[]
    for root in roots do
      let w ← walkOf root
      seen := seen ++ w.seen
      for e in w.edges do
        unless edges.contains e do edges := edges.push e
      for p in w.positions do
        unless keys.contains p.key do keys := keys.push p.key
      for e in w.edges do
        let k := s!"{e.parent}.{e.field}"
        unless edgeKeys.contains k do edgeKeys := edgeKeys.push k
    let rowKeys := rows.map (·.1)
    let coverage ← Effect4.Laws.Auto.TypedSources.ownerCoverage rows roots edges seen
    let missing := keys.filter fun k =>
      !rowKeys.contains k && (!coverage.covered.contains k || coverage.active.contains k)
    -- a row names a position, or an edge (`nested`, `custom`, `each`, `journal`, `refused` on a
    -- field that reaches a structure)
    let stale := rows.filter (fun (k, _) => !keys.contains k && !edgeKeys.contains k && !coverage.ownerKeys.contains k) |>.map (·.1)
    let dup := rowKeys.filter fun k => (rowKeys.filter (· == k)).length > 1
    unless missing.isEmpty do
      throwError "position_gate: {missing.size} positions without a source row:\n{missing.toList}"
    unless stale.isEmpty do
      throwError "position_gate: {stale.length} source rows naming no position:\n{stale}"
    unless dup.isEmpty do
      throwError "position_gate: duplicate rows: {dup.eraseDups}"

end Effect4.Laws.Auto.PositionGate
