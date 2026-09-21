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
§2B). It also prints the count per source kind, which is the shape of the invariant.
-/

open Lean Meta Elab Command
open Effect4.Laws.Auto.Positions
open Effect4.Program.Typed

namespace Effect4.Laws.Auto.PositionGate

def kindLabel : Source → String
  | .program _ => "program"
  | .continuation _ => "continuation"
  | .value _ => "value"
  | .exit _ => "exit"
  | .cause _ => "cause"
  | .hook _ => "hook"
  | .column _ _ => "column"
  | .journal => "journal"
  | .custom _ => "custom"
  | .owner _ => "owner"
  | .refused _ => "refused"
  | .nested _ => "nested"

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
    -- a row names a position, or an edge (`nested`, `custom`, `journal`, `refused` on a field
    -- that reaches a structure)
    let stale := rows.filter (fun (k, _) => !keys.contains k && !edgeKeys.contains k && !coverage.ownerKeys.contains k) |>.map (·.1)
    let dup := rowKeys.filter fun k => (rowKeys.filter (· == k)).length > 1
    let mut byKind : Array (String × Nat) := #[]
    for key in keys do
      let label := match rows.find? (·.1 == key) with
        | some (_, source) => kindLabel source
        | none => if coverage.covered.contains key && !coverage.active.contains key
          then "owner" else "missing"
      match byKind.findIdx? (·.1 == label) with
      | some i => byKind := byKind.modify i fun (label, n) => (label, n + 1)
      | none => byKind := byKind.push (label, 1)
    let mut report := m!"{keys.size} positions from {roots.size} roots, {rows.length} source rows"
    for (l, n) in byKind do report := report ++ m!"\n  {n}\t{l}"
    for (k, s) in rows do
      if let .refused r := s then report := report ++ m!"\n  refused\t{k}\t{r}"
    logInfo report
    unless missing.isEmpty do
      throwError "position_gate: {missing.size} positions without a source row:\n{missing.toList}"
    unless stale.isEmpty do
      throwError "position_gate: {stale.length} source rows naming no position:\n{stale}"
    unless dup.isEmpty do
      throwError "position_gate: duplicate rows: {dup.eraseDups}"

end Effect4.Laws.Auto.PositionGate
