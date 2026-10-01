import Effect4

/-!
Seat G probe (step 5, row 8 item ii): measure, before changing `ShapeDoc.document`, which shape
documents of the tree repeat a key in their definition table, and whether the repeated bindings
agree. Every closed instance of `Effect4.Store.Canonical` in the core root is read
(`Content` extends it, so every store kind is among them); for each, its table's keys are counted
and the rendered bodies (`renderDef`, the `Representation` that `ShapeDoc.document` puts in the
references) of each repeated key are compared with `Representation`'s `DecidableEq`.
-/

open Lean Meta Elab Command Effect4 Effect4.Store

namespace SeatG.RepeatedDefs

/-- Each key bound more than once: the key, how many bindings, and whether all rendered bodies
are equal to the first. -/
def repeats (defs : List (String × Shape)) : List (String × Nat × Bool) :=
  let keys := (defs.map (·.1)).eraseDups
  keys.filterMap fun k =>
    let bodies := (defs.filter (·.1 == k)).map fun d => renderDef d.1 d.2
    if bodies.length ≤ 1 then none
    else some (k, bodies.length, bodies.all (· == bodies.headD (render .unit)))

/-- The size of a table and its distinct keys. -/
def sizes (defs : List (String × Shape)) : Nat × Nat := (defs.length, (defs.map (·.1)).eraseDups.length)

elab "#repeated_defs" : command => do
  let env ← getEnv
  let mut rows : Array String := #[]
  let mut total : Nat := 0
  let mut withRepeat : Nat := 0
  let mut conflicting : Nat := 0
  for (name, info) in env.constants.toList do
    unless (← liftCoreM (isInstance name)) do continue
    let ty := info.type
    unless ty.isAppOfArity ``Effect4.Store.Canonical 1 do continue
    let carrier := ty.appArg!
    if carrier.hasLooseBVars || carrier.hasFVar || carrier.hasMVar then continue
    if !info.levelParams.isEmpty then continue
    total := total + 1
    let shapeE := mkApp2 (mkConst ``Effect4.Store.Canonical.shape) carrier (mkConst name)
    let defsE := mkApp (mkConst ``Effect4.Store.ShapeDoc.defs) shapeE
    let rep ← liftTermElabM <| unsafe evalExpr (List (String × Nat × Bool))
      (mkApp (mkConst ``List [Level.zero]) (mkApp2 (mkConst ``Prod [Level.zero, Level.zero]) (mkConst ``String)
        (mkApp2 (mkConst ``Prod [Level.zero, Level.zero]) (mkConst ``Nat) (mkConst ``Bool))))
      (mkApp (mkConst ``SeatG.RepeatedDefs.repeats) defsE)
    let sz ← liftTermElabM <| unsafe evalExpr (Nat × Nat)
      (mkApp2 (mkConst ``Prod [Level.zero, Level.zero]) (mkConst ``Nat) (mkConst ``Nat))
      (mkApp (mkConst ``SeatG.RepeatedDefs.sizes) defsE)
    unless rep.isEmpty do
      withRepeat := withRepeat + 1
      if rep.any (fun r => !r.2.2) then conflicting := conflicting + 1
      rows := rows.push s!"{carrier}\t{sz.1} bindings, {sz.2} keys\t{rep}"
  let sorted := rows.qsort (· < ·)
  logInfo m!"closed Canonical instances: {total}; with a repeated key: {withRepeat}; with a repeated key whose bodies differ: {conflicting}\n{"\n".intercalate sorted.toList}"

#repeated_defs

end SeatG.RepeatedDefs
