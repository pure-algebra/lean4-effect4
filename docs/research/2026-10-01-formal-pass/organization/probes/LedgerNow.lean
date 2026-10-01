import Effect4
import Effect4.Laws

/-!
Seat ORGANIZATION probe (2026-10-01): the obligation ledger as loaded from the production roots
(`Effect4`, `Effect4.Laws`; no `Test`). Lists every declared goal (a theorem concluding
`ProofGraph.Obligation p`), whether a checked proof sits beside it (`<goal>.checked`), and whether
a placeholder sits beside it (`<goal>.wanted`), one line per goal with its module, so the open
list can be compared with `#proof_wanted` sites, the scopes `#typed_state_obligations` checks, and
the architecture map's 403/370/33 (which also loads `Test` and the tool roots).
Nothing is asserted.
-/

open Lean Elab Command

def concludesObligation : Expr → Bool
  | .forallE _ _ body _ => concludesObligation body
  | e => e.isAppOfArity ``ProofGraph.Obligation 1

#eval show CommandElabM Unit from do
  let env ← getEnv
  let mods := env.header.moduleNames
  let mut rows : Array String := #[]
  let mut declared : Nat := 0
  let mut proved : Nat := 0
  let mut wanted : Nat := 0
  for (name, ci) in env.constants.toList do
    if let .thmInfo t := ci then
      if concludesObligation t.type then
        declared := declared + 1
        let c := env.contains (name ++ `checked)
        let w := env.contains (name ++ `wanted)
        if c then proved := proved + 1
        if w then wanted := wanted + 1
        let m := match env.getModuleIdxFor? name with
          | some i => mods[i.toNat]!.toString
          | none => "?"
        rows := rows.push s!"{if c then "proved" else if w then "wanted" else "NEITHER"}\t{m}\t{name}"
  let sorted := rows.qsort (· < ·)
  logInfo m!"ledger (production roots): {declared} declared, {proved} proved, {wanted} wanted, {declared - proved - wanted} neither\n{"\n".intercalate sorted.toList}"
