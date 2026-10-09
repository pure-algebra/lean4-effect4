import Lean
import Effect4

/-! A finite check of the core import graph after fragment generation. -/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  unless env.contains `Effect4.Program.Denote.Straight do
    throwError "the core lost its existing Straight classifier"
  for name in #[`Effect4.Program.Denote.Looped, `Effect4.Program.Denote.StraightRows,
      `Effect4.Program.Denote.dataRow] do
    if env.contains name then
      throwError "proof-only fragment declaration entered the core: {name}"
  logInfo "PASS fragment boundary: Straight in core; Looped, StraightRows, and dataRow outside core"
