import Lean
import ProbeQ.TyCore

/-!
# Q1 red controls: Lean 4.33.1's own instruments on the nested `ProbeQ.Ty`

Seat Q probe (2026-10-01). With `record (fields : List (String × Ty))` appended and no generated
companion imported (this file imports `ProbeQ.TyCore` only), each instrument the tree leans on
for `Ty` today refuses or degrades. The messages are asserted, so this file compiles exactly
when the refusals are what the note says (`Lean/Elab/Deriving/DecEq.lean`:
`if indVal.isNested then return false`).
-/

namespace Q1Red

/-- error: None of the deriving handlers for class `DecidableEq` applied to `ProbeQ.Ty` -/
#guard_msgs in
deriving instance DecidableEq for ProbeQ.Ty

/--
error: The `induction` tactic does not support the type `ProbeQ.Ty` because it is a nested inductive type

Hint: Consider using the `cases` tactic instead
-/
#guard_msgs in
example (t : ProbeQ.Ty) : True := by
  induction t <;> trivial

-- The derived `Repr` elaborates, but its function is an `opaque` over a `partial`
-- `_unsafe_rec`: the shape the trust gate refuses (`Store/Carrier/Val.lean:173-177`).
deriving instance Repr for ProbeQ.Ty

open Lean Elab Command in
/-- The kinds of the declarations the derived `Repr` added, read off the environment. -/
def reprKinds : CommandElabM (List String) := do
  let env ← getEnv
  let mut out : List String := []
  for (n, c) in env.constants.map₂.toList do
    if (`Q1Red).isPrefixOf n && (n.toString.splitOn "instReprTy").length > 1 then
      let kind := match c with
        | .defnInfo d => match d.safety with
          | .partial => "partial def" | .unsafe => "unsafe def" | .safe => "def"
        | .opaqueInfo _ => "opaque"
        | _ => "other"
      out := out ++ [s!"{n.componentsRev.head!}: {kind}"]
  return out.mergeSort (· ≤ ·)

/--
info: [_unsafe_rec: partial def, instReprTy_q1: def, match_1: def, repr: opaque]
-/
#guard_msgs in
open Lean Elab Command in
#eval show CommandElabM Unit from do logInfo m!"{← reprKinds}"

end Q1Red
