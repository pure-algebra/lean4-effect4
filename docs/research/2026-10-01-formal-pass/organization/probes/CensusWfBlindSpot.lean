import Effect4
import Effect4.Laws
import Effect4.Laws.Auto.Traversals

/-!
Seat ORGANIZATION probe (2026-10-01): does `#traversal_census` see well-founded hand
traversals? The instrument classifies a row `wf` only when the definition's own value uses
`WellFounded.fix`; Lean compiles a well-founded definition of two or more explicit arguments
through an internal `_unary` (or `_mutual`) helper, which `definitionsUnder` filters out as an
internal detail. This probe lists, per free object, every taker whose value calls such a
helper whose own value reaches `WellFounded.fix` or `WellFounded.Nat.fix` (the toolchain's
fixpoint for a `Nat`-valued measure; the census looks only for `WellFounded.fix`) — the rows the census prints as `opaque` or
`delegates` though they are hand traversals by well-founded recursion.

Red control: `Effect4.Program.Ty.sub` (`Program/Ty.lean`, `termination_by sizeOf a + sizeOf b`)
must be listed; if it is not, the probe is wrong, not the census.
-/

open Lean Elab Meta Command Effect4.Laws.Auto

/-- Internal helpers a definition's value calls that are well-founded fixpoints. -/
def wfHelpers (env : Environment) (value : Expr) : Array Name :=
  value.getUsedConstants.filter fun c =>
    (c.isInternalDetail || c.isInternal ||
      c.components.any (fun s => s.toString == "_unary" || s.toString == "_mutual")) &&
    match env.find? c with
    | some (.defnInfo d) =>
      let u := d.value.getUsedConstants
      u.contains ``WellFounded.fix || u.contains ``WellFounded.Nat.fix
    | _ => false

syntax (name := wfBlind) "#wf_blind_spot " ident : command

@[command_elab wfBlind] def elabWfBlind : CommandElab := fun stx => do
  let root := stx[1].getId
  let family ← liftCoreM (familyOf root)
  let env ← getEnv
  let defs := definitionsUnder env `Effect4
  let folds := foldsOf family defs
  let mut out : Array String := #[]
  for (n, m, type, value) in defs do
    if folds.contains n then continue
    if (← liftTermElabM (domainOf family type)).isNone then continue
    let hs := wfHelpers env value
    if hs.isEmpty then continue
    let direct := value.getUsedConstants.contains ``WellFounded.fix ||
      value.getUsedConstants.contains ``WellFounded.Nat.fix
    out := out.push s!"{m}\t{n}\tdirect-fix={direct}\thelpers={hs.toList}"
  logInfo m!"#wf_blind_spot {root}: {out.size} well-founded takers\n{"\n".intercalate out.toList}"

#wf_blind_spot Effect4.Program.Eff
#wf_blind_spot Effect4.Program.Ty
#wf_blind_spot Effect4.Program.Term
#wf_blind_spot Effect4.Representation
#wf_blind_spot Effect4.Store.Val
