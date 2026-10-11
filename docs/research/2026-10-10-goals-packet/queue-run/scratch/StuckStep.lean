import Test.Dogfood.Scenario.QueueWorkers

/-! Scratch probe: N1's stuck step, located. `#stuck fun total => e` puts `e` in weak head
normal form at the default transparency, the one `rfl` uses. If it is not a constructor, it
follows the stuck discriminant, recursor major or definition down, and prints the chain. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

open Lean Meta Elab Command

namespace StuckProbe

def statusOf : ReducibilityStatus → String
  | .reducible => "reducible"
  | .semireducible => "semireducible"
  | .irreducible => "irreducible"
  | _ => "other"

/-- The chain of stuck positions under `e`, at most `fuel` levels deep. -/
def stuckChain : Nat → Expr → MetaM (List MessageData)
  | 0, _ => return [m!"(fuel out)"]
  | fuel + 1, e => do
    let e ← whnf e
    if (← isConstructorApp e) then
      return [m!"constructor {e.getAppFn}"]
    let f := e.getAppFn
    match f with
    | .const n _ =>
      if let some mApp ← matchMatcherApp? e (alsoCasesOn := true) then
        for d in mApp.discrs do
          let d' ← whnf d
          unless (← isConstructorApp d') do
            let rest ← stuckChain fuel d'
            return m!"match {n} is stuck on a discriminant headed {d'.getAppFn}" :: rest
        return [m!"match {n}: every discriminant is a constructor, yet it did not reduce"]
      if let some (.recInfo r) := (← getEnv).find? n then
        let args := e.getAppArgs
        if h : r.getMajorIdx < args.size then
          let rest ← stuckChain fuel args[r.getMajorIdx]
          return m!"recursor {n} is stuck on its major" :: rest
        return [m!"recursor {n} is partially applied"]
      let rs ← getReducibilityStatus n
      let raw ← withTheReader Core.Context
        (fun ctx => { ctx with options := ctx.options.setBool `smartUnfolding false })
        (unfoldDefinition? e)
      match raw with
      | some e' =>
        let rest ← stuckChain fuel e'
        return m!"definition {n} ({statusOf rs}) does not unfold by smart unfolding" :: rest
      | none =>
        return [m!"definition {n} ({statusOf rs}) does not unfold at this transparency"]
    | .fvar _ => return [m!"a free variable: {e}"]
    | _ => return [m!"head {f}"]

elab "#stuck " t:term : command => liftTermElabM do
  let e ← Term.elabTerm t none
  Term.synthesizeSyntheticMVarsNoPostponing
  let e ← instantiateMVars e
  lambdaTelescope e fun _ body => do
    let chain ← stuckChain 200 body
    logInfo (MessageData.joinSep chain "\n")

end StuckProbe

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Authoring
open Test.Dogfood.Scenario Test.Dogfood.Scenario.QueueWorkers

namespace StuckProbe

def loop0 (total : Nat) : Module NativeOp :=
  { main := iterateWith (bool true)
        { while_ := fun _ => bool true
          body := fun _ => succeed (nat total)
          step := fun c _ => c } }

def scopeOf (m : Module NativeOp) : Env := { layers := [], rows := RowDef.names m.rowDefs, defs := [] }

-- 1. The minted loop alone, at the empty scope (control: `rfl` closes it).
#stuck fun total : Nat => (loop0 total).main {} []

-- 2. The minted loop's module.
#stuck fun total : Nat => elaborateModule (loop0 total)

-- 3. The crew's main program at the module's scope.
#stuck fun total : Nat => (crew total).main (scopeOf (crew total)) []

-- 4. The crew's module.
#stuck fun total : Nat => elaborateModule (crew total)

end StuckProbe
