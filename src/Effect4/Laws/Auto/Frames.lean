import Effect4.Laws.Auto.Positions
import ProofGraph.Search

/-!
Frame rules for a structure-valued invariant. For each field of the state, reconstruct the
state with a fresh value. Each invariant clause is either supplied by its old accessor or
becomes an explicit premise. Lean checks the assembled constructor term. In particular,
changing an expected-type field also requires every clause that depends on that field.
-/
namespace Effect4.Laws.Auto.Frames
open Lean Meta Elab Command

structure Result where
  theoremName : Name
  field : Name
  reused : Nat
  required : Nat

/-- Fill the invariant constructor with old projections wherever their types still match.
New hypotheses are abstracted in the returned term, never discharged by an assumption. -/
private def fill (invariant : Name) (old : Expr) : Nat → Nat → Expr → MetaM (Expr × Nat × Nat)
  | 0, _, _ => throwError "frame rules: clause walk ran out of depth at {invariant}"
  | fuel + 1, i, ctor => do
    let ty ← whnf (← inferType ctor)
    match ty with
    | .forallE _ goal _ _ =>
      let prior := mkProj invariant i old
      if ← isDefEq (← inferType prior) goal then
        let (proof, reused, required) ← fill invariant old fuel (i + 1) (mkApp ctor prior)
        return (proof, reused + 1, required)
      else
        withLocalDeclD (Name.mkSimple s!"clause{i}") goal fun h => do
          let (proof, reused, required) ← fill invariant old fuel (i + 1) (mkApp ctor h)
          return (← mkLambdaFVars #[h] proof, reused, required + 1)
    | _ => return (ctor, 0, 0)

/-- Generate one rule per state field. `invariant` must be a structure predicate whose final
parameter is the state record. This explicit shape is checked, not inferred from names. -/
def generate (invariant : Name) : MetaM (Array Result) := do
  let env ← getEnv
  unless isStructure env invariant do throwError "frame rules: {invariant} is not a structure predicate"
  let info ← getConstInfoInduct invariant
  let levels := info.levelParams.map mkLevelParam
  forallTelescope info.type fun params result => do
    unless result.isProp do throwError "frame rules: {invariant} is not a predicate"
    if params.isEmpty then throwError "frame rules: {invariant} has no state parameter"
    let state := params.back!
    let stateTy ← whnf (← inferType state)
    let .const owner ownerLevels := stateTy.getAppFn
      | throwError "frame rules: final parameter of {invariant} is not a record"
    unless isStructure env owner do throwError "frame rules: {owner} is not a structure"
    let fields := getStructureFields env owner
    let some ownerCtor := (← getConstInfoInduct owner).ctors.head?
      | throwError "frame rules: {owner} has no constructor"
    let some invCtor := info.ctors.head? | throwError "frame rules: {invariant} has no constructor"
    let inv := mkAppN (mkConst invariant levels) params
    withLocalDeclD `before inv fun before => do
      let mut out := #[]
      for i in [:fields.size] do
        let field := fields[i]!
        let fieldTy ← inferType (mkProj owner i state)
        let r ← withLocalDeclD `value fieldTy fun value => do
          let values := fields.mapIdx fun j _ => if j == i then value else mkProj owner j state
          let updated := mkAppN (mkConst ownerCtor ownerLevels) (stateTy.getAppArgs ++ values)
          let newParams := params.set! (params.size - 1) updated
          let ctor := mkAppN (mkConst invCtor levels) newParams
          let (body, reused, required) ← fill invariant before 10000 0 ctor
          let proof ← mkLambdaFVars (params ++ #[before, value]) body
          let proposition ← inferType proof
          let theoremName := invariant ++ Name.mkSimple s!"frame_{field}"
          discard <| ProofGraph.addTheorem theoremName info.levelParams proposition proof
          return {theoremName, field, reused, required : Result}
        out := out.push r
      return out

syntax (name := frameRules) "#frame_rules " ident+ : command
@[command_elab frameRules] def elabFrameRules : CommandElab := fun stx => do
  let mut rules : Nat := 0
  let mut reused : Nat := 0
  let mut required : Nat := 0
  for name in stx[1].getArgs do
    let results ← liftTermElabM do generate (← realizeGlobalConstNoOverloadWithInfo name)
    for r in results do
      rules := rules + 1
      reused := reused + r.reused
      required := required + r.required
  logInfo m!"frame rules: {rules} checked theorems, {reused} reused clauses, {required} explicit premises"

end Effect4.Laws.Auto.Frames
