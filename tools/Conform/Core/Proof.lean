import Lean
import Lean.Util.CollectAxioms

/-!
Checked theorem references for reports. The elaborator freezes the actual proposition,
including its binders and universe parameters. A later environment must supply a theorem
of that proposition and within the stated transitive axiom policy. Names alone are not evidence.
This reflection data is tooling only; it never enters stored program content.
-/
namespace Conform
open Lean Meta Elab Term

structure ProofRef where
  name : Name
  levels : List Name
  proposition : Expr

def ProofRef.validate (p : ProofRef) : MetaM (Except String Unit) := do
  let some (.thmInfo t) := (← getEnv).find? p.name
    | return .error s!"{p.name}: missing or not a theorem"
  if t.type.hasMVar || t.type.hasFVar || p.proposition.hasMVar || p.proposition.hasFVar then
    return .error s!"{p.name}: open proposition"
  if t.levelParams != p.levels then return .error s!"{p.name}: universe parameters changed"
  unless ← isDefEq t.type p.proposition do
    return .error s!"{p.name}: proposition changed"
  let extra := (← collectAxioms p.name).filter fun n => ![``propext, ``Quot.sound].contains n
  unless extra.isEmpty do return .error s!"{p.name}: disallowed axioms {extra}"
  return .ok ()

private def quoteLevel : Level → Expr
  | .zero => mkConst ``Level.zero
  | .succ u => mkApp (mkConst ``Level.succ) (quoteLevel u)
  | .max u v => mkApp2 (mkConst ``Level.max) (quoteLevel u) (quoteLevel v)
  | .imax u v => mkApp2 (mkConst ``Level.imax) (quoteLevel u) (quoteLevel v)
  | .param n => mkApp (mkConst ``Level.param) (toExpr n)
  | .mvar _ => panic! "universe metavariable in a closed declaration"

private def quoteLevels (us : List Level) : Expr :=
  us.foldr (fun u tail => mkApp3 (mkConst ``List.cons [Level.zero])
    (mkConst ``Level) (quoteLevel u) tail) (mkApp (mkConst ``List.nil [Level.zero]) (mkConst ``Level))

private def quoteBinder : BinderInfo → Expr
  | .default => mkConst ``BinderInfo.default
  | .implicit => mkConst ``BinderInfo.implicit
  | .strictImplicit => mkConst ``BinderInfo.strictImplicit
  | .instImplicit => mkConst ``BinderInfo.instImplicit

/-- Quote closed kernel syntax, preserving all type arguments. -/
private def quoteClosed : Expr → MetaM Expr
  | .bvar i => pure <| mkApp (mkConst ``Expr.bvar) (toExpr i)
  | .sort u => pure <| mkApp (mkConst ``Expr.sort) (quoteLevel u)
  | .const n us => pure <| mkApp2 (mkConst ``Expr.const) (toExpr n) (quoteLevels us)
  | .app f a => do
    return mkApp2 (mkConst ``Expr.app) (← quoteClosed f) (← quoteClosed a)
  | .lam n t b bi => do
    return mkApp4 (mkConst ``Expr.lam) (toExpr n)
      (← quoteClosed t) (← quoteClosed b) (quoteBinder bi)
  | .forallE n t b bi => do
    return mkApp4 (mkConst ``Expr.forallE) (toExpr n)
      (← quoteClosed t) (← quoteClosed b) (quoteBinder bi)
  | .letE n t v b nd => do
    return mkApp5 (mkConst ``Expr.letE) (toExpr n)
      (← quoteClosed t) (← quoteClosed v) (← quoteClosed b) (toExpr nd)
  | .lit l => pure <| mkApp (mkConst ``Expr.lit) (toExpr l)
  | .mdata _ b => quoteClosed b
  | .proj n i b => do
    return mkApp3 (mkConst ``Expr.proj) (toExpr n) (toExpr i) (← quoteClosed b)
  | _ => throwError "proof reference contains a free variable or metavariable"

elab "checked_theorem% " n:ident : term => do
  let name ← realizeGlobalConstNoOverloadWithInfo n
  let .thmInfo t ← getConstInfo name | throwError "{name} is not a theorem"
  let p : ProofRef := ⟨name, t.levelParams, t.type⟩
  if let .error why ← p.validate then throwError why
  return mkApp3 (mkConst ``ProofRef.mk) (toExpr name) (toExpr t.levelParams) (← quoteClosed t.type)

end Conform
