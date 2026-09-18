import Effect4.Laws.Program.InterpR

/-! Probe Q2: derive the value-holding positions reachable from `RState` from the types. -/

open Lean Meta Elab Command

namespace Probe

/-- Where the walk stops and reports. -/
def carriers : List Name :=
  [`Effect4.Store.Val, `Effect4.Machine.Val, `Effect4.Exit, `Effect4.Cause, `Effects.Program, `Effect4.Machine.Program,
   `Effect4.Prim, `Effect4.Reason]

/-- Wrappers the walk sees through. -/
def wrappers : List Name := [`List, `Option, `Prod, `Array]

structure Position where
  owner : Name
  field : String
  shape : String
  carrier : Name

/-- Instantiate the leading binders of a constructor type with the type's arguments. -/
def instArgs : Expr → List Expr → Option Expr
  | e, [] => some e
  | .forallE _ _ b _, a :: rest => instArgs (b.instantiate1 a) rest
  | _, _ => none

partial def walkType (owner : Name) (field : String) (shape : String) (ty : Expr)
    (seen : Array Name) : MetaM (Array Position × Array Name) := do
  let ty ← whnf (← instantiateMVars ty)
  match ty with
  | .forallE _ d b _ =>
    -- a function position: report the codomain under `→`
    let dText ← ppExpr d
    walkType owner field (shape ++ s!"({dText} → _)") b seen
  | _ =>
  let fn := ty.getAppFn
  let args := ty.getAppArgs
  match fn with
  | .const n _ =>
    if carriers.contains n then
      return (#[{ owner, field, shape, carrier := n }], seen)
    if wrappers.contains n then
      let mut acc := #[]
      let mut seen := seen
      for a in args do
        let (ps, s) ← walkType owner field (shape ++ s!"{n.getString!} ") a seen
        acc := acc ++ ps; seen := s
      return (acc, seen)
    -- a structure or inductive: recurse into constructor fields once per type constant
    if seen.contains n then return (#[], seen)
    match (← getEnv).find? n with
    | some (.inductInfo iv) =>
      if iv.isRec then
        if args.any (fun a => carriers.any fun c => (a.getUsedConstants).contains c) then
          logWarning m!"REFUSED {owner}.{field}: recursive type {n} over a carrier"
        return (#[], seen)
      let mut acc := #[]
      let mut seen := seen.push n
      for c in iv.ctors do
        let ci ← getConstInfoCtor c
        let cty := ci.type.instantiateLevelParams ci.levelParams (fn.constLevels!)
        let some cty := instArgs cty args.toList | do
          logWarning m!"skipped {n}: {args.size} args do not fit its constructor"; return (#[], seen)
        let (ps, s) ← forallTelescope cty fun xs _ => do
          let mut acc := #[]
          let mut seen := seen
          for x in xs do
            let xty ← inferType x
            let name := (← x.fvarId!.getDecl).userName.toString
            let label := if iv.ctors.length == 1 then name else s!"{c.getString!}.{name}"
            let (ps, s) ← walkType n label "" xty seen
            acc := acc ++ ps; seen := s
          return (acc, seen)
        acc := acc ++ ps; seen := s
      return (acc, seen)
    | _ =>
      -- not an inductive: refuse if a carrier hides in its arguments
      if args.any (fun a => carriers.any fun c => (a.getUsedConstants).contains c) then
        logWarning m!"REFUSED {owner}.{field}: unknown type constructor {n} over a carrier"
      return (#[], seen)
  | _ => return (#[], seen)

elab "#positions " id:ident : command => do
  let root := id.getId
  liftTermElabM do
    let ci ← getConstInfo root
    let v := match ci.value? with
      | some v => v
      | none => mkConst root (ci.levelParams.map mkLevelParam)
    let (ps, _) ← walkType root "" "" v #[]
    let mut report := m!"{ps.size} positions from {root}"
    for p in ps do
      report := report ++ m!"\n  {p.owner}.{p.field} : {p.shape}{p.carrier}"
    logInfo report

end Probe

#positions Effect4.Machine.Ctx
#positions Effect4.Program.Sched.RInterp
#positions Effect4.Program.Sched.RIter
