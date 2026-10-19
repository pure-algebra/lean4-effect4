import Effect4
import Lean
open Lean Meta Elab Command
run_cmd liftTermElabM do
  let info ← getConstInfoInduct ``Effect4.ServiceName
  for cn in info.ctors do
    let ci ← getConstInfoCtor cn
    forallTelescopeReducing ci.type fun xs _ => do
      for x in xs[ci.numParams:] do
        let ty ← whnf (← inferType x)
        if (ty.find? (fun e => e.isConstOf ``Nat)).isSome then
          logInfo m!"NAT_FIELD {cn} {← ppExpr ty}"
  let info ← getConstInfoInduct ``Effect4.ServiceTypeCode
  for cn in info.ctors do
    let ci ← getConstInfoCtor cn
    forallTelescopeReducing ci.type fun xs _ => do
      for x in xs[ci.numParams:] do
        let ty ← whnf (← inferType x)
        if (ty.find? (fun e => e.isConstOf ``Nat)).isSome then
          logInfo m!"NAT_FIELD {cn} {← ppExpr ty}"
  let info ← getConstInfoInduct ``Effect4.ServiceKey
  for cn in info.ctors do
    let ci ← getConstInfoCtor cn
    forallTelescopeReducing ci.type fun xs _ => do
      for x in xs[ci.numParams:] do
        let ty ← whnf (← inferType x)
        if (ty.find? (fun e => e.isConstOf ``Nat)).isSome then
          logInfo m!"NAT_FIELD {cn} {← ppExpr ty}"
  let info ← getConstInfoInduct ``Effect4.Program.Ty
  for cn in info.ctors do
    let ci ← getConstInfoCtor cn
    forallTelescopeReducing ci.type fun xs _ => do
      for x in xs[ci.numParams:] do
        let ty ← whnf (← inferType x)
        if (ty.find? (fun e => e.isConstOf ``Nat)).isSome then
          logInfo m!"NAT_FIELD {cn} {← ppExpr ty}"
  let info ← getConstInfoInduct ``Effect4.Program.Lit
  for cn in info.ctors do
    let ci ← getConstInfoCtor cn
    forallTelescopeReducing ci.type fun xs _ => do
      for x in xs[ci.numParams:] do
        let ty ← whnf (← inferType x)
        if (ty.find? (fun e => e.isConstOf ``Nat)).isSome then
          logInfo m!"NAT_FIELD {cn} {← ppExpr ty}"
  let info ← getConstInfoInduct ``Effect4.Program.FieldReadMode
  for cn in info.ctors do
    let ci ← getConstInfoCtor cn
    forallTelescopeReducing ci.type fun xs _ => do
      for x in xs[ci.numParams:] do
        let ty ← whnf (← inferType x)
        if (ty.find? (fun e => e.isConstOf ``Nat)).isSome then
          logInfo m!"NAT_FIELD {cn} {← ppExpr ty}"
  let info ← getConstInfoInduct ``Effect4.Program.Term
  for cn in info.ctors do
    let ci ← getConstInfoCtor cn
    forallTelescopeReducing ci.type fun xs _ => do
      for x in xs[ci.numParams:] do
        let ty ← whnf (← inferType x)
        if (ty.find? (fun e => e.isConstOf ``Nat)).isSome then
          logInfo m!"NAT_FIELD {cn} {← ppExpr ty}"
  let info ← getConstInfoInduct ``Effect4.Program.Terms
  for cn in info.ctors do
    let ci ← getConstInfoCtor cn
    forallTelescopeReducing ci.type fun xs _ => do
      for x in xs[ci.numParams:] do
        let ty ← whnf (← inferType x)
        if (ty.find? (fun e => e.isConstOf ``Nat)).isSome then
          logInfo m!"NAT_FIELD {cn} {← ppExpr ty}"
  let info ← getConstInfoInduct ``Effect4.Program.CauseTerm
  for cn in info.ctors do
    let ci ← getConstInfoCtor cn
    forallTelescopeReducing ci.type fun xs _ => do
      for x in xs[ci.numParams:] do
        let ty ← whnf (← inferType x)
        if (ty.find? (fun e => e.isConstOf ``Nat)).isSome then
          logInfo m!"NAT_FIELD {cn} {← ppExpr ty}"
  let info ← getConstInfoInduct ``Effect4.Supervision.MaskMode
  for cn in info.ctors do
    let ci ← getConstInfoCtor cn
    forallTelescopeReducing ci.type fun xs _ => do
      for x in xs[ci.numParams:] do
        let ty ← whnf (← inferType x)
        if (ty.find? (fun e => e.isConstOf ``Nat)).isSome then
          logInfo m!"NAT_FIELD {cn} {← ppExpr ty}"
  let info ← getConstInfoInduct ``Effect4.Supervision.ForkOptions
  for cn in info.ctors do
    let ci ← getConstInfoCtor cn
    forallTelescopeReducing ci.type fun xs _ => do
      for x in xs[ci.numParams:] do
        let ty ← whnf (← inferType x)
        if (ty.find? (fun e => e.isConstOf ``Nat)).isSome then
          logInfo m!"NAT_FIELD {cn} {← ppExpr ty}"
  let info ← getConstInfoInduct ``Effect4.Supervision.ObserverMode
  for cn in info.ctors do
    let ci ← getConstInfoCtor cn
    forallTelescopeReducing ci.type fun xs _ => do
      for x in xs[ci.numParams:] do
        let ty ← whnf (← inferType x)
        if (ty.find? (fun e => e.isConstOf ``Nat)).isSome then
          logInfo m!"NAT_FIELD {cn} {← ppExpr ty}"
  let info ← getConstInfoInduct ``Effect4.FinalizerStrategy
  for cn in info.ctors do
    let ci ← getConstInfoCtor cn
    forallTelescopeReducing ci.type fun xs _ => do
      for x in xs[ci.numParams:] do
        let ty ← whnf (← inferType x)
        if (ty.find? (fun e => e.isConstOf ``Nat)).isSome then
          logInfo m!"NAT_FIELD {cn} {← ppExpr ty}"
  let info ← getConstInfoInduct ``Effect4.Program.NativeOp
  for cn in info.ctors do
    let ci ← getConstInfoCtor cn
    forallTelescopeReducing ci.type fun xs _ => do
      for x in xs[ci.numParams:] do
        let ty ← whnf (← inferType x)
        if (ty.find? (fun e => e.isConstOf ``Nat)).isSome then
          logInfo m!"NAT_FIELD {cn} {← ppExpr ty}"
  let info ← getConstInfoInduct ``Effect4.Program.Decision
  for cn in info.ctors do
    let ci ← getConstInfoCtor cn
    forallTelescopeReducing ci.type fun xs _ => do
      for x in xs[ci.numParams:] do
        let ty ← whnf (← inferType x)
        if (ty.find? (fun e => e.isConstOf ``Nat)).isSome then
          logInfo m!"NAT_FIELD {cn} {← ppExpr ty}"
  let info ← getConstInfoInduct ``Effect4.Program.DefRole
  for cn in info.ctors do
    let ci ← getConstInfoCtor cn
    forallTelescopeReducing ci.type fun xs _ => do
      for x in xs[ci.numParams:] do
        let ty ← whnf (← inferType x)
        if (ty.find? (fun e => e.isConstOf ``Nat)).isSome then
          logInfo m!"NAT_FIELD {cn} {← ppExpr ty}"
  let info ← getConstInfoInduct ``Effect4.Program.ParamDecl
  for cn in info.ctors do
    let ci ← getConstInfoCtor cn
    forallTelescopeReducing ci.type fun xs _ => do
      for x in xs[ci.numParams:] do
        let ty ← whnf (← inferType x)
        if (ty.find? (fun e => e.isConstOf ``Nat)).isSome then
          logInfo m!"NAT_FIELD {cn} {← ppExpr ty}"
  let info ← getConstInfoInduct ``Effect4.Program.DefDecl
  for cn in info.ctors do
    let ci ← getConstInfoCtor cn
    forallTelescopeReducing ci.type fun xs _ => do
      for x in xs[ci.numParams:] do
        let ty ← whnf (← inferType x)
        if (ty.find? (fun e => e.isConstOf ``Nat)).isSome then
          logInfo m!"NAT_FIELD {cn} {← ppExpr ty}"
  let info ← getConstInfoInduct ``Effect4.Program.Eff
  for cn in info.ctors do
    let ci ← getConstInfoCtor cn
    forallTelescopeReducing ci.type fun xs _ => do
      for x in xs[ci.numParams:] do
        let ty ← whnf (← inferType x)
        if (ty.find? (fun e => e.isConstOf ``Nat)).isSome then
          logInfo m!"NAT_FIELD {cn} {← ppExpr ty}"
  let info ← getConstInfoInduct ``Effect4.Program.Stmt
  for cn in info.ctors do
    let ci ← getConstInfoCtor cn
    forallTelescopeReducing ci.type fun xs _ => do
      for x in xs[ci.numParams:] do
        let ty ← whnf (← inferType x)
        if (ty.find? (fun e => e.isConstOf ``Nat)).isSome then
          logInfo m!"NAT_FIELD {cn} {← ppExpr ty}"
  let info ← getConstInfoInduct ``Effect4.Program.Stmts
  for cn in info.ctors do
    let ci ← getConstInfoCtor cn
    forallTelescopeReducing ci.type fun xs _ => do
      for x in xs[ci.numParams:] do
        let ty ← whnf (← inferType x)
        if (ty.find? (fun e => e.isConstOf ``Nat)).isSome then
          logInfo m!"NAT_FIELD {cn} {← ppExpr ty}"
  let info ← getConstInfoInduct ``Effect4.Program.Effs
  for cn in info.ctors do
    let ci ← getConstInfoCtor cn
    forallTelescopeReducing ci.type fun xs _ => do
      for x in xs[ci.numParams:] do
        let ty ← whnf (← inferType x)
        if (ty.find? (fun e => e.isConstOf ``Nat)).isSome then
          logInfo m!"NAT_FIELD {cn} {← ppExpr ty}"
  let info ← getConstInfoInduct ``Effect4.Program.ActionTerm
  for cn in info.ctors do
    let ci ← getConstInfoCtor cn
    forallTelescopeReducing ci.type fun xs _ => do
      for x in xs[ci.numParams:] do
        let ty ← whnf (← inferType x)
        if (ty.find? (fun e => e.isConstOf ``Nat)).isSome then
          logInfo m!"NAT_FIELD {cn} {← ppExpr ty}"
  let info ← getConstInfoInduct ``Effect4.Program.LayerTerm
  for cn in info.ctors do
    let ci ← getConstInfoCtor cn
    forallTelescopeReducing ci.type fun xs _ => do
      for x in xs[ci.numParams:] do
        let ty ← whnf (← inferType x)
        if (ty.find? (fun e => e.isConstOf ``Nat)).isSome then
          logInfo m!"NAT_FIELD {cn} {← ppExpr ty}"
  let info ← getConstInfoInduct ``Effect4.Program.LayerTerms
  for cn in info.ctors do
    let ci ← getConstInfoCtor cn
    forallTelescopeReducing ci.type fun xs _ => do
      for x in xs[ci.numParams:] do
        let ty ← whnf (← inferType x)
        if (ty.find? (fun e => e.isConstOf ``Nat)).isSome then
          logInfo m!"NAT_FIELD {cn} {← ppExpr ty}"
  let info ← getConstInfoInduct ``Effect4.Program.RowKind
  for cn in info.ctors do
    let ci ← getConstInfoCtor cn
    forallTelescopeReducing ci.type fun xs _ => do
      for x in xs[ci.numParams:] do
        let ty ← whnf (← inferType x)
        if (ty.find? (fun e => e.isConstOf ``Nat)).isSome then
          logInfo m!"NAT_FIELD {cn} {← ppExpr ty}"
  let info ← getConstInfoInduct ``Effect4.Program.RowShape
  for cn in info.ctors do
    let ci ← getConstInfoCtor cn
    forallTelescopeReducing ci.type fun xs _ => do
      for x in xs[ci.numParams:] do
        let ty ← whnf (← inferType x)
        if (ty.find? (fun e => e.isConstOf ``Nat)).isSome then
          logInfo m!"NAT_FIELD {cn} {← ppExpr ty}"
  let info ← getConstInfoInduct ``Effect4.Program.Registration
  for cn in info.ctors do
    let ci ← getConstInfoCtor cn
    forallTelescopeReducing ci.type fun xs _ => do
      for x in xs[ci.numParams:] do
        let ty ← whnf (← inferType x)
        if (ty.find? (fun e => e.isConstOf ``Nat)).isSome then
          logInfo m!"NAT_FIELD {cn} {← ppExpr ty}"
  let info ← getConstInfoInduct ``Effect4.Program.RowArg
  for cn in info.ctors do
    let ci ← getConstInfoCtor cn
    forallTelescopeReducing ci.type fun xs _ => do
      for x in xs[ci.numParams:] do
        let ty ← whnf (← inferType x)
        if (ty.find? (fun e => e.isConstOf ``Nat)).isSome then
          logInfo m!"NAT_FIELD {cn} {← ppExpr ty}"
  let info ← getConstInfoInduct ``Effect4.Program.Row
  for cn in info.ctors do
    let ci ← getConstInfoCtor cn
    forallTelescopeReducing ci.type fun xs _ => do
      for x in xs[ci.numParams:] do
        let ty ← whnf (← inferType x)
        if (ty.find? (fun e => e.isConstOf ``Nat)).isSome then
          logInfo m!"NAT_FIELD {cn} {← ppExpr ty}"
  let info ← getConstInfoInduct ``Effect4.Program.EffTy
  for cn in info.ctors do
    let ci ← getConstInfoCtor cn
    forallTelescopeReducing ci.type fun xs _ => do
      for x in xs[ci.numParams:] do
        let ty ← whnf (← inferType x)
        if (ty.find? (fun e => e.isConstOf ``Nat)).isSome then
          logInfo m!"NAT_FIELD {cn} {← ppExpr ty}"
  let info ← getConstInfoInduct ``Effect4.Store.Val
  for cn in info.ctors do
    let ci ← getConstInfoCtor cn
    forallTelescopeReducing ci.type fun xs _ => do
      for x in xs[ci.numParams:] do
        let ty ← whnf (← inferType x)
        if (ty.find? (fun e => e.isConstOf ``Nat)).isSome then
          logInfo m!"NAT_FIELD {cn} {← ppExpr ty}"
  let info ← getConstInfoInduct ``Effect4.Machine.Err
  for cn in info.ctors do
    let ci ← getConstInfoCtor cn
    forallTelescopeReducing ci.type fun xs _ => do
      for x in xs[ci.numParams:] do
        let ty ← whnf (← inferType x)
        if (ty.find? (fun e => e.isConstOf ``Nat)).isSome then
          logInfo m!"NAT_FIELD {cn} {← ppExpr ty}"
  let info ← getConstInfoInduct ``Effect4.Machine.Defect
  for cn in info.ctors do
    let ci ← getConstInfoCtor cn
    forallTelescopeReducing ci.type fun xs _ => do
      for x in xs[ci.numParams:] do
        let ty ← whnf (← inferType x)
        if (ty.find? (fun e => e.isConstOf ``Nat)).isSome then
          logInfo m!"NAT_FIELD {cn} {← ppExpr ty}"
  let info ← getConstInfoInduct ``Effect4.Reason
  for cn in info.ctors do
    let ci ← getConstInfoCtor cn
    forallTelescopeReducing ci.type fun xs _ => do
      for x in xs[ci.numParams:] do
        let ty ← whnf (← inferType x)
        if (ty.find? (fun e => e.isConstOf ``Nat)).isSome then
          logInfo m!"NAT_FIELD {cn} {← ppExpr ty}"
  let info ← getConstInfoInduct ``Effect4.Exit
  for cn in info.ctors do
    let ci ← getConstInfoCtor cn
    forallTelescopeReducing ci.type fun xs _ => do
      for x in xs[ci.numParams:] do
        let ty ← whnf (← inferType x)
        if (ty.find? (fun e => e.isConstOf ``Nat)).isSome then
          logInfo m!"NAT_FIELD {cn} {← ppExpr ty}"
  let info ← getConstInfoInduct ``Effect4.Machine.Completion
  for cn in info.ctors do
    let ci ← getConstInfoCtor cn
    forallTelescopeReducing ci.type fun xs _ => do
      for x in xs[ci.numParams:] do
        let ty ← whnf (← inferType x)
        if (ty.find? (fun e => e.isConstOf ``Nat)).isSome then
          logInfo m!"NAT_FIELD {cn} {← ppExpr ty}"
