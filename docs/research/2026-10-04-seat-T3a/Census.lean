import Effect4
import Effect4.Laws
import Test.All
open Lean

/-! Measurement for seat T3a's design note (phase 1). Which declarations of the `Effect4` and
`Test` roots name each listed constant directly, in their type or their value? Auxiliary
declarations (matchers, equation lemmas, `proof_N`, `_unfold`, `induct`, …) are attributed to
their parent, and a used auxiliary constant (`NativeOp.refTy.eq_1`) counts as its parent. A
declaration that only unfolds a listed constant by `decide` or `rfl` names none and is not
counted. Replay from the worktree root under the shared lock:
`lake env lean docs/research/2026-10-04-seat-T3a/Census.lean`. -/

def targets : List Name :=
  [`Effect4.Program.NativeOp.refTy, `Effect4.Program.NativeOp.deferredTy,
   `Effect4.Program.NativeOp.refTarget, `Effect4.Program.NativeOp.deferredTarget,
   `Effect4.Program.NativeOp.deferredTypeArgs, `Effect4.Program.NativeOp.all,
   `Effect4.Program.fnNames,
   `Effect4.Program.NativeOp.row_closed, `Effect4.Program.nativeSignature_row_closed,
   `Effect4.Program.NativeOp.row_templateAdmissible, `Effect4.Program.NativeOp.row_wellScoped,
   `Effect4.Program.rowTy_closed, `Effect4.Program.rowTy_closed_some,
   `Effect4.Program.Typed.syncRow_typed, `Effect4.Program.Typed.fits_refTy_inv,
   `Effect4.Program.Typed.fits_deferredTy_inv, `Effect4.Program.Typed.refRead_nat,
   `Effect4.Program.Typed.HandleFits, `Effect4.Program.Typed.FlatFits,
   `Effect4.Program.internalHandleTargets, `Effect4.Program.externalHandleTarget,
   `Effect4.Program.nativeSpell, `Effect4.Program.Table.lawful, `Effect4.Program.rowChecks,
   `Effect4.Program.Val.hasTy_refTy_inv, `Effect4.Program.Val.hasTy_deferredTy_inv,
   `Effect4.Program.nativeServiceTypes, `Effect4.Program.NativeOp.deferredMake,
   `Effect4.Program.NativeOp.syncOpOf, `Effect4.Program.builtinLookup_none]

/-- Strip the auxiliary suffixes Lean appends to a declaration's own name, and the private
prefix. -/
partial def parentOf (n : Name) : Name :=
  let n := (privateToUserName? n).getD n
  match n with
  | .str p s =>
    if s.startsWith "match_" || s.startsWith "proof_" || s.startsWith "eq_" || s == "eq_def"
        || s == "_unfold" || s == "induct" || s == "induct_unfolding" || s == "_sunfold"
        || s.startsWith "_private" || s == "fun_cases" || s.startsWith "spec_" || s == "_cstage1"
        || s == "_cstage2" || s == "_redArg" || s == "_closed" || s.startsWith "_lambda"
        || s == "mutual_induct" || s == "brecOn" || s == "below" || s.startsWith "_auxLemma"
        || s == "inj" || s == "injEq" || s == "noConfusion" || s == "sizeOf_spec" then parentOf p
    else n
  | .num p _ => parentOf p
  | _ => n

def usedIn (ci : ConstantInfo) : NameSet := Id.run do
  let mut s : NameSet := {}
  for x in ci.type.getUsedConstants do s := s.insert (parentOf x)
  if let some v := ci.value? (allowOpaque := true) then
    for x in v.getUsedConstants do s := s.insert (parentOf x)
  return s

#eval show CoreM Unit from do
  let env ← getEnv
  -- target ↦ (module ↦ parents)
  let mut byTarget : Std.HashMap Name (Std.HashMap Name (Array Name)) := {}
  for (n, ci) in env.constants.toList do
    let p := parentOf n
    -- the parent's own module when the parent exists, the auxiliary's otherwise
    let some idx := (env.getModuleIdxFor? p).orElse (fun _ => env.getModuleIdxFor? n) | continue
    let mod := env.header.moduleNames[idx.toNat]!
    let root := mod.getRoot
    unless root == `Effect4 || root == `Test do continue
    let used := usedIn ci
    for t in targets do
      if used.contains t && p != t then
        let inner := byTarget.getD t {}
        byTarget := byTarget.insert t (inner.insert mod ((inner.getD mod #[]).push p))
  for t in targets do
    let inner := byTarget.getD t {}
    let mods := inner.toList.toArray.qsort (fun a b => a.1.toString < b.1.toString)
    let total := mods.foldl (fun acc (_, ds) => acc + ds.toList.eraseDups.length) 0
    IO.println s!"## {t}: {total} declarations in {mods.size} modules"
    for (m, ds) in mods do
      let ds := (ds.qsort (fun a b => a.toString < b.toString)).toList.eraseDups
      IO.println s!"  {m} ({ds.length}): {String.intercalate ", " (ds.map toString)}"
