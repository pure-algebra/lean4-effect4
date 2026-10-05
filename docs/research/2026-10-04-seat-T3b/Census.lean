import Effect4
import Effect4.Laws
import Test.All
open Lean

/-! Measurement for seat T3b's design note (phase 1), after seat T3a's `Census.lean`. Which
declarations of the `Effect4` and `Test` roots name each listed constant directly, in their type
or their value? Auxiliary declarations (matchers, equation lemmas, `proof_N`, `_unfold`, `induct`,
…) are attributed to their parent, and a used auxiliary constant counts as its parent. A
declaration that only unfolds a listed constant by `decide` or `rfl` names none and is not
counted. Replay from the worktree root under the shared lock, at `5949fe4b`:
`lake env lean -M8192 docs/research/2026-10-04-seat-T3b/Census.lean`. -/

def targets : List Name :=
  [ -- the function-name alphabet and its interpretations
    `Effect4.Machine.FnName, `Effect4.Machine.FnName.incr, `Effect4.Machine.FnName.double,
    `Effect4.Machine.FnName.zeroWhenPositive, `Effect4.Machine.FnName.noChange,
    `Effect4.Machine.FnName.takeAndBump,
    `Effect4.Machine.FnName.total, `Effect4.Machine.FnName.partialUpdate,
    `Effect4.Machine.FnName.modify, `Effect4.Machine.FnName.modifySome,
    -- T2's lowerings and agreements
    `Effect4.Machine.FnName.updateTerm, `Effect4.Machine.FnName.updateSomeTerm,
    `Effect4.Machine.FnName.modifyTerm, `Effect4.Machine.FnName.modifySomeTerm,
    `Effect4.Machine.FnName.updateTerm_agrees, `Effect4.Machine.FnName.updateSomeTerm_agrees,
    `Effect4.Machine.FnName.modifyTerm_agrees, `Effect4.Machine.FnName.modifySomeTerm_agrees,
    -- the faces' vocabulary
    `Effect4.Program.NativeOp.fnSpelling, `Effect4.Program.fnNames,
    `Effect4.Codegen.Forms.lambdaShape, `Effect4.Codegen.Forms.lambdaAtom,
    `Effect4.Codegen.Styles.atom?,
    -- T2's connector and discharges, and the deletions T2 left to T3
    `Effect4.Program.NativeOp.fnKernel, `Effect4.Program.kernel_term_agrees,
    `Effect4.Program.Typed.updateTerm_maps, `Effect4.Program.Typed.updateSomeTerm_maps,
    `Effect4.Program.Typed.modifyTerm_maps, `Effect4.Program.Typed.modifySomeTerm_maps,
    `Effect4.Program.Typed.modify_nat, `Effect4.Program.Typed.modifySome_nat,
    `Effect4.Program.Typed.fits_total, `Effect4.Program.Typed.fits_partialUpdate,
    `Effect4.Program.Typed.nat_of_equiv, `Effect4.Program.Typed.fits_toOption,
    `Effect4.Program.Typed.poke_world, `Effect4.Program.Typed.Evaluating.store_restated,
    -- the eight read-modify-write constructors
    `Effect4.Program.NativeOp.refUpdate, `Effect4.Program.NativeOp.refGetAndUpdate,
    `Effect4.Program.NativeOp.refUpdateAndGet, `Effect4.Program.NativeOp.refUpdateSome,
    `Effect4.Program.NativeOp.refGetAndUpdateSome, `Effect4.Program.NativeOp.refUpdateSomeAndGet,
    `Effect4.Program.NativeOp.refModify, `Effect4.Program.NativeOp.refModifySome,
    -- what the rows' change reaches
    `Effect4.Program.NativeOp.syncOpOf, `Effect4.Program.NativeOp.row,
    `Effect4.Program.NativeOp.spelled, `Effect4.Program.NativeOp.scopedAt_eq_true,
    `Effect4.Program.Typed.syncRow_typed, `Effect4.Program.checkRow, `Effect4.Program.rowTy,
    `Effect4.Program.Eff.weaken, `Effect4.Program.weakenAlg, `Effect4.Program.frontierMap,
    `Effect4.Program.Formation.programAnnotations]

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
  let mut byTarget : Std.HashMap Name (Std.HashMap Name (Array Name)) := {}
  for (n, ci) in env.constants.toList do
    let p := parentOf n
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
