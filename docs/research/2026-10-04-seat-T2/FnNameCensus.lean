import Effect4
import Effect4.Laws
import Test.All
open Lean

/-! Scratch measurement for seat T2's design note (not committed).
Which declarations of this package mention the eight read-modify-write `SyncOp` rows, or the four
`FnName` interpretations those rows run? Auxiliary declarations (matchers, equation lemmas,
`proof_N`, `_unfold`, `induct`, `match_N`, `eq_N`) are attributed to their parent declaration. -/

def rows : List Name :=
  [`Effect4.Machine.SyncOp.refUpdate, `Effect4.Machine.SyncOp.refGetAndUpdate,
   `Effect4.Machine.SyncOp.refUpdateAndGet, `Effect4.Machine.SyncOp.refUpdateSome,
   `Effect4.Machine.SyncOp.refGetAndUpdateSome, `Effect4.Machine.SyncOp.refUpdateSomeAndGet,
   `Effect4.Machine.SyncOp.refModify, `Effect4.Machine.SyncOp.refModifySome]

def interps : List Name :=
  [`Effect4.Machine.FnName.total, `Effect4.Machine.FnName.partialUpdate,
   `Effect4.Machine.FnName.modify, `Effect4.Machine.FnName.modifySome]

/-- Strip the auxiliary suffixes Lean appends to a declaration's own name. -/
partial def parentOf (n : Name) : Name :=
  match n with
  | .str p s =>
    if s.startsWith "match_" || s.startsWith "proof_" || s.startsWith "eq_" || s == "eq_def"
        || s == "_unfold" || s == "induct" || s == "induct_unfolding" || s == "_sunfold"
        || s.startsWith "_private" || s == "fun_cases" || s.startsWith "spec_" || s == "_cstage1"
        || s == "_cstage2" || s == "_redArg" || s == "_closed" || s.startsWith "_lambda"
        || s == "mutual_induct" || s == "eq_1" || s == "brecOn" || s == "below" then parentOf p
    else n
  | .num p _ => parentOf p
  | _ => n

def usedIn (ci : ConstantInfo) : NameSet := Id.run do
  let mut s : NameSet := {}
  for x in ci.type.getUsedConstants do s := s.insert x
  if let some v := ci.value? (allowOpaque := true) then
    for x in v.getUsedConstants do s := s.insert x
  return s

#eval show CoreM Unit from do
  let env ← getEnv
  let mut byRow : Std.HashMap Name (Array Name) := {}
  let mut byInterp : Std.HashMap Name (Array Name) := {}
  let mut modules : Std.HashMap Name Unit := {}
  let mut decls : Std.HashMap Name Name := {}
  for (n, ci) in env.constants.toList do
    let some idx := env.getModuleIdxFor? n | continue
    let mod := env.header.moduleNames[idx.toNat]!
    let root := mod.getRoot
    unless root == `Effect4 || root == `Test do continue
    if n.isInternal && !(n.toString.contains "match_") then
      -- keep internal names only through their parent below
      pure ()
    let used := usedIn ci
    let p := parentOf n
    for r in rows do
      if used.contains r then
        byRow := byRow.insert r ((byRow.getD r #[]).push p)
        decls := decls.insert p mod
    for f in interps do
      if used.contains f then
        byInterp := byInterp.insert f ((byInterp.getD f #[]).push p)
        decls := decls.insert p mod
  -- dedupe and print
  let mut perModule : Std.HashMap Name (Array Name) := {}
  for (d, m) in decls.toList do
    perModule := perModule.insert m ((perModule.getD m #[]).push d)
  let mods := perModule.toList.toArray.qsort (fun a b => a.1.toString < b.1.toString)
  IO.println s!"declarations (parents): {decls.size}; modules: {mods.size}"
  for (m, ds) in mods do
    let ds := (ds.qsort (fun a b => a.toString < b.toString)).toList.eraseDups
    IO.println s!"{m}\t{ds.length}"
    for d in ds do
      IO.println s!"    {d}"
