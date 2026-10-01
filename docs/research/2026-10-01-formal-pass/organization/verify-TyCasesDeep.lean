import Effect4
import Effect4.Laws

/-!
Verifier of seat ORGANIZATION (2026-10-01), probe for ORG-21 (row 132's rule: no case analysis
on `Ty` outside `Laws/Program/Typed/Membership.lean`).

The seat's probe (`probes/TyCasesInTyped.lean`) counts a declaration when its type or body names
`Ty.rec`/`casesOn`/`recOn`/`brecOn`/`below`, or a matcher whose own body names one. On 4.33.1 a
`match` with a catch-all compiles through a shared sparse `casesOn` helper named after whichever
definition first needed it (`Ty.isFactor.match_1` uses `Ty.infer._sparseCasesOn_13`), which that
test does not follow. This probe follows every compiler-made helper (matchers, sparse `casesOn`,
splitters, `_unary`/`_mutual`, `match_`/`proof_` auxiliaries) transitively from each declaration of
a module under `Effect4.Laws.Program.Typed`, wherever the helper is defined, and reports the
declarations that reach a case analysis on `Ty` by that route, per module.

Red controls: `Effect4.Program.Typed.Fits` (Membership) must be a hit; `Effect4.Program.Ty.isFactor`
(outside the directory, a sparse match) must be a hit when checked directly.
-/

open Lean Elab Command

def tyCase (c : Name) : Bool :=
  c.getPrefix == `Effect4.Program.Ty &&
    ["rec", "casesOn", "recOn", "brecOn", "below"].any (fun s => s == c.getString!)

def helper (env : Environment) (c : Name) : Bool :=
  c.isInternalDetail || c.isInternal || Lean.Meta.isMatcherCore env c ||
    c.components.any (fun s =>
      let t := s.toString
      t == "_unary" || t == "_mutual" || t == "splitter" || "_sparseCasesOn".isPrefixOf t ||
        "match_".isPrefixOf t || "proof_".isPrefixOf t || "_proof_".isPrefixOf t)

def reachesTyCase (env : Environment) (start : Array Name) : Bool := Id.run do
  let mut seen : NameSet := {}
  let mut stack := start.toList
  let mut steps := 0
  let mut found := false
  while !stack.isEmpty && steps < 20000 && !found do
    steps := steps + 1
    match stack with
    | [] => break
    | c :: rest =>
      stack := rest
      if seen.contains c then continue
      seen := seen.insert c
      if tyCase c then found := true
      else if helper env c then
        match env.find? c with
        | some (.defnInfo d) => stack := d.value.getUsedConstants.toList ++ stack
        | _ => pure ()
  return found

def declUses (env : Environment) (ci : ConstantInfo) : Bool :=
  let body := (ci.value? (allowOpaque := true)).getD (mkConst `Unit)
  reachesTyCase env (ci.type.getUsedConstants ++ body.getUsedConstants)

#eval show CommandElabM Unit from do
  let env ← getEnv
  let mods := env.header.moduleNames
  let mut hits : Std.HashMap Name (Array Name) := {}
  for (n, ci) in env.constants.toList do
    let some i := env.getModuleIdxFor? n | continue
    let m := mods[i.toNat]!
    unless (`Effect4.Laws.Program.Typed).isPrefixOf m do continue
    if declUses env ci then hits := hits.insert m ((hits.getD m #[]).push n)
  let rows := hits.toArray.qsort (fun a b => a.1.toString < b.1.toString)
  let lines := rows.map fun (m, ns) =>
    let users := ns.filter (fun x => !x.isInternal && !(helper env x))
    s!"{m}: {ns.size} hits, {users.size} person-written — {(users.qsort (fun a b => a.toString < b.toString)).toList.take 12}"
  let red1 : Bool := (hits.getD `Effect4.Laws.Program.Typed.Membership #[]).contains `Effect4.Program.Typed.Fits
  let red2 : Bool := match env.find? `Effect4.Program.Ty.isFactor with
    | some ci => declUses env ci
    | none => false
  logInfo m!"red controls: Typed.Fits hit {red1}; Ty.isFactor hit {red2}\n{"\n".intercalate lines.toList}"
