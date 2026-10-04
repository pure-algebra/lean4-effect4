import ProofGraph.Ledger
import ProofGraph.Search

/-!
# Obligation extraction: a proof sketch whose holes become ledger goals

`#extract_obligations G using tac` runs the script `tac` on the proposition `P` of the ledger
goal `G` and turns what it leaves open into the plan:

- each residual goal, closed over the hypotheses the script introduced, becomes a ledger goal
  `G.part1`, `G.part2`, … (`theorem G.partᵢ : Obligation pᵢ`);
- the script itself becomes the reduction `G.reduce : p₁ → … → pₙ → P`, whose proof is the
  script's term with each residual goal filled by its hypothesis. It is published through
  `addTheorem`, so the kernel and the semantic ceiling check it.

The plan (`ProofGraph.Plan`) then reads `G.reduce` as a checked edge from the parts to `G`:
`#plan_status G via G.reduce for G` reports `G` as reduced and the parts as next goals. A part is
proved by a theorem `G.partᵢ.checked`; once every part is, `G` is ready and
`#obligation_close G via G.reduce for G` proves it. This is the reference scout's
`#extract_obligations` (`docs/research/2026-10-04-reference-scout/compilation.md` §4.4): lean-mlir's
`extract_goals`, with the ledger in place of `sorry`.

The script runs twice, once to read the residual goals and once to build the reduction, the second
time in a context that does not hold the parts' hypotheses, so it cannot use them. A script whose
residual goals differ between the runs is refused. The parts get no `wanted` placeholder: the ledger
goal holds their place, and the placement facts of `AGENTS.md` are the author's to write, as for
any goal. Universe-polymorphic goals are refused. This reflection is tooling only; it never enters
stored program content.
-/
namespace ProofGraph
open Lean Meta Elab Term Command

/-- A residual goal's proposition, closed over the hypotheses in its context other than
`exclude`, with those hypotheses in order. -/
private def closeResidual (g : MVarId) (exclude : Array Expr) : MetaM (Expr × Array Expr) :=
  g.withContext do
    let decl ← g.getDecl
    let fvars := decl.lctx.foldl (init := #[]) fun acc d =>
      if d.isImplementationDetail || exclude.contains d.toExpr then acc else acc.push d.toExpr
    let p ← mkForallFVars fvars (← instantiateMVars decl.type)
    return (← instantiateMVars p, fvars)

/-- Run `tac` on a fresh goal `P` in the empty context; the root and the residual goals. -/
private def runScript (P : Expr) (tac : Syntax) : TermElabM (Expr × List MVarId) := do
  let root ← mkFreshExprMVarAt {} {} P
  let before := (← Core.getMessageLog).toList.length
  let rest ← Term.withoutErrToSorry <|
    Tactic.run root.mvarId! (Tactic.withoutRecover (Tactic.evalTactic tac))
  -- an error the script logged instead of throwing fails the extraction, never a part
  let logged := (← Core.getMessageLog).toList.drop before
  if logged.any (·.severity == .error) then
    throwError "extract: the script reported an error; extraction needs a script that elaborates"
  return (root, rest)

/-- Extract the parts and the reduction of the ledger goal `goal` (see the module docstring). -/
def extractObligations (goal : Name) (tac : Syntax) : TermElabM (Array Name × Name) := do
  let some g ← readGoal goal | throwError "extract: {goal} is not a ledger goal"
  unless g.levels.isEmpty do throwError "extract: {goal} is universe-polymorphic"
  let props ← withoutModifyingState do
    let (_, rest) ← runScript g.proposition tac
    rest.toArray.mapM fun m => do
      let (p, _) ← closeResidual m #[]
      if p.hasMVar || p.hasFVar then throwError "extract: a residual goal of {goal} is not closed"
      pure p
  if props.isEmpty then
    throwError "extract: the script closes {goal}; prove it with #obligation_proved"
  let decls := props.mapIdx fun i p => ((`h).appendIndexAfter (i + 1), fun _ => pure p)
  let (type, value) ← withLocalDeclsD decls fun hs => do
    let (root, rest) ← runScript g.proposition tac
    unless rest.length == hs.size do
      throwError "extract: the script leaves {rest.length} goals on its second run, {hs.size} on its first"
    for (m, h, p) in rest.zip (hs.toList.zip props.toList) do
      let (q, fvars) ← closeResidual m hs
      unless ← isDefEq q p do throwError "extract: the script's residual goals changed between runs"
      m.assign (mkAppN h fvars)
    let proof ← instantiateMVars root
    if proof.hasMVar then throwError "extract: the reduction of {goal} leaves a metavariable"
    return (← mkForallFVars hs g.proposition, ← mkLambdaFVars hs proof)
  let reduction := goal ++ `reduce
  discard <| addTheorem reduction [] type value
  let mut parts : Array Name := #[]
  for (p, i) in props.zipIdx do
    let name := goal ++ Name.mkSimple s!"part{i + 1}"
    let type := mkApp (mkConst ``Obligation) p
    let value := mkApp (mkConst ``Obligation.mk) p
    addDecl <| .thmDecl { name, levelParams := [], type, value }
    parts := parts.push name
  return (parts, reduction)

/-- `#extract_obligations G using tac`: declare the parts the script leaves open and the checked
reduction from them to `G`. -/
syntax (name := extractObligationsCmd) "#extract_obligations " ident " using " tacticSeq : command

@[command_elab extractObligationsCmd] def elabExtractObligations : CommandElab := fun stx => do
  let report ← liftTermElabM do
    let goal ← realizeGlobalConstNoOverloadWithInfo stx[1]
    let (parts, reduction) ← extractObligations goal stx[3]
    let mut out := s!"{goal}: {parts.size} part(s), reduced by {reduction}"
    for p in parts do
      let some part ← readGoal p | throwError "extract: {p} did not read back as a goal"
      out := out ++ s!"\n  {p} : {← ppExpr part.proposition}"
    return out
  logInfo report

end ProofGraph
