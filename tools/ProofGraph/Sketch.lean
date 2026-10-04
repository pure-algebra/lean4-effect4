import ProofGraph.Goal

/-!
# Sketches: a proof whose holes become planned goals

`proof_sketch G binders : P := by tac` runs the script `tac` on `P`, under the binders, and turns what it
leaves open into the plan:

- each residual goal, closed over the hypotheses in its context, becomes a planned goal
  `G.part1`, `G.part2`, … (a theorem whose body is `sorry`, tagged as `goal` tags it);
- `G` itself becomes a theorem whose proof is the script's term, with each residual goal filled by
  its part. It is added through the kernel like any theorem, and its standing is proved modulo the
  parts.

The info message prints each part as a `proof_goal` line, ready to paste. To work on a part, paste
it above the sketch as an authored `proof_goal`, and close the script's hole with it. Proving the goal in
place then proves `G`. This is the reference scout's `#extract_obligations`
(`docs/research/2026-10-04-reference-scout/compilation.md` §4.4, lean-mlir's `extract_goals`),
with planned goals as decisions row 203 defines them. A script that closes `P` is refused: write
the theorem. A script that logs an error, or leaves a residual goal that is not closed, is refused.
Universe-polymorphic statements are refused. This reflection is tooling only; it never enters
stored program content.
-/
namespace ProofGraph
open Lean Meta Elab Term Command

/-- A residual goal's proposition, closed over the hypotheses in its context, with those
hypotheses in order. -/
private def closeResidual (g : MVarId) : MetaM (Expr × Array Expr) :=
  g.withContext do
    let decl ← g.getDecl
    let fvars := decl.lctx.foldl (init := #[]) fun acc d =>
      if d.isImplementationDetail then acc else acc.push d.toExpr
    let p ← mkForallFVars fvars (← instantiateMVars decl.type)
    return (← instantiateMVars p, fvars)

/-- Declare the sketch `name : ∀ xs, P` proved by `tac`, and its parts. Returns the parts. -/
def addSketch (name : Name) (xs : Array Expr) (P : Expr) (tac : Syntax) : TermElabM (Array Name) := do
  let type ← instantiateMVars (← mkForallFVars xs P)
  if type.hasMVar || type.hasLevelParam then
    throwError "sketch: the statement of {name} is not closed, or is universe-polymorphic"
  let root ← mkFreshExprSyntheticOpaqueMVar P
  let saved ← Core.getMessageLog
  let rest ← Term.withoutErrToSorry <|
    Tactic.run root.mvarId! (Tactic.withoutRecover (Tactic.evalTactic tac))
  -- an error the script logged instead of throwing fails the sketch, never a part; the sketch's
  -- one refusal carries the script's first error
  let logged := ((← Core.getMessageLog).toList.drop saved.toList.length).filter (·.severity == .error)
  if let some first := logged.head? then
    Core.setMessageLog saved
    throwError "sketch: the script reported an error: {← first.data.toString}"
  if rest.isEmpty then throwError "sketch: the script closes {name}; write it as a theorem"
  let mut parts : Array Name := #[]
  for (m, i) in rest.toArray.zipIdx do
    let (p, fvars) ← closeResidual m
    if p.hasMVar || p.hasFVar then throwError "sketch: a residual goal of {name} is not closed"
    let part := name ++ Name.mkSimple s!"part{i + 1}"
    withOptions (warn.sorry.set · false) do
      addDecl <| .thmDecl { name := part, levelParams := [], type := p, value := ← mkSorry p false }
    tagGoal part
    m.assign (mkAppN (mkConst part) fvars)
    parts := parts.push part
  let value ← instantiateMVars (← mkLambdaFVars xs root)
  if value.hasMVar then throwError "sketch: the proof of {name} leaves a metavariable"
  addDecl <| .thmDecl { name, levelParams := [], type, value }
  return parts

/-- `proof_sketch G binders : P := by tac`: declare `G`, proved by the script modulo the parts it leaves
open, which become planned goals `G.partᵢ`. -/
syntax (name := sketchCmd) "proof_sketch " ident (ppSpace bracketedBinder)* " : " term " := " "by "
  tacticSeq : command

@[command_elab sketchCmd] def elabSketch : CommandElab := fun stx => do
  let name := (← getCurrNamespace) ++ stx[1].getId
  let report ← liftTermElabM do
    Term.elabBinders stx[2].getArgs fun xs => do
      let P ← Term.elabType stx[4]
      Term.synthesizeSyntheticMVarsNoPostponing
      let parts ← addSketch name xs (← instantiateMVars P) stx[7]
      let mut out := s!"{name}: proved modulo {parts.size} part(s)"
      for p in parts do
        let some (.thmInfo t) := (← getEnv).find? p | throwError "sketch: {p} was not added"
        -- the part's name as the sketch's namespace reads it, ready to paste beside the sketch
        out := out ++ s!"\nproof_goal {stx[1].getId ++ p.componentsRev.head!} : {← ppExpr t.type}"
      return out
  logInfo report

end ProofGraph
