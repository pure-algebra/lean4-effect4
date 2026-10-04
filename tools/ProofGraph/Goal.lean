import ProofGraph.Axioms

/-!
# Planned goals

A planned goal is a named theorem whose body is `sorry`, declared by the `proof_goal` command
(decisions row 203). Downstream proofs use it as a theorem, and its statement is the plan's record of what is
owed. When it is proved, the author replaces `proof_goal G : P` by `theorem G : P := …` in place, and
nothing downstream changes.

The command is the one place a `sorry` enters the tree:

- the token stays out of source, and Lean's sorry warning (`warn.sorry`) is off only inside the
  command, so a `sorry` written anywhere else still fails the build (`-DwarningAsError=true`);
- the command checks that the body it added is exactly `sorry` under the theorem's binders, then
  tags the declaration (`goalExt`);
- the axiom gate (`Test/Audit/AxiomGate.lean`) walks every declaration with goals as leaves, so a
  declaration reaches `sorryAx` only as a goal's own body, and the gate counts what rests on goals.

A theorem's standing is read from its dependencies with goals as leaves (`standing`): open when it
is a goal, proved modulo the goals the walk stops at when it reaches one, and proved otherwise.
This reflection is tooling only; it never enters stored program content.
-/
namespace ProofGraph
open Lean Meta Elab Command

/-- The planned goals, tagged in the module that declares them. -/
initialize goalExt : TagDeclarationExtension ← mkTagDeclarationExtension `ProofGraph.goal

/-- Whether `n` is a planned goal. -/
def isGoal (env : Environment) (n : Name) : Bool := goalExt.isTagged env n

/-- A goal's body: `sorry` under the theorem's binders, and nothing else. -/
def bareSorry : Expr → Bool
  | .lam _ _ body _ => bareSorry body
  | .mdata _ body => bareSorry body
  | e => e.isNonSyntheticSorry

/-- Tag `name` as a goal after checking that it is a theorem whose body is `sorry`. -/
def tagGoal (name : Name) : CoreM Unit := do
  let some (.thmInfo t) := (← getEnv).find? name | throwError "goal: {name} is not a theorem"
  unless bareSorry t.value do throwError "goal: the body of {name} is not `sorry`"
  modifyEnv (goalExt.tag · name)

/-- `proof_goal G binders : P` declares the planned goal `G`: the theorem `G binders : P` whose body is
`sorry`. A docstring and attributes before it are the theorem's, so a goal carries its placement
as a theorem does (`@[semantics "concept" (requirement := R4)] proof_goal G : P`, decisions row
207), and proving it changes `proof_goal` to `theorem` with nothing else moved. -/
syntax (name := goalDecl) (docComment)? (Lean.Parser.Term.attributes)? "proof_goal " declId declSig : command

@[command_elab goalDecl] def elabGoal : CommandElab := fun stx => do
  let doc? : Option (TSyntax ``Parser.Command.docComment) :=
    if stx[0].isNone then none else some ⟨stx[0][0]⟩
  let attrs? : Option (TSyntax ``Parser.Term.attributes) :=
    if stx[1].isNone then none else some ⟨stx[1][0]⟩
  let id : TSyntax ``Parser.Command.declId := ⟨stx[3]⟩
  let sig : TSyntax ``Parser.Command.declSig := ⟨stx[4]⟩
  let decl ← `(command| $[$doc?:docComment]? $[$attrs?:attributes]? theorem $id $sig := sorry)
  -- the body is `sorry`, so the binders are unused by construction: both warnings are off here only
  withScope (fun scope => { scope with
      opts := (warn.sorry.set scope.opts false).setBool `linter.unusedVariables false }) do
    elabCommand decl
  let name ← liftTermElabM <| realizeGlobalConstNoOverloadWithInfo id.raw[0]
  liftCoreM <| tagGoal name

/-- The standing of a theorem, read from its dependencies with goals as leaves. -/
inductive Standing
  /-- the theorem is a goal -/
  | goal
  /-- the theorem reaches these goals and no other `sorry` -/
  | modulo (goals : Array Name)
  /-- the theorem reaches no goal -/
  | proved
  deriving Inhabited, BEq

def Standing.word : Standing → String
  | .goal => "goal"
  | .modulo _ => "modulo"
  | .proved => "proved"

/-- The axioms and the goals `name` reaches, goals as leaves, with the memo threaded through;
`none` only if the step budget ran out. -/
def reachedWithGoals (env : Environment) (name : Name) :
    StateM AxiomMemo (Option (Array Name × Array Name)) := do
  let some all ← reachedAxioms env name (isGoal env) | return none
  return some (all.filter (!isGoal env ·), all.filter (isGoal env ·))

/-- The standing of `name` and the axioms it reaches. -/
def standing (env : Environment) (name : Name) :
    StateM AxiomMemo (Option (Standing × Array Name)) := do
  let some (axioms, goals) ← reachedWithGoals env name | return none
  if isGoal env name then return some (.goal, axioms)
  if goals.isEmpty then return some (.proved, axioms)
  return some (.modulo (goals.qsort (·.toString < ·.toString)), axioms)

end ProofGraph
