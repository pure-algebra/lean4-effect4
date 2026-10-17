import ProofGraph.GoalTag

/-!
# Declared facts: a statement whose proof lives outside Lean

A **declared fact** is a planned goal whose proof is done elsewhere: in the Rocq development of
`docs/research/2026-10-16-itrees/`, say, of its transcription of the declaration's definitions.
It is the owner's declared exception to the proof gates (2026-10-16): Lean holds the statement,
and the citation names the theorem that proves it. In every respect the gates read, the
declaration is a goal: the axiom gate admits its `sorry` body and counts what rests on it. The
citation is the one difference. `declaredSource?` gives it, and `#plan_status` prints it beside
the goal.

This module is apart from `ProofGraph.GoalTag`, so that a law module that declares no fact does
not rebuild when it changes.
-/

namespace ProofGraph
open Lean Meta Elab Command

/-- The declared facts, with the citation of each one's proof. -/
initialize declaredExt : MapDeclarationExtension String ← mkMapDeclarationExtension

/-- The citation of a declared fact's proof, or `none` for a declaration that is not one. -/
def declaredSource? (env : Environment) (n : Name) : Option String := declaredExt.find? env n

/-- `declared G binders : P from "where"` declares the fact `G`: a planned goal (`proof_goal`)
whose proof is the theorem the citation names. A docstring and attributes before it are the
theorem's, as for a goal. -/
syntax (name := declaredDecl) (docComment)? (Lean.Parser.Term.attributes)? "declared " declId declSig
  " from " str : command

@[command_elab declaredDecl] def elabDeclared : CommandElab := fun stx => do
  let doc? : Option (TSyntax ``Parser.Command.docComment) :=
    if stx[0].isNone then none else some ⟨stx[0][0]⟩
  let attrs? : Option (TSyntax ``Parser.Term.attributes) :=
    if stx[1].isNone then none else some ⟨stx[1][0]⟩
  let id : TSyntax ``Parser.Command.declId := ⟨stx[3]⟩
  let sig : TSyntax ``Parser.Command.declSig := ⟨stx[4]⟩
  let source : TSyntax `str := ⟨stx[6]⟩
  elabCommand (← `(command| $[$doc?:docComment]? $[$attrs?:attributes]? proof_goal $id $sig))
  let name ← liftTermElabM <| realizeGlobalConstNoOverloadWithInfo id.raw[0]
  modifyEnv (declaredExt.insert · name source.getString)

end ProofGraph
