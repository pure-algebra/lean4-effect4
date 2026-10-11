import Test.Dogfood.Scenario.Routing

/-! The elaborated shape of `request`, and the kernel on a free id and id text. A finite probe. -/

open Effect4 Effect4.Machine Effect4.Program Test.Dogfood.Scenario Test.Dogfood.Scenario.Routing

set_option maxRecDepth 100000
set_option maxHeartbeats 0

syntax (name := kernelRfl) "kernel_rfl" : tactic

open Lean Elab Tactic Meta in
@[tactic kernelRfl] def evalKernelRfl : Tactic := fun _ => do
  let goal ← getMainGoal
  let ty ← instantiateMVars (← goal.getType)
  match ty.consumeMData.eq? with
  | some (_, lhs, _) =>
    goal.assign (← mkEqRefl lhs)
    replaceMainGoal []
  | none => throwError "kernel_rfl: the goal is not an equation"



/-- The elaborated program, read off the elaboration. -/
def progOf (token : String) (id : Nat) (idText : String) : Api.Program :=
  match Authoring.elaborateModule (request token id idText) with
  | .ok p => p
  | .error _ => .succeed (.lit .unit)

-- the elaboration with a free token, id and id text, by the kernel
set_option trace.profiler true in
theorem elaborate_free (token : String) (id : Nat) (idText : String) :
    Authoring.elaborateModule (request token id idText) = .ok (progOf token id idText) := by
  kernel_rfl

-- the fragment with free leaves, by the kernel
set_option trace.profiler true in
theorem straight_free (token : String) (id : Nat) (idText : String) :
    Denote.StraightRows (request token id idText).table (progOf token id idText) = true := by
  kernel_rfl

/-- A build's program is its elaboration. -/
theorem build_program {m : Authoring.Module NativeOp} {b : Api.Built}
    (h : Effect4.Api.Author.build m = .ok b) : Authoring.elaborateModule m = .ok b.program := by
  unfold Effect4.Api.Author.build at h
  split at h
  · cases h
  · next program hprog =>
    dsimp only at h
    split at h
    · cases h
    · unfold Effect4.Api.Author.Internal.finishBuild at h
      split at h
      · cases h
        exact hprog
      · split at h <;> cases h
      · cases h

-- the escape run at the tag `SqlError`, every id, id text and message, by the kernel
set_option trace.profiler true in
theorem escapes_sqlError (id : Nat) (idText message : String) (b : Api.Built)
    (hb : Effect4.Api.Author.build (request "secret" id idText) = .ok b) :
    (observe (Test.Dogfood.Scenario.play (opened b) (failing "SqlError" message))).outcome =
      some (.failure (Cause.fail (.tagged "SqlError" message))) := by
  have hprog : b.program = progOf "secret" id idText := by
    have h := build_program hb
    rw [elaborate_free] at h
    exact (Except.ok.inj h).symm
  have htable : b.table = (request "secret" id idText).table :=
    (Effect4.Program.Authoring.build_table hb).1
  obtain ⟨table, program, admitted, rowNames⟩ := b
  have hp : program = progOf "secret" id idText := hprog
  have ht : table = (request "secret" id idText).table := htable
  subst hp
  subst ht
  kernel_rfl
