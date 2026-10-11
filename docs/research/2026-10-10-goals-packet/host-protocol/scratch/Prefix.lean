import Test.Dogfood.Scenario.Routing
import Effect4.Laws.Api.SessionMeaning

/-! The escape run before its last row, with a free tag, message, id and id text. Does the kernel
compute its phases, its tape and the premises of `denoteRows_eq_session`? A finite probe of the
route of `escape_session`. The `#eval` printed six verdicts, funded, host-driven, at rest and two
decisions. The result of `pre_free` was not captured when the work stopped: unverified. -/

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

def progOf (token : String) (id : Nat) (idText : String) : Api.Program :=
  match Authoring.elaborateModule (request token id idText) with
  | .ok p => p
  | .error _ => .succeed (.lit .unit)

/-- The escape script without its last row: the start, the configuration answered, the
repository's failure received. -/
def pre (tag message : String) : List Move :=
  script [[.start], answer cfg (ok (configOf "secret" 20)), [.receive repo (failed tag message)]]

#eval match Effect4.Api.Author.build (request "secret" 2 "2") with
  | .ok b =>
    let s := Test.Dogfood.Scenario.play (opened b) (pre "SqlError" "down")
    s!"{repr s.phases} funded={Run.funded s} host={Run.hostDriven s} rest={Run.atRest s} \
      tape={(Run.tapeOf s).length}"
  | .error _ => "no build"

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

theorem elaborate_free (token : String) (id : Nat) (idText : String) :
    Authoring.elaborateModule (request token id idText) = .ok (progOf token id idText) := by
  kernel_rfl

theorem built_request {token : String} {id : Nat} {idText : String} {b : Api.Built}
    (hb : Effect4.Api.Author.build (request token id idText) = .ok b) :
    b.program = progOf token id idText ∧ b.table = (request token id idText).table := by
  refine ⟨?_, (Effect4.Program.Authoring.build_table hb).1⟩
  have h := build_program hb
  rw [elaborate_free] at h
  exact (Except.ok.inj h).symm

set_option trace.profiler true in
/-- The prefix with every value free: its verdicts, and the three premises of
`denoteRows_eq_session` that a prefix can carry. -/
theorem pre_free (id : Nat) (idText tag message : String) (b : Api.Built)
    (hb : Effect4.Api.Author.build (request "secret" id idText) = .ok b) :
    ((Test.Dogfood.Scenario.play (opened b) (pre tag message)).phases,
      Run.funded (Test.Dogfood.Scenario.play (opened b) (pre tag message)),
      Run.hostDriven (Test.Dogfood.Scenario.play (opened b) (pre tag message)),
      Run.atRest (Test.Dogfood.Scenario.play (opened b) (pre tag message)),
      Run.appliedExits (Test.Dogfood.Scenario.play (opened b) (pre tag message))) =
    ([.progressed, .bound, .preflight, .applied, .bound, .preflight], true, true, true,
      [.success (configOf "secret" 20)]) := by
  obtain ⟨hprog, htable⟩ := built_request hb
  obtain ⟨table, program, admitted, rowNames⟩ := b
  have hp : program = progOf "secret" id idText := hprog
  have ht : table = (request "secret" id idText).table := htable
  subst hp
  subst ht
  kernel_rfl
