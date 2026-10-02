import Effect4.Laws.Program.Typed.AnswerSchema

/-!
# Test.Program.AnswerSchema — decoded host answers at their token

Placement: semantics Concept 5 (exact codecs) with Concept 1's membership, consumed by the host-answer
edit (`edit_answer`, `M6Edits.answer`) through `answerOk_of_decode` (`Typed/AnswerSchema.lean`).

* A string-error failure and a unit success, encoded by the Schema codec and decoded back, are
  admitted at a declared token.
* An exit with an internal defect (`badName`) is still represented: the codec encodes and decodes
  it. The typing refuses it (`NoShapeDefect`, decisions row 152): representation is total, typing is
  the decidable check on top.
* The classifier: an exit type is not shape-decided; its columns can be.

Reach: concrete exits at one exit type; the strings avoid binary64 numbers, which the kernel does not
evaluate. No session correlation, no host decoder agreement.
-/

set_option autoImplicit false

namespace Test.Program.AnswerSchema
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Sched Effect4.Program.Denote
open Effect4.Program.Typed

abbrev W := Effect4.Program.Typed.World

def ty : EffTy := ⟨.unit, .string, Env.Requirement.empty⟩
def exitTy : Ty := .exitOf ty.answer ty.error

def okExit : ExitV := .success Val.unit
def failExit : ExitV := .failure (Cause.fail (errOf (Val.str "boom")))
def badExit : ExitV := .failure (Cause.die Defect.badName)

theorem columns_decided : shapeDecides ty.answer = true ∧ shapeDecides ty.error = true := ⟨rfl, rfl⟩

theorem exit_not_decided : shapeDecides exitTy = false := rfl

theorem ok_encodes : ∃ j, Schema.encode exitTy (reifyExitVal okExit) = some j := ⟨_, rfl⟩
theorem fail_encodes : ∃ j, Schema.encode exitTy (reifyExitVal failExit) = some j := ⟨_, rfl⟩
theorem bad_encodes : ∃ j, Schema.encode exitTy (reifyExitVal badExit) = some j := ⟨_, rfl⟩

theorem fail_shapeFree : NoShapeDefect ty failExit := by
  intro r hr
  simp only [Cause.fail, List.mem_singleton] at hr
  subst hr
  trivial

/-- **A decoded failure is admitted at its token.** -/
theorem fail_admitted (w : W) (m : RState) (target : FiberId) (token : Nat)
    (declared : w.Θ target token = some ty) :
    AnswerOk w m (.answerAsync target token (.ofExit failExit)) := by
  obtain ⟨j, hj⟩ := fail_encodes
  exact answerOk_of_decode declared rfl rfl (Schema.decode_of_encode hj) fail_shapeFree

/-- **A decoded success is admitted at its token.** -/
theorem ok_admitted (w : W) (m : RState) (target : FiberId) (token : Nat)
    (declared : w.Θ target token = some ty) :
    AnswerOk w m (.answerAsync target token (.ofExit okExit)) := by
  obtain ⟨j, hj⟩ := ok_encodes
  exact answerOk_of_decode declared rfl rfl (Schema.decode_of_encode hj) trivial

/-- **The internal defect is represented**: it decodes from its own encoding. -/
theorem bad_decodes : ∃ j, Schema.decode exitTy j = some (reifyExitVal badExit) := by
  obtain ⟨j, hj⟩ := bad_encodes
  exact ⟨j, Schema.decode_of_encode hj⟩

/-- **…and the typing refuses it**, at every world. -/
theorem bad_refused (w : W) : ¬ ExitOk w ty badExit := fun h =>
  (h.2 _ (List.mem_singleton_self _)).1 rfl

end Test.Program.AnswerSchema
