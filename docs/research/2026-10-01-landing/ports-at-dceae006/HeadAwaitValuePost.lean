-- Synthesis seat port to the merged head (0c534f06): FitsExit read through H2's ExitOk.
import Effect4.Laws.Program.Typed.Assembly

/-!
# Formal pass, seat PROOFS — red control: the await-by-value post is the join's, not the await's

Base `efd67af1`. Reading aid for `note.md` §3 G6. `Fiber.await` answers the fiber's exit as a
value: the checker types `awaitFiber t .awaitValue` at `pure (exitOf a e)`
(`Program/Checker.lean:196`), the reference delivers `success (reifyExitVal ex)`
(`exitValue`, `Laws/Program/InterpR.lean:368-370`), and the denotation's continuation passes the
answer on as the success value (`fun v => .pure (.success v)`, `Laws/Program/DenoteR.lean:655`).
The fiber protocol's post for that row says the answer fits the target's *answer* column
(`fiberPost`, `.await target .awaitValue`, `Typed/Residual.lean:153-155`), which is the join's
value. So:

* `delivered_fits_checked`: the delivered value fits the checker's type.
* `post_excludes_delivered`: at a world declaring the target at `pure nat`, the post refuses
  the delivered value.
* `await_code_refused`: the denotation's await code is not `TypedProg` at the checker's type, at a
  world where the target is declared at `pure nat` — so the denotation lemma M5 needs fails for
  every program that awaits a fiber by value before it exits (the typed corpus's
  `awaitFiber.value` and `forkValue` shapes, `Test/Program/TypedCorpus.lean:62,127`, reading).
-/

set_option autoImplicit false

namespace Research.Synthesis.HeadAwaitValuePost
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Sched Effect4.Program.Typed
abbrev W := Effect4.Program.Typed.World

def target : FiberId := ⟨1⟩
def checkedTy : EffTy := EffTy.pure (.exitOf .nat .never)

/-- A world whose fiber table declares the target at `pure nat`. -/
def w : W := (initialWorld checkedTy).addFiber target (EffTy.pure .nat)

theorem target_declared : w.Γ target = some (EffTy.pure .nat) := by
  change tableInsert (initialWorld checkedTy).Γ target (EffTy.pure .nat) target = some _
  unfold tableInsert
  rw [if_pos rfl]

/-- The await code exactly as `denoteR` builds it for a target that has not exited. -/
def awaitCode : RProgram := .vis (.inr (.await target .awaitValue)) fun v => .pure (.success v)

def delivered : Val := reifyExitVal (.success (.nat 5))

theorem exitValue_delivers (root : NativeEff) :
    (interpR root).exitValue (.success (.nat 5)) .awaitValue = .pure (.success delivered) := rfl

theorem delivered_fits_checked (w' : W) : Fits w' delivered (.exitOf .nat .never) := trivial

/-- At the world where the target is declared at `pure nat`, the post refuses the delivered
value. (The post is not refuted at every world: a target declared at an exit, `unknown`, or a
union holding one, admits it; the defect is that the post reads the wrong column.) -/
theorem post_excludes_delivered (cert : FiberCert (.await target .awaitValue)) :
    ¬ fiberPost w (.await target .awaitValue) cert delivered := by
  rintro ⟨ty, hty, h⟩
  rw [target_declared] at hty
  cases hty
  exact h

theorem await_code_refused (root : ProgramSource) : ¬ TypedProg root w checkedTy awaitCode := by
  intro h
  cases h with
  | fiber _ _ _ _ cert _ next =>
    have hnext := next w (leHost_refl w) (Val.nat 5) ⟨EffTy.pure .nat, target_declared, trivial⟩
    exact (TypedProg.pure_inv hnext).1

end Research.Synthesis.HeadAwaitValuePost

open Research.Synthesis.HeadAwaitValuePost in
#print axioms target_declared
open Research.Synthesis.HeadAwaitValuePost in
#print axioms exitValue_delivers
open Research.Synthesis.HeadAwaitValuePost in
#print axioms delivered_fits_checked
open Research.Synthesis.HeadAwaitValuePost in
#print axioms post_excludes_delivered
open Research.Synthesis.HeadAwaitValuePost in
#print axioms await_code_refused
