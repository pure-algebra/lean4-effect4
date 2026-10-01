import Effect4.Laws.Program.Author
import Effect4.Laws.Program.Authoring.Loops
import Effect4.Laws.Program.Authoring.Rows
import Effect4.Laws.Program.Authoring.Sugar

/-! Seat PROGRAMS (2026-09-30): the obligations a hand-written form meets today. The two forms
of `ProbeProgram1.lean` (copied verbatim) are scope-safe for every argument, proved by the
tree's `authoring_scoped` tactic from the lemmas the lifts already carry. That is the one form
obligation that comes for free. DI-89 also asks of a form a typing lemma and one behaviour law;
the tree states a typing law for 8 of its 19 generated forms (`Laws/Codegen/Forms.lean`) and a
behaviour law for none, and these two have neither. Scratch, not in the tree. -/

set_option autoImplicit false

namespace Probe.FormLaws
open Effect4 Effect4.Program Effect4.Program.Authoring

def timeoutForm (body : Src NativeOp) (millis : TermSrc) (timedOut : TermSrc) : Src NativeOp :=
  eff do
    let entrant ← fork body
    let timer ← fork (andThen (Effect.sleep millis) (fail timedOut))
    let winner ← withFiber (Action.raceAll
      [andThen (await entrant) (succeed (nat 0)), andThen (await timer) (succeed (nat 1))])
    ifElse (app "eq" [winner, nat 0])
      (andThen (withFiber (Action.interrupt timer)) (join entrant))
      (andThen (withFiber (Action.interrupt entrant)) (join timer))

theorem timeoutForm_scoped {body : Src NativeOp} {millis timedOut : TermSrc}
    (h0 : body.Scoped) (h1 : millis.Scoped) (h2 : timedOut.Scoped) :
    (timeoutForm body millis timedOut).Scoped := by
  unfold timeoutForm; authoring_scoped

def retryForm (attempt : Src NativeOp) (retryable : TermSrc → TermSrc) (times base : Nat)
    (answerTy errorTy : Ty) : Src NativeOp :=
  let cursorTy : Ty := .prod .nat (.prod .nat (.prod (.option answerTy) (.option errorTy)))
  bindName "retry.last"
    (iterateWith (app "pair" [nat 0, app "pair" [nat base, app "pair" [app "none" [], app "none" []]]])
      { cursorTy := some cursorTy
        while_ := fun c =>
          app "and" [app "not" [app "isSome" [app "fst" [app "snd" [app "snd" [c]]]]],
            app "or" [app "eq" [app "fst" [c], nat 0],
              app "lt" [app "fst" [c], nat (times + 1)]]]
        body := fun c => eff do
          let _ ← ifElse (app "lt" [nat 0, app "fst" [c]])
            (Effect.sleep (app "fst" [app "snd" [c]])) (succeed unit)
          catchIf "retry.error" (retryable (var "retry.error"))
            (bindName "retry.answer" attempt fun a =>
              succeed (app "pair" [app "some" [a], app "none" []]))
            (succeed (app "pair" [app "none" [], app "some" [var "retry.error"]]))
        step := fun c last =>
          app "pair" [app "succ" [app "fst" [c]],
            app "pair" [app "mul" [app "fst" [app "snd" [c]], nat 2], last]]
        result := fun c => app "snd" [app "snd" [c]] })
    fun last =>
      selectOption "retry.ok" (app "fst" [last])
        (selectOption "retry.err" (app "snd" [last])
          (failCause (Cause.die (str "retry: no attempt ran")))
          (fail (var "retry.err")))
        (succeed (var "retry.ok"))

theorem retryForm_scoped {attempt : Src NativeOp} {retryable : TermSrc → TermSrc}
    (times base : Nat) (answerTy errorTy : Ty)
    (h0 : attempt.Scoped) (h1 : ∀ e : TermSrc, e.Scoped → (retryable e).Scoped) :
    (retryForm attempt retryable times base answerTy errorTy).Scoped := by
  unfold retryForm
  authoring_scoped
  -- the one goal the tactic leaves: the caller's predicate applied to the bound error
  exact h1 _ (var_scoped _)

/-- Red control: a source that emits a variable no binder holds is provably not scoped, so the
two lemmas above say something. -/
def leaky : Src NativeOp := fun _ _ => .ok (.succeed (.var 99))

theorem leaky_not_scoped : ¬ leaky.Scoped := fun h =>
  absurd (h.holds {} [] (.succeed (.var 99)) rfl) (by decide)

end Probe.FormLaws

#print axioms Probe.FormLaws.timeoutForm_scoped
#print axioms Probe.FormLaws.retryForm_scoped
#print axioms Probe.FormLaws.leaky_not_scoped
