import Effect4.Laws.Program.Typed.Assembly

/-!
# Formal pass, seat PROOFS — red control: the close-scope post is the argument, not the answer

Base `efd67af1`. Reading aid for `note.md` §3 G6. `Scope.close(scope, exit)` answers `void`:
the checker types `withFiber (closeScope s e)` at `pure unit` (`Program/Checker.lean:377-381`),
and the reference runs the scope's close program, which is `pure (success unit)` when the scope
holds no finalizer (`closeScopeR`, `Laws/Program/InterpR.lean:166-169`). The denotation passes
the delivered exit on as the program's own (`Effects.Program.pure`,
`Laws/Program/DenoteR.lean:197`). The fiber protocol's post says the answer *is* the exit passed
to close (`fiberPost`, `.closeScope _ ex => ans = ex`, `Typed/Residual.lean:160`).

* `close_no_finalizer`: on a store whose scope 0 holds no finalizer, the close program is
  `pure (success unit)` — not the argument exit.
* `post_excludes_answer`: the post refuses that answer whenever the argument is a failure.
* `close_code_refused`: the denotation's close code with a typed-failure argument is not
  `TypedProg` at the checker's `pure unit`, at any world.
-/

set_option autoImplicit false

namespace FormalPass.Proofs.CloseScopePost
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Sched Effect4.Program.Typed
abbrev W := Effect4.Program.Typed.World

def failed : ExitV := .failure (Cause.fail (.tag 1))
def closeCode : RProgram := .vis (.inr (.closeScope 0 failed)) Effects.Program.pure

/-- A store holding one open sequential scope at key 0 and no finalizer. -/
def oneScope : Stores :=
  ((syncOpStep (.scopeMake .sequential) Stores.empty).map (·.1)).getD Stores.empty

def isPureUnit : Option (Stores × RProgram) → Bool
  | some (_, .pure (.success .unit)) => true
  | _ => false

theorem close_no_finalizer : isPureUnit (closeScopeR 0 failed true oneScope) = true := by
  decide +kernel

theorem post_excludes_answer (w' : W) (cert : FiberCert (.closeScope 0 failed)) :
    ¬ fiberPost w' (.closeScope 0 failed) cert (.success .unit) := by
  intro h
  cases h

theorem close_code_refused (root : ProgramSource) (w : W) :
    ¬ TypedProg root w (EffTy.pure .unit) closeCode := by
  intro h
  cases h with
  | fiber _ _ _ _ cert _ next =>
    have hnext := next w (leHost_refl w) failed rfl
    have fits := TypedProg.pure_inv hnext
    have clean := cleanExit_of_never_fits w (EffTy.pure .unit) (Cause.fail (.tag 1)) rfl fits
    exact Bool.noConfusion clean

end FormalPass.Proofs.CloseScopePost

open FormalPass.Proofs.CloseScopePost in
#print axioms close_no_finalizer
open FormalPass.Proofs.CloseScopePost in
#print axioms post_excludes_answer
open FormalPass.Proofs.CloseScopePost in
#print axioms close_code_refused
