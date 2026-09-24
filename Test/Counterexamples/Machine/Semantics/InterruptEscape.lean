import Effect4.Api
import Effect4.Laws.Program.RuntimeR
import Effect4.Laws.Program.Typed.World

/-!
E4-SCHED-CE-008, U-01: the signed interruption divergence from rc.112.
The error-removing catch checks at answer `nat`, error `never`. rc.112 lets
`Fail 42` escape when an interrupt arrives during the masked await and the
region subsequently fails. Both Lean walks now strip Fail reasons at the
preempted catch and retain the recorded interrupt, including `stack0`.

The quiet tapes and the original failure's two typing facts remain controls.
The poisoned tapes check the repaired outcome, including the nested program
whose incorrectly delivered string used to cause a bad-shape defect. These
are exact finite runs; the runtime agreement theorem is checked separately.
-/
set_option autoImplicit false
set_option maxRecDepth 10000
namespace Test.Counterexamples.InterruptEscape
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Sched
open Effect4.Program.Typed (ExitFits)
abbrev TWorld := Effect4.Program.Typed.World

def n (i : Nat) : Term := .lit (.nat i)
def yes : Term := .lit (.bool true)
def budget : Nat := 120
def evaluate : Api.Decision := .evaluate Api.root
def interruptRoot : Api.Decision :=
  .interruptFrom (some Api.root) ReasonAnnotations.empty Api.root
def replyRoot (answer : Completion Val Err Defect FiberId Ann) (token : Nat := 0) :
    Api.Decision := .answerAsync Api.root token answer
/-- Park on a fresh deferred: the masked region has to be suspended for a decision to land. -/
def waiting : NativeEff :=
  .bind (.perform .deferredMake (.lit .unit)) (.perform .deferredAwait (.var 0))

/-- `catchAll(uninterruptible(await >> fail 42), _ => succeed 0)`. -/
def escape : NativeEff :=
  .catchIf yes (.uninterruptible (.bind waiting (.fail (n 42)))) (.succeed (n 0))
/-- The region resumes with no interrupt recorded. -/
def quiet : List Api.Decision := [evaluate, replyRoot (.ofExit (.success .unit))]
/-- The interrupt is recorded while the root is masked, then the region resumes. -/
def poisoned : List Api.Decision :=
  [evaluate, interruptRoot, replyRoot (.ofExit (.success .unit))]

def machineOf : RReplay → RState
  | .finished m | .frontier _ m | .stuck _ m => m
def termExit (p : NativeEff) (tape : List Api.Decision) : Option ExitV :=
  ((machineOf (replayR p budget tape)).fiber? Api.root).bind RunFiber.exit
def frameExit (p : NativeEff) (tape : List Api.Decision) : Option ExitV :=
  (Api.replay p budget tape).exit

def escapedExit : ExitV := .failure (Cause.fail (.tag 42))
def sanitizedExit : ExitV := .failure
  ((Cause.interrupt (some Api.root)).annotate (stackAnnotationsOf Api.root) false)
def checkedTy : EffTy := ⟨.nat, .never, .empty⟩

#guard typeOf nativeSignature escape = some checkedTy
#guard frameExit escape quiet = some (.success (.nat 0))
#guard termExit escape quiet = some (.success (.nat 0))
/-- The formerly escaping typed failure is replaced by the recorded interrupt. -/
def escaped_no_longer : Bool :=
  frameExit escape poisoned == some sanitizedExit && termExit escape poisoned == some sanitizedExit
#guard escaped_no_longer

/-- The delivered exit does not fit the program's checked type at any world. -/
theorem escaped_exit_does_not_fit (w : TWorld) : ¬ ExitFits w checkedTy escapedExit :=
  fun h => Bool.noConfusion h

/-- The same failure fits the masked region's own type, so the catch was the only frame
that could have removed it. -/
theorem escaped_exit_fits_region (w : TWorld) :
    ExitFits w ⟨.never, .nat, .empty⟩ escapedExit := rfl

/-- Contagion: the escaped string failure passes the inner catch, the walk is re-masked by
`interruptible`'s restoration, and the outer catch typed at `nat` runs its handler on a
string. `add` on a string is the bad-shape defect. -/
def leakBody : NativeEff :=
  .catchIf yes
    (.bind
      (.interruptible
        (.catchIf yes (.uninterruptible (.bind waiting (.fail (.lit (.str "boom")))))
          (.succeed (n 0))))
      (.fail (n 7)))
    (.succeed (.app "add" (.cons (.var 0) (.cons (n 1) .nil))))
def leak : NativeEff := .uninterruptible leakBody

def isBadShape : Option ExitV → Bool
  | some (.failure ⟨[.die .badName _]⟩) => true
  | _ => false

#guard typeOf nativeSignature leak = some checkedTy
#guard frameExit leak quiet = some (.success (.nat 8))
#guard termExit leak quiet = some (.success (.nat 8))
#guard frameExit leak poisoned = some sanitizedExit
#guard termExit leak poisoned = some sanitizedExit
#guard !isBadShape (frameExit leak poisoned)
#guard !isBadShape (termExit leak poisoned)

#print axioms escaped_exit_does_not_fit
#print axioms escaped_exit_fits_region
end Test.Counterexamples.InterruptEscape
