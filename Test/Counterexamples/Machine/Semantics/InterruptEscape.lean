import Effect4.Api
import Effect4.Laws.Program.RuntimeR
import Effect4.Laws.Program.Typed.Contracts

/-!
E4-SCHED-CE-008: a typed failure escapes an error-removing catch on the reference machine,
the term evaluator and the pinned rc.112 source, from a checker-typed source program and a
three-decision tape. `catchAll(uninterruptible(await >> fail 42), _ => succeed 0)` checks at
answer `nat`, error `never`. When an interrupt is recorded while the fiber is masked and the
masked region then fails, `popR` restores the mask, meets the catch under preemption
(`failing ∧ interruptible ∧ interruptedCause.isSome`, `EvaluateR.lean:84`) and skips it; the
walk ends with the original `Fail 42`. rc.112 `internal/core.ts:540-545` discards every
failure continuation under the same condition; the end-to-end host run is retained in
`docs/research/2026-09-21-foundations-fr08-evidence/`.

The second program shows the escaped payload reaching a catch typed at a different error
type once a `restoreMask false` re-masks the walk: a nat-typed handler receives a string and
its `add` is the machine's bad-shape defect. No defect is in the source.

These are exact runs, not claims about every tape: the typed-state theorem is stated for
runs without such an escape (the `SkipsClean` walk premise of the FR-08 ruling), and this
file is why that premise is necessary.
-/
set_option autoImplicit false
set_option maxRecDepth 10000
namespace Test.Counterexamples.InterruptEscape
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Sched
open Effect4.Program.Typed.Contracts
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
def checkedTy : EffTy := ⟨.nat, .never, .empty⟩

#guard typeOf nativeSignature escape = some checkedTy
#guard frameExit escape quiet = some (.success (.nat 0))
#guard termExit escape quiet = some (.success (.nat 0))
#guard frameExit escape poisoned = some escapedExit
#guard termExit escape poisoned = some escapedExit

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
#guard isBadShape (frameExit leak poisoned)
#guard isBadShape (termExit leak poisoned)

#print axioms escaped_exit_does_not_fit
#print axioms escaped_exit_fits_region
end Test.Counterexamples.InterruptEscape
