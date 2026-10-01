import Effect4.Laws.Program.Typed.Assembly

/-!
# Verifier red controls — this file must NOT compile

Both claims are false. Observed (verify-logs/verify-rerun-red-oom.log): exit 137 after 126 s at
3.5 GB resident under `-M6144`: on a false claim `decide +kernel`'s failure path reduces the replay
in the elaborator, the memory blow-up seat PROOFS recorded for elaborator `decide` (bisect T2).
The negations are proved positively instead (`VerifySplit.budget7_is_fuel_frontier`,
`budget7_not_finished`). Kept as a fixture of that cost; do not add it to a battery.
-/
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Sched Effect4.Program.Typed

namespace FormalPass.Proofs.Verify.Red
def n (i : Nat) : Term := .lit (.nat i)
def yes : Term := .lit (.bool true)
def sleepy : NativeEff := .perform .sleep (.lit (.nat 1))
def prog : NativeEff :=
  .catchIf yes (.uninterruptible (.bind sleepy (.bind (.succeed (n 0)) (.fail (n 42)))))
    (.succeed (n 0))
def interruptRoot : Api.Decision :=
  .interruptFrom (some Api.root) ReasonAnnotations.empty Api.root
def tape : List Api.Decision :=
  [Api.evaluate, Api.flush, interruptRoot, .advance (ClockMillis.ofNat 1), Api.flush]
abbrev RR := ReplayResult EffName EffThunk Val Err Defect FiberId Ann Ctx Stores RProgram RSaved Unit
def isFinished : RR → Bool | .finished _ => true | _ => false

/-- False: budget 7 is a fuel frontier. -/
theorem wrong_finished7 : isFinished (replayR prog 7 tape) = true := by decide +kernel

/-- False: the window fiber is running. -/
theorem wrong_not_running6 : ∀ f ∈ (replayR prog 6 tape).machine.fibers, f.running = false := by
  decide +kernel
end FormalPass.Proofs.Verify.Red
