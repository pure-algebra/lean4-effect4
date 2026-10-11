import EffectsTest.Coalgebra.CoalgebraContract

set_option autoImplicit false

namespace IndexedReview
open Effects EffectsTest.Coalgebra

-- Control: compliance admits a host that never answers; it cannot establish progress.
def silent : IComodel Async (List Code) where
  answer _ _ _ := none

theorem silent_meets : silent.Meets tens := by
  intro _ _ _ _ _ h
  cases h

#guard (silent.run twoJobs []).isNone

-- Control: reply typing does not relate the final world to private host state.
def forgetful : IComodel Async (List Code) where
  answer opened operation _ := match operation with
    | .async _ => some ((), [])
    | .await promise => some (job (opened.get promise) promise.val, [])

theorem forgetful_meets : forgetful.Meets tens := by
  intro opened operation state answer next h
  cases operation with
  | async code => exact trivial
  | await promise =>
    change some (job (opened.get promise) promise.val, []) = some (answer, next) at h
    cases h
    exact job_tens (opened.get promise) promise.val

#guard (jobs.run twoJobs []).map (fun r => (r.1, r.2.1, r.2.2)) =
  some ([.num, .flag], 10, [.num, .flag])
#guard (forgetful.run twoJobs []).map (fun r => (r.1, r.2.1, r.2.2)) =
  some ([.num, .flag], 10, [])

-- Reader: the theorem still gives precisely its postcondition on the latter run.
example : (10 : Nat) % 10 = 0 :=
  IProgram.Sat.sound forgetful forgetful_meets twoJobs twoJobs_tens [] [.num, .flag] 10 [] rfl

-- A well-formed await at an existing world may still have no matching runtime resource.
#guard (jobs.answer [.num] (.await ⟨0, by decide⟩) []).isNone

-- Reader: the reverse embedding law at a program with several operations.
example : IProgram.ofProgram (IProgram.toProgram (IProgram.ofProgram askTwice)) =
    IProgram.ofProgram askTwice :=
  IProgram.ofProgram_toProgram (IProgram.ofProgram askTwice)

-- Reader and control: the one-world embedding also preserves an unanswered call.
def declining : Comodel Ask Nat where
  answer _ _ := none
example : declining.toIndexed.run (IProgram.ofProgram askTwice) 5 =
    (declining.run askTwice 5).map (fun result => ⟨(), result.1, result.2⟩) :=
  IComodel.run_ofProgram declining askTwice 5
#guard (declining.toIndexed.run (IProgram.ofProgram askTwice) 5).isNone

#eval ((jobs.run twoJobs []).map (fun r => r.2.1),
  (forgetful.run twoJobs []).map (fun r => r.2.2.length), (silent.run twoJobs []).isNone)
end IndexedReview
