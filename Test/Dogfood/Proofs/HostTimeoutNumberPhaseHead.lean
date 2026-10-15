import Test.Dogfood.Proofs.HostTimeoutNumberPhaseFlow
import Test.Dogfood.Proofs.HostTimeoutNumberCounted

/-!
Concept: scope-lifetime-finalization R11 and translation-simulation R10.
Question: actual native heads expose the numeric class required by their returned frame.
Consumer: pending request parking and numeric cleanup dispatch for both Timeout endpoints.
Reach: the existing phase classes and actual source callback equations.
Limit: initialized history and race assignments remain separate obligations.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace Test.Dogfood.Proofs.HostTimeoutNumberPhaseHead
open Effect4 Effect4.Machine Effect4.Program
open HostTimeoutNumberPhaseFlow HostTimeoutNumberCallbacks

/-- An actual asynchronous phase head belongs to the unchanged pre-cleanup heap class. -/
theorem async_class (state : Stores) (kind : Kind) (name : EffName) (signal : Bool)
    (cancel : Option EffName) (owned : CodeAt state kind (.async name signal cancel)) :
    ∃ phase, kind = .before phase ∧ At phase state := by
  cases owned
  all_goals aesop (rule_sets := [Effect4.CodeClosure]) (add norm simp [completed_code, cleanup_code,
    write_code, cleanup_write_code, HostTimeoutNumberEntry.attempt_code,
    HostTimeoutNumberCounted.attempt_body_code])

end Test.Dogfood.Proofs.HostTimeoutNumberPhaseHead
