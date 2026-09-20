import Effect4.Laws.Auto.Obligations
open ProofGraph

namespace Test.Obligations.Positive
def closed : Obligation (∀ n : Nat, n = n) := ⟨⟩
def pending : Obligation (∀ n : Nat, n = n + 1) := ⟨⟩
#proof_wanted pending
end Test.Obligations.Positive

/-- info: Test.Obligations.Positive: 1 open, 1 proved, 2 total; ceiling 1 -/
#guard_msgs in
#typed_state_obligations Test.Obligations.Positive ceiling 1 using aesop

/-- error: proof graph: 1 open obligations exceed ceiling 0 -/
#guard_msgs in
#typed_state_obligations Test.Obligations.Positive ceiling 0 using aesop

namespace Test.Obligations.Missing
def pending : Obligation (∀ n : Nat, n = n + 1) := ⟨⟩
end Test.Obligations.Missing
/-- error: obligation ledger: missing proof or placeholder for [Test.Obligations.Missing.pending] -/
#guard_msgs in
#typed_state_obligations Test.Obligations.Missing ceiling 1 using aesop

namespace Test.Obligations.Stale
def extra : ProofWanted True := ⟨⟩
def closed : Obligation True := ⟨⟩
end Test.Obligations.Stale
/-- error: obligation ledger: stale placeholder Test.Obligations.Stale.extra -/
#guard_msgs in
#typed_state_obligations Test.Obligations.Stale ceiling 1 using aesop

namespace Test.Obligations.Solved
def closed : Obligation (∀ n : Nat, n = n) := ⟨⟩
#proof_wanted closed
end Test.Obligations.Solved
/-- error: obligation ledger: proved goals still have a placeholder: [Test.Obligations.Solved.closed] -/
#guard_msgs in
#typed_state_obligations Test.Obligations.Solved ceiling 1 using aesop

namespace Test.Obligations.Parameterized
def closed : Obligation True := ⟨⟩
def leftover (n : Nat) : ProofWanted (n = n) := ⟨⟩
end Test.Obligations.Parameterized
/-- error: obligation ledger: stale placeholder Test.Obligations.Parameterized.leftover -/
#guard_msgs in
#typed_state_obligations Test.Obligations.Parameterized ceiling 0 using aesop

#print axioms Test.Obligations.Positive.closed.checked
