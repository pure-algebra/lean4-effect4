-- The proof-style ratchet's red control (Test/Audit/ProofStyle.lean). Not a battery module:
-- `Test/fixtures/` is outside the module-closure gate. The words simp_all, first and try in this
-- comment are not counted; nor is the `try … catch` of `do` notation below.
theorem banned (n : Nat) : n + 0 = n := by
  try simp_all
  first | rfl | simp

theorem plain (n : Nat) : n + 0 = n := by
  simp only [Nat.add_zero]

def caught : IO Unit := do
  try pure () catch _ => pure ()

-- A tactic local to this file: the scan's parser tables do not hold it, so the command that uses
-- it is unread, and a banned use inside it would go uncounted.
local macro "fixture_rfl" : tactic => `(tactic| rfl)

theorem localSyntax (n : Nat) : n = n := by
  fixture_rfl
