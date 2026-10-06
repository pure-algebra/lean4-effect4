-- The proof-style scan's control for the word `under` (Test/Audit/ProofStyle.lean). Not a battery
-- module: `Test/fixtures/` is outside the module-closure gate. Three commands of the law graph
-- write a clause `under Some.Prefix`, and the word is a keyword in that place only. So the scan
-- reads a theorem with a hypothesis of that name, and it counts the banned use inside its proof.
theorem named (under : True) : True := by
  first | exact under | trivial
