import ProofGraph.StatementCensus

/-!
# Controls of `#statement_census`

The battery of `ProofGraph.StatementCensus` (`tools/ProofGraph/StatementCensus.lean`):
- two theorems with one statement under different binder names, binder annotations and universe
  level names are found as one group;
- two theorems with different statements stay apart;
- one pair whose statements differ only by an `abbrev` is missed by the default mode and found in
  `#statement_census reducible`;
- an unimported module name is refused.
-/

namespace Test.Audit.StatementCensusControls

/-- An `abbrev` wrapper that only reducible unfolding equates with `Nat.add`. -/
abbrev addAlias (a b : Nat) : Nat := a + b

/-- First member of the binder-renamed duplicate pair. -/
theorem binderFirst.{u} {α : Type u} (x : α) : x = x := rfl

/-- Second member of the binder-renamed duplicate pair: different universe parameter name,
explicit binder annotation, and binder name. -/
theorem binderSecond.{v} (β : Type v) (y : β) : y = y := rfl

/-- First member of the `abbrev` pair. -/
theorem abbrevFirst (n m : Nat) : addAlias n m = n + m := rfl

/-- Second member of the `abbrev` pair: stated with `n + m` in place of `addAlias n m`. -/
theorem abbrevSecond (a b : Nat) : a + b = a + b := rfl

/-- Distinct statement (uses `binderFirst` and `abbrevSecond` so use counts are exercised). -/
theorem distinctLeft (n : Nat) : n + 0 = n := by
  have _ := binderFirst n
  have _ := abbrevSecond n 0
  rfl

/-- Second distinct statement: flipped argument order is not grouped with `distinctLeft`. -/
theorem distinctRight (n : Nat) : 0 + n = n := Nat.zero_add n

-- red: an unimported module is refused
/-- error: #statement_census: the module Missing.Census.Module is not imported -/
#guard_msgs (error) in
#statement_census Missing.Census.Module

-- green (default mode): only `binderFirst` and `binderSecond` form a group; `distinctLeft` and
-- `distinctRight` stay apart, and `abbrevFirst` / `abbrevSecond` stay apart without unfolding
/--
info: #statement_census: 6 theorems in 1 modules; 1 duplicate groups:
  Test.Audit.StatementCensusControls.binderFirst (Test.Audit.StatementCensusControls, 1 uses), Test.Audit.StatementCensusControls.binderSecond (Test.Audit.StatementCensusControls, 0 uses)
-/
#guard_msgs in
#statement_census Test.Audit.StatementCensusControls

-- green (reducible mode): `abbrevFirst` and `abbrevSecond` are found alongside the binder pair
/--
info: #statement_census reducible: 6 theorems in 1 modules; 2 duplicate groups:
  Test.Audit.StatementCensusControls.abbrevFirst (Test.Audit.StatementCensusControls, 0 uses), Test.Audit.StatementCensusControls.abbrevSecond (Test.Audit.StatementCensusControls, 1 uses)
  Test.Audit.StatementCensusControls.binderFirst (Test.Audit.StatementCensusControls, 1 uses), Test.Audit.StatementCensusControls.binderSecond (Test.Audit.StatementCensusControls, 0 uses)
-/
#guard_msgs in
#statement_census reducible Test.Audit.StatementCensusControls

end Test.Audit.StatementCensusControls
