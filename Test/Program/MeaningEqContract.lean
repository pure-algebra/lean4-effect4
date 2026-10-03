import Effect4.Laws.Program.MeaningEq

/-! `straight-composition-agreement`: a source edit used under binding, failure and cleanup,
with independent runtime budgets. The limits follow the existing denotation contract. -/
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

namespace Test.Program.MeaningEqContract
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Denote
open Effect4.Program.Agreement

def allocate : NativeEff := .perform .refMake (.lit (.nat 0))
def writeThenFail : NativeEff :=
  .bind (.perform .refSet (.app "pair" (.cons (.var 0) (.cons (.lit (.nat 7)) .nil))))
    (.fail (.lit (.nat 5)))
def cleanup : NativeEff := .perform (.refUpdate FnName.incr) (.var 0)
def original : NativeEff := .bind allocate (.onExit (.suspend writeThenFail) (.suspend cleanup))
def rewritten : NativeEff := .bind allocate (.onExit writeThenFail cleanup)

/-- Actual composition consumer: two local suspension edits underneath bind and onExit. -/
theorem rewrite_agrees : StraightEq original rewritten :=
  (StraightEq.refl allocate (by decide)).bind
    ((StraightEq.suspend_remove writeThenFail (by decide)).onExit
      (StraightEq.suspend_remove cleanup (by decide)))

example : (Api.run original 100).outcome = .finished ∧
    (Api.run rewritten 120).outcome = .finished ∧
    (Api.run original 100).exit = (Api.run rewritten 120).exit ∧
    (Api.run original 100).stores = (Api.run rewritten 120).stores :=
  rewrite_agrees.run_agrees 100 120 (by decide) (by decide) (by decide) (by decide)

#guard (Api.run original 100).exit = some (.failure (.fail (.tag 5)))
#guard (Api.run original 100).stores.refs = [.nat 8]
#guard (Api.run rewritten 120).exit = some (.failure (.fail (.tag 5)))
#guard (Api.run rewritten 120).stores.refs = [.nat 8]
example : (Api.run original (StraightEq.fuelFor original)).exit =
    (Api.run rewritten (StraightEq.fuelFor rewritten)).exit :=
  rewrite_agrees.run_agrees_at_bound.2.2.1

#guard (Api.run original 0).outcome != .finished
#guard depth original > depth rewritten
#guard steps original > steps rewritten

-- A relation on exit alone would accept these, but our complete-store observation refuses.
def leaveCell : NativeEff := .bind allocate (.succeed (.lit (.nat 3)))
def leaveNothing : NativeEff := .succeed (.lit (.nat 3))
#guard (meaning leaveCell [] Stores.empty).1 = (meaning leaveNothing [] Stores.empty).1
#guard (meaning leaveCell [] Stores.empty).2 != (meaning leaveNothing [] Stores.empty).2

example (h : StraightEq leaveCell leaveNothing) : False := by
  have cells := congrArg (fun result => result.2.refs) (h.same [] Stores.empty)
  change [Val.nat 0] = [] at cells
  cases cells

-- The outside-fragment denotation fallback must not count as a semantic comparison.
def sleeping : NativeEff := .perform .sleep (.lit (.nat 1))
#guard Straight sleeping = false
example (h : StraightEq sleeping sleeping) : False := by
  have fragment := h.left_straight
  contradiction

-- Congruence covers selection, caught failure, materialized exits and both cause arms.
example {a a' b b' : NativeEff} (ha : StraightEq a a') (hb : StraightEq b b') :
    StraightEq (.select (.lit (.bool true)) .bool (.exit a) (.catchCause a b))
      (.select (.lit (.bool true)) .bool (.exit a') (.catchCause a' b')) :=
  StraightEq.select _ _ ha.exit (ha.catchCause hb)

example {a a' v v' c c' : NativeEff}
    (ha : StraightEq a a') (hv : StraightEq v v') (hc : StraightEq c c') :
    StraightEq (.suspend (.matchCause a v c)) (.suspend (.matchCause a' v' c')) :=
  (ha.matchCause hv hc).suspend_congr

/-- info: 'Effect4.Program.Denote.StraightEq.run_agrees' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms StraightEq.run_agrees
/-- info: 'Test.Program.MeaningEqContract.rewrite_agrees' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms rewrite_agrees

end Test.Program.MeaningEqContract
