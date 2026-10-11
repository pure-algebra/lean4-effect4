import Test.Dogfood.Scenario.Atomic.WriterSource

/-!
Concept: scope-lifetime-finalization, R11.
Consumer: saved-callback writer reservation transport of Atomic.Cleanup.log_debits.
The callbacks use existing source ownership and the actual native interpreter.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace Test.Dogfood.Scenario.Atomic.WriterCallbacks
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.SourceScope Effect4.Laws.Auto
open WriterPhase WriterSource

/-- An actual source callback consumes only its future active note reservation. -/
theorem value_bound (built : Api.Built) (admitted : Api.Author.build (shop .none) = .ok built)
    (id : Nat) (member : id ∈ requests) (callback : EffName) (value : Val)
    (owned : NameAt built.program callback) :
    current id (Program.contAOf built.program callback value) ≤ name id callback := by
  revert owned
  fun_cases Program.contAOf built.program callback value
  all_goals intro owned
  case case1 point =>
    exact resolve_bound built admitted id member (point.childWith 1 value)
      (childWith_at built.program point 1 value owned.1)
  case case2 point =>
    exact resolve_bound built admitted id member (point.childWith 1 value)
      (childWith_at built.program point 1 value owned.1)
  case case12 point previous =>
    simpa only [current, cata_prim, name, Point.child, Nat.add_zero] using resolve_bound built admitted id member (point.child 0)
      (child_at built.program point 0 owned)
  case case18 point context scope =>
    have first := resolve_bound built admitted id member (point.child 0)
      (child_at built.program point 0 owned.1)
    obtain ⟨acquire, release, source⟩ := owned.2.2
    have ordinary := ordinary_at built admitted id member point _ source (by intro _ _ wrong; cases wrong)
    have divided := WriterSource.siblings_le id point.path 0 1 (by decide) ordinary
    change current id (resolve built.program (point.child 0)) + WriterPhase.below id (point.path ++ [1]) ≤
      WriterPhase.below id point.path
    change current id (resolve built.program (point.child 0)) ≤ WriterPhase.below id (point.path ++ [0]) at first
    omega
  case case15 stored => exact store_value_bound id stored value
  case case22 acquired captured exit different found =>
    change current id (embed (finProgram captured exit)) + 0 ≤ 0
    have zero : current id (embed (finProgram captured exit)) = 0 := program_exact id (.finalizerOf captured exit)
    rw [zero]
    omega
  case case30 update region =>
    cases region with
    | program point =>
      unfold updateThenK
      split
      · split
        · simpa only [regionCode, name] using resolve_bound built admitted id member point owned
        · simp only [current, cata_prim, thunk, name, Nat.zero_add, Nat.add_zero, Nat.le_refl]
      · exact Nat.zero_le _
    | build _ _ _ => exact owned.elim
    | buildAdding _ _ _ => exact owned.elim
    | construct _ _ => exact owned.elim
  case case31 region previous =>
    cases region with
    | program point =>
      simpa only [regionCode, current, cata_prim, name, Nat.add_zero] using resolve_bound built admitted id member point owned
    | build _ _ _ => exact owned.elim
    | buildAdding _ _ _ => exact owned.elim
    | construct _ _ => exact owned.elim
  all_goals aesop (add norm simp [current, cata_prim, thunk, name, program, storeName, storeAction, operation,
    NameAt, StoreNameAt, RegionAt, Point.childWith, Point.child, badShape, regionCode, Prim.ofExit,
    updateThenK, addCurrentMemoMapK, combineWithK, mergeContextsK, serviceLookupK, bindServiceK]) (add safe apply [store_value_bound, (resolve_bound built admitted id member), child_at, childWith_at])

/-- An actual source cause callback spends only its future handler reservation. -/
theorem cause_bound (built : Api.Built) (admitted : Api.Author.build (shop .none) = .ok built)
    (id : Nat) (member : id ∈ requests) (callback : EffName) (cause : CauseV)
    (owned : NameAt built.program callback) :
    current id (Program.contEOf built.program callback cause) ≤ name id callback := by
  revert owned
  fun_cases Program.contEOf built.program callback cause
  all_goals intro owned
  case case1 point =>
    exact resolve_bound built admitted id member (point.childWith 1 (.exitErr cause))
      (childWith_at built.program point 1 (.exitErr cause) owned.1)
  case case2 point test body handler found value answer =>
    exact resolve_bound built admitted id member (point.childWith 1 value)
      (childWith_at built.program point 1 value owned.1)
  case case5 point =>
    exact resolve_bound built admitted id member (point.childWith 2 (.exitErr cause))
      (childWith_at built.program point 2 (.exitErr cause) owned)
  all_goals aesop (add norm simp [current, cata_prim, name, NameAt, store_cause_zero, Prim.ofExit])

/-- The native interpreter's completed view changes no source callback reservation. -/
theorem interp_value_bound (built : Api.Built) (admitted : Api.Author.build (shop .none) = .ok built)
    (id : Nat) (member : id ∈ requests) (view : List (FiberId × ExitV)) (callback : EffName) (value : Val)
    (owned : NameAt built.program callback) :
    current id ((interpAt built.program view built.table).contA callback value) ≤ name id callback := by
  cases callback <;> dsimp only [interpAt, RunInterp.toPrimInterp] <;>
    apply value_bound built admitted id member <;> exact owned

/-- The native interpreter retains the cause handler's future note reservation. -/
theorem interp_cause_bound (built : Api.Built) (admitted : Api.Author.build (shop .none) = .ok built)
    (id : Nat) (member : id ∈ requests) (view : List (FiberId × ExitV)) (callback : EffName) (cause : CauseV)
    (owned : NameAt built.program callback) :
    current id ((interpAt built.program view built.table).contE callback cause) ≤ name id callback := by
  cases callback <;> dsimp only [interpAt, RunInterp.toPrimInterp] <;>
    apply cause_bound built admitted id member <;> exact owned

end Test.Dogfood.Scenario.Atomic.WriterCallbacks
