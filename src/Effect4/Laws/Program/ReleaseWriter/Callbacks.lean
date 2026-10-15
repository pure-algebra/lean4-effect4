import Effect4.Laws.Program.ReleaseWriter.Stored
import Effect4.Laws.Program.NativeCallbacks

/-!
Concept: scope-lifetime-finalization R11.
Question: existing callbacks retain the release-write reservation they consume.
Reach: a direct-release source contract and actual native source-owned callback names.
Consumers: the crews' shared writer frame and evaluator debit.
The callback bound does not prove its captured value or the store observation.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace Effect4.Program.ReleaseWriter
open Effect4 Effect4.Machine Effect4.Program

/-- A native value callback spends its retained future write reservation. -/
theorem Source.value_bound {target : Target} {root : NativeEff} (source : Source target root)
    (callback : EffName) (value : Val) (owned : SourceScope.NameAt root callback) :
    current target (contAOf root callback value) ≤ name target callback := by
  revert owned
  fun_cases Program.contAOf root callback value
  all_goals intro owned
  case case1 point | case2 point => exact source.resolve_bound (point.childWith 1 value)
  case case12 point previous =>
    simpa only [current, pair, cata_prim, name, Point.child, Nat.add_zero] using
      source.resolve_bound (point.child 0)
  case case18 point context scope =>
    have bound := source.resolve_bound (point.child 0)
    change current target (resolve root (point.child 0)) ≤ leaf target (point.path ++ [0]) at bound
    rw [leaf_child_zero target _ 0 (by decide)] at bound
    simpa only [current, pair, cata_prim, successName, name, Nat.add_zero] using bound
  case case15 stored => exact Stored.value_bound target stored value
  case case22 acquired captured exit different found =>
    change current target (embed (finProgram captured exit)) + 0 ≤ 0
    rw [show current target (embed (finProgram captured exit)) = 0 from
      Stored.program_exact target (.finalizerOf captured exit)]
    exact Nat.le_refl 0
  case case32 update region flag =>
    cases region with
    | program point =>
      unfold updateThenK
      split
      · split
        · simp only [current, thunk, name, Nat.le_refl]
        · simp only [current, thunk, successName, name, Nat.zero_add, Nat.add_zero, Nat.le_refl]
      · exact Nat.zero_le _
    | build _ _ _ => exact owned.elim
    | buildAdding _ _ _ => exact owned.elim
    | construct _ _ => exact owned.elim
  case case33 region previous flag =>
    cases region with
    | program point => simp only [current, thunk, name, Nat.add_zero, Nat.le_refl]
    | build _ _ _ => exact owned.elim
    | buildAdding _ _ _ => exact owned.elim
    | construct _ _ => exact owned.elim
  all_goals aesop (add norm simp [current, pair, cata_prim, thunk, successName, name, program,
    storeName, storeAction, StoredWeights.program, StoredWeights.name, StoredWeights.action, operation,
    SourceScope.NameAt, SourceScope.StoreNameAt, SourceScope.RegionAt, Point.childWith, Point.child,
    leaf_child_one, badShape, regionCode, Prim.ofExit, updateThenK, addCurrentMemoMapK,
    combineWithK, mergeContextsK, serviceLookupK, bindServiceK])

/-- A cause callback spends only its retained handler reservation. -/
theorem Source.cause_bound {target : Target} {root : NativeEff} (source : Source target root)
    (callback : EffName) (cause : CauseV) (owned : SourceScope.NameAt root callback) :
    current target (contEOf root callback cause) ≤ name target callback := by
  revert owned
  fun_cases Program.contEOf root callback cause
  all_goals intro owned
  case case1 point => exact source.resolve_bound (point.childWith 1 (.exitErr cause))
  case case2 point test body handler found value answer => exact source.resolve_bound (point.childWith 1 value)
  case case5 point => exact source.resolve_bound (point.childWith 2 (.exitErr cause))
  all_goals aesop (add norm simp [current, pair, cata_prim, name, SourceScope.NameAt,
    Stored.cause_zero, Prim.ofExit])

/-- The native completed view changes no callback's source reservation. -/
theorem Source.interp_value_bound {target : Target} {root : NativeEff} (source : Source target root)
    (table : RowTable) (view : List (FiberId × ExitV)) (callback : EffName) (value : Val)
    (owned : SourceScope.NameAt root callback) :
    current target ((interpAt root view table).contA callback value) ≤ name target callback := by
  cases callback <;> dsimp only [interpAt, RunInterp.toPrimInterp] <;>
    apply source.value_bound <;> exact owned

/-- The native completed view retains the handler's source reservation. -/
theorem Source.interp_cause_bound {target : Target} {root : NativeEff} (source : Source target root)
    (table : RowTable) (view : List (FiberId × ExitV)) (callback : EffName) (cause : CauseV)
    (owned : SourceScope.NameAt root callback) :
    current target ((interpAt root view table).contE callback cause) ≤ name target callback := by
  cases callback <;> dsimp only [interpAt, RunInterp.toPrimInterp] <;>
    apply source.cause_bound <;> exact owned

end Effect4.Program.ReleaseWriter
