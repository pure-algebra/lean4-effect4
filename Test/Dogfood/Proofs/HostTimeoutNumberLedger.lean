import Test.Dogfood.Proofs.HostTimeoutNumberSteps

/-!
Placement: scope-lifetime-finalization R11 and translation-simulation R10.
Question: the ordered heap assertion of the two remaining Timeout planned goals.
Consumer: the numeric source and command history assertion.
Cleanup entries retain their own position and exact Boolean field.
The reader connects that assertion to the original cleanup observation.
The source history still must supply the writer's count and ordering premises.
-/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Test.Dogfood.Proofs.HostTimeoutNumberLedger
open Effect4 Effect4.Machine Effect4.Program
open HostTimeoutSource HostTimeoutSlots HostTimeoutFlow HostTimeoutNumberSteps
open Test.Dogfood.Scenario.Timeout

/-- Each appended cleanup entry records exactly its next position. -/
inductive CleanupsAt : List Val → Prop
  | nil : CleanupsAt []
  | append {entries : List Val} (previous : CleanupsAt entries) (interrupted : Bool) :
      CleanupsAt (entries ++ [.list [.nat (entries.length + 1), .bool interrupted]])

/-- The exact number reader of `Observation.cleaned`. -/
def cleanupNumbers (entries : List Val) : List Nat :=
  entries.filterMap fun entry => match entry with
    | .list [.nat attempt, _] => some attempt
    | _ => none

/-- An exact cleanup log has one readable number per entry. -/
theorem cleanup_numbers (entries : List Val) (ordered : CleanupsAt entries) :
    cleanupNumbers entries = (List.range entries.length).map (· + 1) := by
  induction ordered with
  | nil => rfl
  | @append entries previous interrupted ih =>
    simp only [cleanupNumbers, List.filterMap_append, List.filterMap_cons,
      List.filterMap_nil, List.length_append, List.length_cons, List.length_nil,
      Nat.zero_add, List.range_succ, List.map_append, List.map_cons, List.map_nil]
    exact congrArg (· ++ [entries.length + 1]) ih

/-- The cleanup reader preserves the length needed by both original count inequalities. -/
theorem cleanup_length (entries : List Val) (ordered : CleanupsAt entries) :
    (cleanupNumbers entries).length = entries.length := by
  rw [cleanup_numbers entries ordered, List.length_map, List.length_range]

/-- The concrete number-list comparison needs no classical order instance. -/
theorem number_list_self (numbers : List Nat) : (numbers == numbers) = true := by
  induction numbers with
  | nil => rfl
  | cons number rest ih =>
    change (decide (number = number) && (rest == rest)) = true
    rw [decide_eq_true (Eq.refl number), ih]
    rfl

/-- The exact ordered heap assertion discharges the original cleanup observation. -/
theorem cleanup_observation (observation : Observation)
    (ordered : CleanupsAt observation.cleanups)
    (lower : observation.cleanups.length ≤ observation.attempts)
    (upper : observation.attempts ≤ observation.cleanups.length + 1) :
    observation.cleanupKeeps = true := by
  have decoded : observation.cleaned = cleanupNumbers observation.cleanups := rfl
  have length := cleanup_length observation.cleanups ordered
  have sequence := cleanup_numbers observation.cleanups ordered
  unfold Observation.cleanupKeeps
  rw [decoded, length, sequence]
  rw [number_list_self]
  rw [decide_eq_true lower, decide_eq_true upper]
  rfl

/-- The actual cleanup source writer appends the next position when its saved read matches count. -/
theorem cleanup_write (view : View) (state : Stores) (fuel count delay : Nat)
    (n : Fin 4) (error : Val) (exit : ExitV) (entries completed : List Val)
    (ordered : CleanupsAt entries) (own : count = entries.length + 1) :
    let written := entries ++ [.list [.nat count, .bool (interruptionFlag exit)]]
    sourceStep view
      (sourcePoint [1,1,1,0,0,1,0,0,0,0,0,0,1,1,0]
        (ready (Val.cell ⟨0⟩) (Val.cell ⟨1⟩) (Val.cell ⟨2⟩) n delay error ++
          [reifyExitVal exit, .nat count]) fuel)
      {state with refs := numberHeap count entries completed} =
      some ({state with refs := numberHeap count written completed}, .unit) ∧
      CleanupsAt written ∧ written.length = count := by
  dsimp only
  refine ⟨cleanup_note view state fuel count count delay n error exit entries completed, ?_, ?_⟩
  · rw [own]
    exact .append ordered (interruptionFlag exit)
  · simp only [List.length_append, List.length_cons, List.length_nil, Nat.zero_add]
    exact own.symm

/-- Starting the next counted attempt requires the preceding cleanup log to be complete.
This is the heap component; command history must supply that source-order premise. -/
theorem count_write (view : View) (state : Stores) (fuel count delay : Nat)
    (n : Fin 4) (error : Val) (entries completed : List Val)
    (ordered : CleanupsAt entries) (complete : entries.length = count)
    (bounded : count ≤ n.val) :
    sourceStep view
      (sourcePoint [1,1,1,0,0,1,0,0,0,0,0,0,0,0]
        (ready (Val.cell ⟨0⟩) (Val.cell ⟨1⟩) (Val.cell ⟨2⟩) n delay error) fuel)
      {state with refs := numberHeap count entries completed} =
      some ({state with refs := numberHeap (count + 1) entries completed}, .unit) ∧
      entries.length ≤ count + 1 ∧ count + 1 ≤ entries.length + 1 ∧ count + 1 ≤ 4 ∧
      CleanupsAt entries := by
  refine ⟨count_update view state fuel count delay n error entries completed, ?_, ?_, ?_, ordered⟩
  all_goals have bound := n.isLt; omega

/-- Completed entries retain the exact saved exit written by the source finalizer. -/
inductive FormsAt : List Val → List ExitV → Prop
  | nil : FormsAt [] []
  | cons (number : Nat) (exit : ExitV) {entries : List Val} {exits : List ExitV}
      (rest : FormsAt entries exits) :
      FormsAt (.list [.nat number, reifyExitVal exit] :: entries) (exit :: exits)

/-- The source's finalizer writer extends the exact completed-exit log. -/
theorem forms_append {entries : List Val} {exits : List ExitV} (good : FormsAt entries exits)
    (number : Nat) (exit : ExitV) :
    FormsAt (entries ++ [.list [.nat number, reifyExitVal exit]]) (exits ++ [exit]) := by
  induction good with
  | nil => exact .cons number exit .nil
  | cons n saved rest ih => exact .cons n saved ih

/-- Decode the actual completed log entry, retaining no guess about the winner's role. -/
def entryExit : Val → Option ExitV
  | .list [.nat _, written] => exitImage.ofVal written
  | _ => none

/-- The exact completed log reader recovers each original saved exit. -/
theorem form_exits {entries : List Val} {exits : List ExitV} (good : FormsAt entries exits) :
    entries.filterMap entryExit = exits := by
  induction good with
  | nil => rfl
  | cons number exit rest ih =>
    simp only [List.filterMap_cons, entryExit, reifyExitVal_eq_exitImage,
      exitImage.ofVal_toVal]
    exact congrArg (exit :: ·) ih

/-- The original observation's completed exits depend only on the exact third-cell entries. -/
theorem completed_exits (run : Run) (entries : List Val) (stored : Scenario.cell run 2 = some (.list entries)) :
    (completedForms run).map (·.exit) = entries.filterMap entryExit := by
  unfold completedForms
  rw [stored, List.map_filterMap]
  dsimp only
  calc
    _ = entries.zipIdx.filterMap (fun entry => entryExit entry.1) := by
      congr 1
      funext entry
      rcases entry with ⟨value, index⟩
      dsimp only
      split
      · simp only [entryExit, Option.map_map, Function.comp_def, Option.map_id']
      · unfold entryExit
        split
        · aesop
        · rfl
    _ = entries.filterMap entryExit := by
      change entries.zipIdx.filterMap (entryExit ∘ Prod.fst) = _
      rw [← List.filterMap_map (f := Prod.fst) (g := entryExit), List.zipIdx_map_fst]

/-- Each source completed note preserves the exact exit sequence consumed by retry observation. -/
theorem completed_write (view : View) (state : Stores) (fuel count seen delay : Nat)
    (n : Fin 4) (error : Val) (exit : ExitV) (entries completed : List Val)
    (exits : List ExitV) (good : FormsAt completed exits) :
    let written := completed ++ [.list [.nat seen, reifyExitVal exit]]
    sourceStep view
      (sourcePoint [1,1,1,0,0,1,0,0,1,1]
        (ready (Val.cell ⟨0⟩) (Val.cell ⟨1⟩) (Val.cell ⟨2⟩) n delay error ++
          [reifyExitVal exit, .nat seen]) fuel)
      {state with refs := numberHeap count entries completed} =
      some ({state with refs := numberHeap count entries written}, .unit) ∧
      FormsAt written (exits ++ [exit]) :=
  ⟨completed_note view state fuel count seen delay n error exit entries completed,
    forms_append good seen exit⟩

/-- The retry predicate reads only the complete exit of a completed form. -/
def exitRetries (exit : ExitV) : Bool :=
  FormOutcome.retries ⟨0, none, .unknown, exit⟩

/-- Exact completed-exit decoding discharges the original retry observation.
Command history must supply the predecessor prefix, count gap, and count bound. -/
theorem retry_observation (observation : Observation) (exits : List ExitV)
    (decoded : observation.forms.map (·.exit) = exits)
    (declared : (exits.take (observation.attempts - 1)).all exitRetries = true)
    (gap : observation.attempts ≤ exits.length + 1) (bound : observation.attempts ≤ 4) :
    observation.retriesDeclared = true := by
  have length : observation.forms.length = exits.length := by
    have mapped := congrArg List.length decoded
    simpa only [List.length_map] using mapped
  have selectedPrefix : (observation.forms.take (observation.attempts - 1)).all FormOutcome.retries =
      (exits.take (observation.attempts - 1)).all exitRetries := by
    rw [← decoded, ← List.map_take, List.all_map]
    rfl
  unfold Observation.retriesDeclared
  rw [selectedPrefix, declared, length, decide_eq_true gap, decide_eq_true bound]
  rfl

end Test.Dogfood.Proofs.HostTimeoutNumberLedger
