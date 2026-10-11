import Test.Dogfood.Proofs.HostTimeoutNumberLedger
import Effect4.Laws.Program.NativeHeapExecution

/-!
Placement: scope-lifetime-finalization R11 and translation-simulation R10.
Question: the heap component of the two original remaining Timeout goals.
Consumer: the state-indexed source contract and actual command history assertion.
The assertion reads the actual three reference cells and retains the source-order premises.
The assertion alone establishes no reached history, callback correlation, or progress.
-/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Test.Dogfood.Proofs.HostTimeoutNumberState
open Effect4 Effect4.Machine Effect4.Program
open HostTimeoutSource HostTimeoutSlots HostTimeoutFlow HostTimeoutNumberSteps HostTimeoutNumberLedger
open Test.Dogfood.Scenario.Timeout

/-- The allocated cells retain both logs and the one-attempt gap through their actual writers. -/
structure Numbers (count : Nat) (cleanups completed : List Val) (exits : List ExitV) : Prop where
  cleanupsAt : CleanupsAt cleanups
  formsAt : FormsAt completed exits
  cleanupLower : cleanups.length ≤ count
  cleanupUpper : count ≤ cleanups.length + 1
  formLower : exits.length ≤ cleanups.length
  formUpper : count ≤ exits.length + 1
  bound : count ≤ 4

/-- Plain reply histories additionally retain the completed predecessor's declared failures. -/
def Declared (count : Nat) (exits : List ExitV) : Prop :=
  (exits.take (count - 1)).all exitRetries = true

/-- Allocation stages are retained instead of assuming all three cells already exist. -/
inductive HeapAt : RefHeap → Prop
  | empty : HeapAt []
  | count : HeapAt [.nat 0]
  | cleanup : HeapAt [.nat 0, .list []]
  | ready (count : Nat) (cleanups completed : List Val) (exits : List ExitV)
      (numbers : Numbers count cleanups completed exits) :
      HeapAt (numberHeap count cleanups completed)

/-- The source's final allocation installs the initial complete numeric heap. -/
theorem initial_numbers : Numbers 0 [] [] [] :=
  ⟨.nil, .nil, Nat.le_refl _, by omega, Nat.le_refl _, by omega, by omega⟩

/-- The ready assertion's exact count and logs discharge the original cleanup reader. -/
theorem cleanup_ready (run : Run) (count : Nat) (cleanups completed : List Val) (exits : List ExitV)
    (heap : run.machine.state.refs = numberHeap count cleanups completed)
    (numbers : Numbers count cleanups completed exits) :
    (observe run).cleanupKeeps = true := by
  have counted : (observe run).attempts = count := by
    change (match Scenario.cell run 0 with | some (Val.nat n) => n | _ => 0) = count
    change (match run.machine.state.refs[0]? with | some (Val.nat n) => n | _ => 0) = count
    rw [heap]
    rfl
  have logged : (observe run).cleanups = cleanups := by
    change (match run.machine.state.refs[1]? with | some (Val.list entries) => entries | _ => []) = cleanups
    rw [heap]
    rfl
  exact cleanup_observation (observe run) (logged ▸ numbers.cleanupsAt)
    (by rw [logged, counted]; exact numbers.cleanupLower)
    (by rw [logged, counted]; exact numbers.cleanupUpper)

/-- Every allocation stage and ready heap supports the unchanged original cleanup observation. -/
theorem cleanup_heap (run : Run) (heap : HeapAt run.machine.state.refs) :
    (observe run).cleanupKeeps = true := by
  generalize shape : run.machine.state.refs = refs at heap
  cases heap with
  | empty =>
    have counted : (observe run).attempts = 0 := by
      change (match run.machine.state.refs[0]? with | some (Val.nat n) => n | _ => 0) = 0
      rw [shape]; rfl
    have logged : (observe run).cleanups = [] := by
      change (match run.machine.state.refs[1]? with | some (Val.list entries) => entries | _ => []) = []
      rw [shape]; rfl
    exact cleanup_observation (observe run) (logged ▸ CleanupsAt.nil)
      (by rw [logged, counted]; exact Nat.le_refl _)
      (by rw [logged, counted]; decide)
  | count =>
    have counted : (observe run).attempts = 0 := by
      change (match run.machine.state.refs[0]? with | some (Val.nat n) => n | _ => 0) = 0
      rw [shape]; rfl
    have logged : (observe run).cleanups = [] := by
      change (match run.machine.state.refs[1]? with | some (Val.list entries) => entries | _ => []) = []
      rw [shape]; rfl
    exact cleanup_observation (observe run) (logged ▸ CleanupsAt.nil)
      (by rw [logged, counted]; exact Nat.le_refl _)
      (by rw [logged, counted]; decide)
  | cleanup =>
    have counted : (observe run).attempts = 0 := by
      change (match run.machine.state.refs[0]? with | some (Val.nat n) => n | _ => 0) = 0
      rw [shape]; rfl
    have logged : (observe run).cleanups = [] := by
      change (match run.machine.state.refs[1]? with | some (Val.list entries) => entries | _ => []) = []
      rw [shape]; rfl
    exact cleanup_observation (observe run) (logged ▸ CleanupsAt.nil)
      (by rw [logged, counted]; exact Nat.le_refl _)
      (by rw [logged, counted]; decide)
  | ready count cleanups completed exits numbers => exact cleanup_ready run count cleanups completed exits shape numbers

/-- Exact completed exits and the declared prefix discharge the original retry reader. -/
theorem retry_ready (run : Run) (count : Nat) (cleanups completed : List Val) (exits : List ExitV)
    (heap : run.machine.state.refs = numberHeap count cleanups completed)
    (numbers : Numbers count cleanups completed exits) (declared : Declared count exits) :
    (observe run).retriesDeclared = true := by
  have counted : (observe run).attempts = count := by
    change (match run.machine.state.refs[0]? with | some (Val.nat n) => n | _ => 0) = count
    rw [heap]; rfl
  have stored : Scenario.cell run 2 = some (.list completed) := by
    change run.machine.state.refs[2]? = some (.list completed)
    rw [heap]; rfl
  have decoded : (observe run).forms.map (·.exit) = exits :=
    (completed_exits run completed stored).trans (form_exits numbers.formsAt)
  exact retry_observation (observe run) exits decoded (by rw [counted]; exact declared)
    (by rw [counted]; exact numbers.formUpper) (by rw [counted]; exact numbers.bound)

/-- Starting the next attempt consumes a complete cleanup and completed-form prefix. -/
theorem count_numbers {count : Nat} {cleanups completed : List Val} {exits : List ExitV}
    (numbers : Numbers count cleanups completed exits) (n : Fin 4)
    (cleanupComplete : cleanups.length = count) (formComplete : exits.length = count)
    (cursor : count ≤ n.val) : Numbers (count + 1) cleanups completed exits := by
  refine ⟨numbers.cleanupsAt, numbers.formsAt, ?_, ?_, numbers.formLower, ?_, ?_⟩
  all_goals have sourceBound := n.isLt; omega

/-- Finishing the active attempt appends its own position without changing either count or forms. -/
theorem cleanup_numbers {count : Nat} {cleanups completed : List Val} {exits : List ExitV}
    (numbers : Numbers count cleanups completed exits) (own : count = cleanups.length + 1)
    (interrupted : Bool) :
    Numbers count (cleanups ++ [.list [.nat count, .bool interrupted]]) completed exits := by
  refine ⟨?_, numbers.formsAt, ?_, ?_, ?_, numbers.formUpper, numbers.bound⟩
  · rw [own]; exact .append numbers.cleanupsAt interrupted
  all_goals have prior := numbers.formLower
  all_goals simp only [List.length_append, List.length_cons, List.length_nil, Nat.zero_add]; omega

/-- Publishing the timeout result follows its completed attempt cleanup and preserves the gaps. -/
theorem completed_numbers {count : Nat} {cleanups completed : List Val} {exits : List ExitV}
    (numbers : Numbers count cleanups completed exits)
    (cleanupComplete : cleanups.length = count) (own : exits.length + 1 = count)
    (seen : Nat) (exit : ExitV) :
    Numbers count cleanups (completed ++ [.list [.nat seen, reifyExitVal exit]]) (exits ++ [exit]) := by
  refine ⟨numbers.cleanupsAt, forms_append numbers.formsAt seen exit,
    numbers.cleanupLower, numbers.cleanupUpper, ?_, ?_, numbers.bound⟩
  all_goals simp only [List.length_append, List.length_cons, List.length_nil, Nat.zero_add]; omega

/-- A new count retains exactly the complete declared prefix it consumed. -/
theorem count_declared (count : Nat) (exits : List ExitV)
    (complete : exits.length = count) (declared : exits.all exitRetries = true) :
    Declared (count + 1) exits := by
  unfold Declared
  rw [Nat.add_sub_cancel, ← complete, List.take_length]
  exact declared

/-- Appending a result cannot change any previously consumed declared predecessor. -/
theorem completed_declared (count : Nat) (exits : List ExitV) (exit : ExitV)
    (before : Declared count exits) (gap : count ≤ exits.length + 1) :
    Declared count (exits ++ [exit]) := by
  unfold Declared at before ⊢
  rw [List.take_append_of_le_length (by omega)]
  exact before

/-- Exact reference inputs retain the source point and its actual heap phase.
The native command invariant must establish this predicate before evaluating a reference leaf. -/
inductive ReferenceAt : Point → RefHeap → Prop
  | countMake (fuel : Nat) : ReferenceAt (sourcePoint [0] [] fuel) []
  | cleanupMake (fuel : Nat) : ReferenceAt
      (sourcePoint [1,0] [Val.cell ⟨0⟩] fuel) [.nat 0]
  | completedMake (fuel : Nat) : ReferenceAt
      (sourcePoint [1,1,0] [Val.cell ⟨0⟩, Val.cell ⟨1⟩] fuel) [.nat 0, .list []]
  | countUpdate (fuel delay : Nat) (n : Fin 4) (error : Val)
      (cleanups completed : List Val) (exits : List ExitV)
      (numbers : Numbers n.val cleanups completed exits)
      (cleanupComplete : cleanups.length = n.val) (formComplete : exits.length = n.val) :
      ReferenceAt
        (sourcePoint [1,1,1,0,0,1,0,0,0,0,0,0,0,0]
          (ready (Val.cell ⟨0⟩) (Val.cell ⟨1⟩) (Val.cell ⟨2⟩) n delay error) fuel)
        (numberHeap n.val cleanups completed)
  | cleanupRead (fuel delay : Nat) (n : Fin 4) (error : Val) (exit : ExitV)
      (cleanups completed : List Val) (exits : List ExitV)
      (numbers : Numbers (n.val + 1) cleanups completed exits)
      (own : n.val + 1 = cleanups.length + 1) :
      ReferenceAt
        (sourcePoint [1,1,1,0,0,1,0,0,0,0,0,0,1,0]
          (ready (Val.cell ⟨0⟩) (Val.cell ⟨1⟩) (Val.cell ⟨2⟩) n delay error ++
            [reifyExitVal exit]) fuel)
        (numberHeap (n.val + 1) cleanups completed)
  | cleanupNote (fuel delay : Nat) (n : Fin 4) (error : Val) (exit : ExitV)
      (cleanups completed : List Val) (exits : List ExitV)
      (numbers : Numbers (n.val + 1) cleanups completed exits)
      (own : n.val + 1 = cleanups.length + 1) :
      ReferenceAt
        (sourcePoint [1,1,1,0,0,1,0,0,0,0,0,0,1,1,0]
          (ready (Val.cell ⟨0⟩) (Val.cell ⟨1⟩) (Val.cell ⟨2⟩) n delay error ++
            [reifyExitVal exit, .nat (n.val + 1)]) fuel)
        (numberHeap (n.val + 1) cleanups completed)
  | completedRead (fuel delay : Nat) (n : Fin 4) (error : Val) (exit : ExitV)
      (cleanups completed : List Val) (exits : List ExitV)
      (numbers : Numbers (n.val + 1) cleanups completed exits)
      (cleanupComplete : cleanups.length = n.val + 1) (own : exits.length = n.val) :
      ReferenceAt
        (sourcePoint [1,1,1,0,0,1,0,0,1,0]
          (ready (Val.cell ⟨0⟩) (Val.cell ⟨1⟩) (Val.cell ⟨2⟩) n delay error ++
            [reifyExitVal exit]) fuel)
        (numberHeap (n.val + 1) cleanups completed)
  | completedNote (fuel delay : Nat) (n : Fin 4) (error : Val) (exit : ExitV)
      (cleanups completed : List Val) (exits : List ExitV)
      (numbers : Numbers (n.val + 1) cleanups completed exits)
      (cleanupComplete : cleanups.length = n.val + 1) (own : exits.length = n.val) :
      ReferenceAt
        (sourcePoint [1,1,1,0,0,1,0,0,1,1]
          (ready (Val.cell ⟨0⟩) (Val.cell ⟨1⟩) (Val.cell ⟨2⟩) n delay error ++
            [reifyExitVal exit, .nat (n.val + 1)]) fuel)
        (numberHeap (n.val + 1) cleanups completed)

/-- The actual source answer retains exact allocated handles and the post-state count read. -/
def ReferenceAnswer (point : Point) (heap : RefHeap) (value : Val) : Prop :=
  match point.path with
  | [0] => value = Val.cell ⟨0⟩
  | [1,0] => value = Val.cell ⟨1⟩
  | [1,1,0] => value = Val.cell ⟨2⟩
  | [1,1,1,0,0,1,0,0,0,0,0,0,1,0] | [1,1,1,0,0,1,0,0,1,0] =>
    ∃ count cleanups completed, heap = numberHeap count cleanups completed ∧ value = .nat count
  | _ => value = .unit

/-- All eight actual reference leaves retain the numeric heap and their precise successful answers.
The producer premise is source-order information, not a strengthened original scenario premise. -/
theorem reference_step (view : View) (state : Stores) (point : Point)
    (owned : ReferenceAt point state.refs) :
    ∃ next value, sourceStep view point state = some (next, value) ∧
      HeapAt next.refs ∧ ReferenceAnswer point next.refs value := by
  generalize stored : state.refs = heap at owned
  have overwrite : {state with refs := heap} = state := by rw [← stored]
  cases owned with
  | countMake fuel =>
    have step := count_make view state fuel
    rw [overwrite] at step
    exact ⟨_, _, step, .count, rfl⟩
  | cleanupMake fuel =>
    have step := cleanup_make view state fuel
    rw [overwrite] at step
    exact ⟨_, _, step, .cleanup, rfl⟩
  | completedMake fuel =>
    have step := completed_make view state fuel
    rw [overwrite] at step
    exact ⟨_, _, step, .ready 0 [] [] [] initial_numbers, rfl⟩
  | countUpdate fuel delay n error cleanups completed exits numbers cleanupComplete formComplete =>
    have step := count_update view state fuel n.val delay n error cleanups completed
    rw [overwrite] at step
    exact ⟨_, _, step, .ready (n.val + 1) cleanups completed exits
      (count_numbers numbers n cleanupComplete formComplete (Nat.le_refl _)), rfl⟩
  | cleanupRead fuel delay n error exit cleanups completed exits numbers own =>
    have step := cleanup_read view state fuel (n.val + 1) delay n error exit cleanups completed
    rw [overwrite] at step
    exact ⟨_, _, step, stored.symm ▸ HeapAt.ready (n.val + 1) cleanups completed exits numbers,
      n.val + 1, cleanups, completed, stored, rfl⟩
  | cleanupNote fuel delay n error exit cleanups completed exits numbers own =>
    have step := cleanup_note view state fuel (n.val + 1) (n.val + 1) delay n error exit cleanups completed
    rw [overwrite] at step
    exact ⟨_, _, step, .ready (n.val + 1) _ completed exits
      (cleanup_numbers numbers own (interruptionFlag exit)), rfl⟩
  | completedRead fuel delay n error exit cleanups completed exits numbers cleanupComplete own =>
    have step := completed_read view state fuel (n.val + 1) delay n error exit cleanups completed
    rw [overwrite] at step
    exact ⟨_, _, step, stored.symm ▸ HeapAt.ready (n.val + 1) cleanups completed exits numbers,
      n.val + 1, cleanups, completed, stored, rfl⟩
  | completedNote fuel delay n error exit cleanups completed exits numbers cleanupComplete own =>
    have step := completed_note view state fuel (n.val + 1) (n.val + 1) delay n error exit cleanups completed
    rw [overwrite] at step
    exact ⟨_, _, step, .ready (n.val + 1) cleanups _ (exits ++ [exit])
      (completed_numbers numbers cleanupComplete (by omega) (n.val + 1) exit), rfl⟩

/-- Canonical reference points erase only metadata unused by the source's synchronous reference operations. -/
def referencePoint (point : Point) : Point :=
  {point with tape := [], completed := [], root := 0, params := [], call := []}

/-- Reference source compilation ignores tape, completed exits, call roots, and parameter stacks. -/
theorem reference_code_fields (point : Point) (op : NativeOp) (request : Term) (fuel : Nat)
    (positive : point.fuel = fuel + 1)
    (node : Node.at_ (.eff HostTimeoutSource.program) point.path = some (.eff (.perform op request)))
    (reference : op = .refMake ∨ op = .refGet ∨ ∃ term, op = .refUpdateWith term) :
    resolve HostTimeoutSource.program point = resolve HostTimeoutSource.program (referencePoint point) := by
  have sameNode : Node.at_ (.eff HostTimeoutSource.program) (referencePoint point).path =
      some (.eff (.perform op request)) := node
  rw [Agreement.resolve_of_at node, Agreement.resolve_of_at sameNode,
    Agreement.compileEff_perform op request positive,
    Agreement.compileEff_perform op request (p := referencePoint point) positive]
  rcases reference with rfl | rfl | ⟨term, rfl⟩
  all_goals rfl

/-- The numeric reference assertion follows the generated source reference census. -/
theorem reference_source {point : Point} {heap : RefHeap} (owned : ReferenceAt point heap) :
    ∃ op request fuel,
      Node.at_ (.eff HostTimeoutSource.program) point.path = some (.eff (.perform op request)) ∧
      (op = .refMake ∨ op = .refGet ∨ ∃ term, op = .refUpdateWith term) ∧
      point.fuel = fuel + 1 := by
  have member : point.path ∈ refPaths := by
    cases owned
    all_goals dsimp only [sourcePoint]
    all_goals rw [refPaths_eq]
    all_goals decide
  have positive : ∃ fuel, point.fuel = fuel + 1 := by
    cases owned
    all_goals exact ⟨_, rfl⟩
  obtain ⟨fuel, positive⟩ := positive
  have source : ∃ op request,
      Node.at_ (.eff HostTimeoutSource.program) point.path = some (.eff (.perform op request)) ∧
      (op = .refMake ∨ op = .refGet ∨ ∃ term, op = .refUpdateWith term) := by
    rw [refPaths_eq] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with path | path | path | path | path | path | path | path
    all_goals refine ⟨(HostTimeoutNative.performParts point.path).1, (HostTimeoutNative.performParts point.path).2, ?_, ?_⟩
    all_goals rw [path]
    · kernel_rfl
    · exact Or.inl rfl
    · kernel_rfl
    · exact Or.inl rfl
    · kernel_rfl
    · exact Or.inl rfl
    · kernel_rfl
    · refine Or.inr (Or.inr ⟨_, rfl⟩)
    · kernel_rfl
    · exact Or.inr (Or.inl rfl)
    · kernel_rfl
    · refine Or.inr (Or.inr ⟨_, rfl⟩)
    · kernel_rfl
    · exact Or.inr (Or.inl rfl)
    · kernel_rfl
    · refine Or.inr (Or.inr ⟨_, rfl⟩)
  obtain ⟨op, request, node, reference⟩ := source
  exact ⟨op, request, fuel, node, reference, positive⟩

/-- Real captured points retain every metadata field; only the numeric source and heap premises matter. -/
def ReferenceAtPoint (point : Point) (heap : RefHeap) : Prop :=
  ReferenceAt (referencePoint point) heap

/-- The complete reference transfer applies to actual captured source points and their completed-exit views. -/
theorem reference_step_point (view : View) (state : Stores) (point : Point)
    (owned : ReferenceAtPoint point state.refs) :
    ∃ next value, sourceStep view point state = some (next, value) ∧
      HeapAt next.refs ∧ ReferenceAnswer point next.refs value := by
  obtain ⟨op, request, fuel, node, reference, positive⟩ := reference_source owned
  have actualNode : Node.at_ (.eff HostTimeoutSource.program) point.path =
      some (.eff (.perform op request)) := node
  have actualFuel : point.fuel = fuel + 1 := positive
  have code := reference_code_fields point op request fuel actualFuel actualNode reference
  obtain ⟨next, value, step, heap, answer⟩ := reference_step view state (referencePoint point) owned
  refine ⟨next, value, ?_, heap, answer⟩
  unfold sourceStep at step ⊢
  rw [code]
  exact step

/-- The numeric reference instance consumes an exact captured source point at its actual store.
This is local transfer; it supplies no history permission for that point. -/
theorem reference_refTransfer (view : View) (point : Point) (before after : Stores)
    (transfer : StoreExecution.RefTransfer (interpreter view)
      (resolve HostTimeoutSource.program point) before after)
    (heap : HeapAt before.refs) (reference : ReferenceAtPoint point before.refs) : HeapAt after.refs := by
  apply transfer.preserves HeapAt heap
  intro thunk next value current unparked answer
  obtain ⟨expected, returned, step, kept, classified⟩ := reference_step_point view before point reference
  unfold sourceStep at step
  rw [current] at step
  dsimp only at step
  rw [answer] at step
  cases step
  exact kept


/-- The actual primitive producer consumes the current row's captured numeric permission.
This establishes one evaluation's heap result; history must still produce that permission. -/
theorem reference_primitive_heap (machine : Effect4.Program.NativeMachine)
    (fiber : Effect4.Program.SourceScope.SourceFiber) (yielding : Bool) (point : Point)
    (current : fiber.frame.current = resolve HostTimeoutSource.program point)
    (heap : HeapAt machine.state.refs) (reference : ReferenceAtPoint point machine.state.refs) :
    HeapAt (evaluatePrim (interpreter machine.completedExits) machine fiber yielding).machine.state.refs := by
  have transfer := StoreExecution.primitive_refTransfer HostTimeoutSource.program machine.completedExits
    Test.Dogfood.Scenario.Timeout.fetch.table machine fiber yielding
  rw [current] at transfer
  exact reference_refTransfer machine.completedExits point machine.state _ transfer heap reference

end Test.Dogfood.Proofs.HostTimeoutNumberState
