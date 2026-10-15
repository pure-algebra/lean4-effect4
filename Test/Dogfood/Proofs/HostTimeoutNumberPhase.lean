import Test.Dogfood.Proofs.HostTimeoutNumberState

/-!
Concepts: scope-lifetime-finalization R11 and translation-simulation R10.
Question: the shared numeric phase serves Timeout.cleanup_keeps and Timeout.retries_declared.
Consumer: the numeric command assertion, including interruption during an unfinished form.
Reach: the actual three reference cells and the source's count, cleanup and form writes.
Limit: these local phase laws supply no command or history permission for a writer.
The cleanup order does not require the completed-form log to have finished publishing.
-/
set_option autoImplicit false
set_option maxRecDepth 100000
namespace Test.Dogfood.Proofs.HostTimeoutNumberPhase
open Effect4 Effect4.Machine Effect4.Program
open HostTimeoutNumberSteps HostTimeoutNumberLedger HostTimeoutNumberState
open Test.Dogfood.Scenario.Timeout

/-- A numeric phase separates committed cleanup order from the completed form's publication. -/
structure Phase where
  count : Nat
  cleanups : List Val
  completed : List Val
  exits : List ExitV
  cleanupsAt : CleanupsAt cleanups
  formsAt : FormsAt completed exits
  cleanupLower : cleanups.length ≤ count
  cleanupUpper : count ≤ cleanups.length + 1
  formUpper : count ≤ exits.length + 1
  bound : count ≤ 4

/-- The numeric phase names the existing three-cell reference heap. -/
def Phase.heap (phase : Phase) : RefHeap :=
  numberHeap phase.count phase.cleanups phase.completed

/-- Allocation establishes the empty numeric phase. -/
def initial : Phase :=
  ⟨0, [], [], [], .nil, .nil, by decide, by decide, by decide, by decide⟩

/-- The stronger local assertion forgets only its comparison between the two log lengths. -/
def ofNumbers (count : Nat) (cleanups completed : List Val) (exits : List ExitV)
    (numbers : Numbers count cleanups completed exits) : Phase :=
  ⟨count, cleanups, completed, exits, numbers.cleanupsAt, numbers.formsAt,
    numbers.cleanupLower, numbers.cleanupUpper, numbers.formUpper, numbers.bound⟩

/-- A counted attempt enters after the prior cleanup, while the source cursor bounds the committed count. -/
def Phase.counted (phase : Phase) (n : Fin 4)
    (cleanupComplete : phase.cleanups.length = phase.count)
    (formsReady : phase.count ≤ phase.exits.length) (cursor : phase.count ≤ n.val) : Phase :=
  ⟨phase.count + 1, phase.cleanups, phase.completed, phase.exits,
    phase.cleanupsAt, phase.formsAt, by omega, by omega, by omega, by have h := n.isLt; omega⟩

/-- The stronger local entry is an instance of the general phase count transition. -/
def Phase.enter (phase : Phase) (n : Fin 4)
    (cleanupComplete : phase.cleanups.length = phase.count)
    (formComplete : phase.exits.length = phase.count) (cursor : phase.count = n.val) : Phase :=
  phase.counted n cleanupComplete (Nat.le_of_eq formComplete.symm) (Nat.le_of_eq cursor)

/-- Cleanup publishes the active attempt's number and retains its committed count. -/
def Phase.cleanup (phase : Phase) (own : phase.count = phase.cleanups.length + 1)
    (interrupted : Bool) : Phase :=
  ⟨phase.count, phase.cleanups ++ [.list [.nat phase.count, .bool interrupted]],
    phase.completed, phase.exits,
    by rw [own]; exact .append phase.cleanupsAt interrupted,
    phase.formsAt,
    by simp only [List.length_append, List.length_cons, List.length_nil, Nat.zero_add]; omega,
    by simp only [List.length_append, List.length_cons, List.length_nil, Nat.zero_add]; omega,
    phase.formUpper, phase.bound⟩

/-- Equal actual reference heaps retain the count and both stored logs, without identifying ghost exits. -/
theorem Phase.heap_fields (before after : Phase) (same : before.heap = after.heap) :
    before.count = after.count ∧ before.cleanups = after.cleanups ∧ before.completed = after.completed := by
  have counts := congrArg (fun heap : RefHeap => heap[0]?) same
  have cleanups := congrArg (fun heap : RefHeap => heap[1]?) same
  have forms := congrArg (fun heap : RefHeap => heap[2]?) same
  change some (Val.nat before.count) = some (.nat after.count) at counts
  change some (Val.list before.cleanups) = some (.list after.cleanups) at cleanups
  change some (Val.list before.completed) = some (.list after.completed) at forms
  exact ⟨Store.Val.nat.inj (Option.some.inj counts), Store.Val.list.inj (Option.some.inj cleanups),
    Store.Val.list.inj (Option.some.inj forms)⟩

/-- The actual cleanup operation depends only on the same count and stored logs. -/
theorem Phase.cleanup_heap_congr (before after : Phase)
    (first : before.count = before.cleanups.length + 1) (last : after.count = after.cleanups.length + 1)
    (interrupted : Bool) (same : before.heap = after.heap) :
    (before.cleanup first interrupted).heap = (after.cleanup last interrupted).heap := by
  obtain ⟨count, cleanups, completed⟩ := Phase.heap_fields before after same
  change numberHeap before.count (before.cleanups ++ [.list [.nat before.count, .bool interrupted]]) before.completed =
    numberHeap after.count (after.cleanups ++ [.list [.nat after.count, .bool interrupted]]) after.completed
  rw [count, cleanups, completed]

/-- Form publication changes neither the cleanup log nor the committed count. -/
def Phase.form (phase : Phase) (seen : Nat) (exit : ExitV) : Phase :=
  ⟨phase.count, phase.cleanups, phase.completed ++ [.list [.nat seen, reifyExitVal exit]],
    phase.exits ++ [exit], phase.cleanupsAt, forms_append phase.formsAt seen exit,
    phase.cleanupLower, phase.cleanupUpper,
    by have h := phase.formUpper
       simp only [List.length_append, List.length_cons, List.length_nil, Nat.zero_add]; omega,
    phase.bound⟩

/-- The cleanup reader consumes the phase without assuming a completed form. -/
theorem Phase.cleanup_observation (phase : Phase) (run : Run)
    (heap : run.machine.state.refs = phase.heap) : (observe run).cleanupKeeps = true := by
  have counted : (observe run).attempts = phase.count := by
    change (match run.machine.state.refs[0]? with | some (Val.nat n) => n | _ => 0) = phase.count
    rw [heap]
    rfl
  have logged : (observe run).cleanups = phase.cleanups := by
    change (match run.machine.state.refs[1]? with | some (Val.list entries) => entries | _ => []) = phase.cleanups
    rw [heap]
    rfl
  exact HostTimeoutNumberLedger.cleanup_observation (observe run)
    (logged ▸ phase.cleanupsAt)
    (by rw [logged, counted]; exact phase.cleanupLower)
    (by rw [logged, counted]; exact phase.cleanupUpper)

/-- The retry reader consumes the declared completed predecessor prefix at the same phase. -/
theorem Phase.retry_observation (phase : Phase) (run : Run)
    (heap : run.machine.state.refs = phase.heap) (declared : Declared phase.count phase.exits) :
    (observe run).retriesDeclared = true := by
  have counted : (observe run).attempts = phase.count := by
    change (match run.machine.state.refs[0]? with | some (Val.nat n) => n | _ => 0) = phase.count
    rw [heap]
    rfl
  have stored : Test.Dogfood.Scenario.cell run 2 = some (.list phase.completed) := by
    change run.machine.state.refs[2]? = some (.list phase.completed)
    rw [heap]
    rfl
  have decoded : (observe run).forms.map (·.exit) = phase.exits :=
    (completed_exits run phase.completed stored).trans (form_exits phase.formsAt)
  exact HostTimeoutNumberLedger.retry_observation (observe run) phase.exits decoded
    (by rw [counted]; exact declared)
    (by rw [counted]; exact phase.formUpper)
    (by rw [counted]; exact phase.bound)

/-- Cleanup leaves the declared predecessor prefix unchanged. -/
theorem Phase.cleanup_declared (phase : Phase)
    (own : phase.count = phase.cleanups.length + 1) (interrupted : Bool)
    (declared : Declared phase.count phase.exits) :
    Declared (phase.cleanup own interrupted).count (phase.cleanup own interrupted).exits := declared

/-- Form publication retains every declared predecessor already consumed by the loop. -/
theorem Phase.form_declared (phase : Phase) (seen : Nat) (exit : ExitV)
    (declared : Declared phase.count phase.exits) :
    Declared (phase.form seen exit).count (phase.form seen exit).exits :=
  completed_declared phase.count phase.exits exit declared phase.formUpper

/-- A new count consumes only the declared predecessor prefix, even when earlier uncounted forms exist. -/
theorem Phase.counted_declared (phase : Phase) (n : Fin 4)
    (cleanupComplete : phase.cleanups.length = phase.count)
    (formsReady : phase.count ≤ phase.exits.length) (cursor : phase.count ≤ n.val)
    (declared : phase.exits.all exitRetries = true) :
    Declared (phase.counted n cleanupComplete formsReady cursor).count
      (phase.counted n cleanupComplete formsReady cursor).exits := by
  change (phase.exits.take (phase.count + 1 - 1)).all exitRetries = true
  rw [List.all_eq_true] at declared ⊢
  intro exit member
  exact declared exit (List.mem_of_mem_take member)

/-- The next attempt consumes the actual complete declared predecessor log. -/
theorem Phase.enter_declared (phase : Phase) (n : Fin 4)
    (cleanupComplete : phase.cleanups.length = phase.count)
    (formComplete : phase.exits.length = phase.count) (cursor : phase.count = n.val)
    (declared : phase.exits.all exitRetries = true) :
    Declared (phase.enter n cleanupComplete formComplete cursor).count
      (phase.enter n cleanupComplete formComplete cursor).exits :=
  count_declared phase.count phase.exits formComplete declared

/-- The actual cleanup write installs exactly the phase whose number it just read. -/
theorem Phase.cleanup_source (phase : Phase) (view : HostTimeoutFlow.View) (state : Stores)
    (fuel delay : Nat) (n : Fin 4) (error : Val) (exit : ExitV)
    (own : phase.count = phase.cleanups.length + 1) :
    sourceStep view
      (sourcePoint [1,1,1,0,0,1,0,0,0,0,0,0,1,1,0]
        (HostTimeoutSlots.ready (Val.cell ⟨0⟩) (Val.cell ⟨1⟩) (Val.cell ⟨2⟩) n delay error ++
          [reifyExitVal exit, .nat phase.count]) fuel)
      {state with refs := phase.heap} =
      some ({state with refs := (phase.cleanup own (interruptionFlag exit)).heap}, .unit) :=
  cleanup_note view state fuel phase.count phase.count delay n error exit phase.cleanups phase.completed

/-- The actual completed-form write changes neither the count nor the cleanup phase. -/
theorem Phase.form_source (phase : Phase) (view : HostTimeoutFlow.View) (state : Stores)
    (fuel delay : Nat) (n : Fin 4) (error : Val) (exit : ExitV) :
    sourceStep view
      (sourcePoint [1,1,1,0,0,1,0,0,1,1]
        (HostTimeoutSlots.ready (Val.cell ⟨0⟩) (Val.cell ⟨1⟩) (Val.cell ⟨2⟩) n delay error ++
          [reifyExitVal exit, .nat phase.count]) fuel)
      {state with refs := phase.heap} =
      some ({state with refs := (phase.form phase.count exit).heap}, .unit) :=
  completed_note view state fuel phase.count phase.count delay n error exit phase.cleanups phase.completed

end Test.Dogfood.Proofs.HostTimeoutNumberPhase
