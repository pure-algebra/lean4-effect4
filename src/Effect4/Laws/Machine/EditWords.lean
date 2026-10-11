import Effect4.Laws.Machine.Edits

/-!
# Driver helper words

Concept: reactive-scheduling, R11, the machine part of evaluation-moves.
These equations supply Approximation and the per-edit invariant instances.
They retain the actual helper lookup, store result, and write order.
They prove no payload invariant, progress, or host agreement.
-/

set_option autoImplicit false

namespace Effect4.Machine.Edits

universe u v w
variable {ν σ : Type u} {β : Type v} {ε δ ι α χ : Type u} {St : Type (max u v)}
  {κ φ η : Type (max u v)}

def startWord (parent : RunFiber ν σ β ε δ ι α χ κ φ) (child : FiberId)
    (immediately : Bool) : List (Edit ν σ β ε δ ι α χ St κ φ η) :=
  if immediately then []
  else [.arm parent.id, .emit [RunEvent.scheduledTask parent.id 0 (Task.start child)]]

theorem start_word (m : RunMachine ν σ β ε δ ι α χ St κ φ η)
    (parent : RunFiber ν σ β ε δ ι α χ κ φ) (child : FiberId) (immediately : Bool) :
    (start m parent child immediately).1 = run (startWord parent child immediately) m := by
  cases immediately <;> rfl

def postTaskWord (m : RunMachine ν σ β ε δ ι α χ St κ φ η) (owner : FiberId)
    (priority : Nat) (task : Task ν σ β ε δ ι α κ) : List (Edit ν σ β ε δ ι α χ St κ φ η) :=
  match m.fiber? owner with
  | none => [.halt (Stuck.unknownFiber owner)]
  | some fiber => [.update {fiber with dispatcher := fiber.dispatcher.enqueue priority task},
      .arm owner, .emit [RunEvent.scheduledTask owner priority task]]

theorem postTask_word (m : RunMachine ν σ β ε δ ι α χ St κ φ η) (owner : FiberId)
    (priority : Nat) (task : Task ν σ β ε δ ι α κ) :
    m.postTask owner priority task = run (postTaskWord m owner priority task) m := by
  cases found : m.fiber? owner <;> simp only [RunMachine.postTask, postTaskWord, found] <;> rfl

theorem arm_word (m : RunMachine ν σ β ε δ ι α χ St κ φ η) (owner : FiberId) :
    m.arm owner = run [.arm owner] m := rfl

theorem disarm_word (m : RunMachine ν σ β ε δ ι α χ St κ φ η) (owner : FiberId) :
    m.disarm owner = run [.disarm owner] m := rfl

def drainWord (m : RunMachine ν σ β ε δ ι α χ St κ φ η) :
    List (Owed κ) → List (Edit ν σ β ε δ ι α χ St κ φ η)
  | [] => []
  | owed :: rest =>
    match owed.mode with
    | .now => drainWord m rest
    | .scheduled owner priority =>
      postTaskWord m owner priority (.resume owed.waiter owed.token owed.code) ++
        drainWord (m.postTask owner priority (.resume owed.waiter owed.token owed.code)) rest

theorem drain_word (m : RunMachine ν σ β ε δ ι α χ St κ φ η) (owed : List (Owed κ)) :
    (drainOwed m owed).1 = run (drainWord m owed) m := by
  induction owed generalizing m with
  | nil => rfl
  | cons head rest ih =>
    cases mode : head.mode with
    | now => simpa only [drainOwed, drainWord, mode] using ih m
    | scheduled owner priority =>
      simp only [drainOwed, drainWord, mode, run_append, ← postTask_word]
      exact ih _

/-- Store-work paths compose the actual task-post paths at each prefix. -/
theorem drain_path
    {Edge : RunMachine ν σ β ε δ ι α χ St κ φ η → RunMachine ν σ β ε δ ι α χ St κ φ η →
      Edit ν σ β ε δ ι α χ St κ φ η → Prop}
    (localPath : ∀ held owner priority task, Effect4.Contracts.Path Edge held
      (held.postTask owner priority task) (postTaskWord held owner priority task))
    (m : RunMachine ν σ β ε δ ι α χ St κ φ η) (owed : List (Owed κ)) :
    Effect4.Contracts.Path Edge m (drainOwed m owed).1 (drainWord m owed) := by
  induction owed generalizing m with
  | nil => exact .nil m
  | cons head rest ih =>
    cases mode : head.mode with
    | now => simpa only [drainOwed, drainWord, mode] using ih m
    | scheduled owner priority =>
      simp only [drainOwed, drainWord, mode]
      exact (localPath m owner priority (.resume head.waiter head.token head.code)).append (ih _)

section core
variable [core : FiberCore ν β ε δ ι α κ φ]

def spawnWord (interp : RunInterp ν σ β ε δ ι α χ St κ)
    (m : RunMachine ν σ β ε δ ι α χ St κ φ η) (parent : RunFiber ν σ β ε δ ι α χ κ φ)
    (program : κ) (options : Supervision.ForkOptions) (site : List Nat) :
    List (Edit ν σ β ε δ ι α χ St κ φ η) :=
  let child : FiberId := ⟨m.nextId⟩
  let interruptible := match options.maskMode with
    | .interruptible => true
    | .uninterruptible => false
    | .inherit => core.interruptible parent.frame
  [.appendFiber (RunFiber.make child program interruptible (interp.budgetOf parent.context) parent.context),
    .bumpId, .addFork ⟨child, parent.id, options.daemon, site⟩,
    .emit [.forked parent.id child options.daemon]]

theorem spawn_word (interp : RunInterp ν σ β ε δ ι α χ St κ)
    (m : RunMachine ν σ β ε δ ι α χ St κ φ η) (parent : RunFiber ν σ β ε δ ι α χ κ φ)
    (program : κ) (options : Supervision.ForkOptions) (site : List Nat) :
    (spawn interp m parent program options site).1 = run (spawnWord interp m parent program options site) m := rfl

theorem launch_word (interp : RunInterp ν σ β ε δ ι α χ St κ) (race : Nat)
    (m : RunMachine ν σ β ε δ ι α χ St κ φ η) (host : RunFiber ν σ β ε δ ι α χ κ φ)
    (program : κ) (site : List Nat) :
    (launchEntrant interp race m host program site).1 =
      run (spawnWord interp m host program ⟨true, true, .interruptible⟩ site) m := rfl

def forksWord (interp : RunInterp ν σ β ε δ ι α χ St κ)
    (m : RunMachine ν σ β ε δ ι α χ St κ φ η) (host : RunFiber ν σ β ε δ ι α χ κ φ) :
    List κ → List (Edit ν σ β ε δ ι α χ St κ φ η)
  | [] => []
  | program :: rest =>
    spawnWord interp m host program ⟨true, true, .inherit⟩ [] ++
      forksWord interp (spawn interp m host program ⟨true, true, .inherit⟩ []).1 host rest

theorem forks_word (interp : RunInterp ν σ β ε δ ι α χ St κ)
    (m : RunMachine ν σ β ε δ ι α χ St κ φ η) (host : RunFiber ν σ β ε δ ι α χ κ φ)
    (programs : List κ) :
    (forkFinalizers interp m host programs).1 = run (forksWord interp m host programs) m := by
  induction programs generalizing m with
  | nil => rfl
  | cons program rest ih =>
    change (forkFinalizers interp (spawn interp m host program ⟨true, true, .inherit⟩ []).1 host rest).1 =
      run (spawnWord interp m host program ⟨true, true, .inherit⟩ [] ++ _) m
    rw [run_append, ← spawn_word]
    exact ih _

/-- Parallel finalizer paths compose the actual spawn paths at each prefix. -/
theorem forks_path
    {Edge : RunMachine ν σ β ε δ ι α χ St κ φ η → RunMachine ν σ β ε δ ι α χ St κ φ η →
      Edit ν σ β ε δ ι α χ St κ φ η → Prop}
    (interp : RunInterp ν σ β ε δ ι α χ St κ)
    (host : RunFiber ν σ β ε δ ι α χ κ φ)
    (localPath : ∀ held program, Effect4.Contracts.Path Edge held
      (spawn interp held host program ⟨true, true, .inherit⟩ []).1
      (spawnWord interp held host program ⟨true, true, .inherit⟩ []))
    (m : RunMachine ν σ β ε δ ι α χ St κ φ η) (programs : List κ) :
    Effect4.Contracts.Path Edge m (forkFinalizers interp m host programs).1
      (forksWord interp m host programs) := by
  induction programs generalizing m with
  | nil => exact .nil m
  | cons program rest ih => exact (localPath m program).append (ih _)

def raceWord (m : RunMachine ν σ β ε δ ι α χ St κ φ η)
    (fiber : RunFiber ν σ β ε δ ι α χ κ φ) (entrants : List κ)
    (site : Option (List Nat)) (mode : Supervision.RaceMode) : List (Edit ν σ β ε δ ι α χ St κ φ η) :=
  [.bumpRace, .bumpToken,
    .appendRace ⟨m.nextRace, fiber.id, m.nextToken,
      {Supervision.RaceAllState.initial [] with remaining := entrants.length},
      false, entrants, false, site, mode, none⟩,
    .emit [.raceStarted m.nextRace fiber.id entrants.length]]

theorem race_word (interp : RunInterp ν σ β ε δ ι α χ St κ)
    (m : RunMachine ν σ β ε δ ι α χ St κ φ η) (fiber : RunFiber ν σ β ε δ ι α χ κ φ)
    (yielding : Bool) (entrants : List κ) (site : Option (List Nat)) (mode : Supervision.RaceMode) :
    (beginRace interp m fiber yielding entrants site mode).machine = run (raceWord m fiber entrants site mode) m := rfl

theorem inject_word (m : RunMachine ν σ β ε δ ι α χ St κ φ η)
    (fiber : RunFiber ν σ β ε δ ι α χ κ φ) (yielding : Bool)
    (next : Iter ν σ β ε δ ι α χ St κ φ η) (fired : injectYield m fiber yielding = some next) :
    next.machine = run [.emit [.yieldInjected fiber.id fiber.currentOpCount]] m := by
  unfold injectYield at fired
  split at fired
  · cases fired
    rfl
  · cases fired

def registerWord (m : RunMachine ν σ β ε δ ι α χ St κ φ η) (race : Nat) :
    List (Edit ν σ β ε δ ι α χ St κ φ η) :=
  match m.race? race with
  | none => []
  | some found => [.updateRace {found with registering := true}]

omit core in
theorem register_word (m : RunMachine ν σ β ε δ ι α χ St κ φ η)
    (fiber : RunFiber ν σ β ε δ ι α χ κ φ) (yielding : Bool) (race : Nat) :
    (registerRace m fiber yielding race).machine = run (registerWord m race) m := by
  cases found : m.race? race <;> simp only [registerRace, registerWord, found] <;> rfl

def exitStoreWord (interp : RunInterp ν σ β ε δ ι α χ St κ)
    (fiber : RunFiber ν σ β ε δ ι α χ κ φ) (exit : Exit β ε δ ι α) :
    List (Edit ν σ β ε δ ι α χ St κ φ η) :=
  [.update (fiber.publish exit), .emit [.exited fiber.id exit]] ++
    match fiber.observers with
    | [] => [.update ((fiber.publish exit).cleared interp)]
    | _ :: _ => []

theorem exit_store_word (interp : RunInterp ν σ β ε δ ι α χ St κ)
    (m : RunMachine ν σ β ε δ ι α χ St κ φ η) (fiber : RunFiber ν σ β ε δ ι α χ κ φ)
    (exit : Exit β ε δ ι α) :
    (exitFiber.exitStore interp m fiber exit).1 = run (exitStoreWord interp fiber exit) m := by
  cases found : fiber.observers <;> simp only [exitFiber.exitStore, exitStoreWord, RunFiber.publish, found] <;> rfl

def exitChildrenWord (interp : RunInterp ν σ β ε δ ι α χ St κ)
    (fiber : RunFiber ν σ β ε δ ι α χ κ φ) (exit : Exit β ε δ ι α) :
    List (Edit ν σ β ε δ ι α χ St κ φ η) :=
  [.update {fiber with
      finalizing := some exit
      running := false
      frame := core.answerWith (core.setDeferred fiber.frame false)
        (core.onSuccess (interp.interruptAllCode fiber.children) (interp.restoreName exit))},
    .emit [.childrenInterrupted fiber.id fiber.children]]

theorem exit_children_word (interp : RunInterp ν σ β ε δ ι α χ St κ)
    (m : RunMachine ν σ β ε δ ι α χ St κ φ η) (fiber : RunFiber ν σ β ε δ ι α χ κ φ)
    (exit : Exit β ε δ ι α) :
    (exitFiber.exitInterruptChildren interp m fiber exit).1 = run (exitChildrenWord interp fiber exit) m := rfl

def exitWord (interp : RunInterp ν σ β ε δ ι α χ St κ)
    (m : RunMachine ν σ β ε δ ι α χ St κ φ η) (fiber : RunFiber ν σ β ε δ ι α χ κ φ)
    (exit : Exit β ε δ ι α) : List (Edit ν σ β ε δ ι α χ St κ φ η) :=
  if m.middlewareInstalled && fiber.finalizing.isNone && !fiber.children.isEmpty then
    exitChildrenWord interp fiber exit
  else exitStoreWord interp fiber exit

theorem exit_word (interp : RunInterp ν σ β ε δ ι α χ St κ)
    (m : RunMachine ν σ β ε δ ι α χ St κ φ η) (fiber : RunFiber ν σ β ε δ ι α χ κ φ)
    (exit : Exit β ε δ ι α) : (exitFiber interp m fiber exit).1 = run (exitWord interp m fiber exit) m := by
  unfold exitFiber exitWord
  split
  · exact exit_children_word interp m fiber exit
  · exact exit_store_word interp m fiber exit

def outcomeWord (next : Iter ν σ β ε δ ι α χ St κ φ η) : List (Edit ν σ β ε δ ι α χ St κ φ η) :=
  match next.outcome with
  | .continue_ | .answered | .commands | .finished _ => [.update next.fiber]
  | .parked =>
    if core.deferredInterrupt next.fiber.frame then
      [.update {next.fiber with parked := .notParked, pending := []}]
    else [.update {next.fiber with running := false}]
  | .stuck why => [.update {next.fiber with running := false}, .halt why]

theorem outcome_word (owner : FiberId) (rest : List (Cmd ν σ β ε δ ι α κ))
    (next : Iter ν σ β ε δ ι α χ St κ φ η) :
    (settleOutcome owner rest next).1 = run (outcomeWord next) next.machine := by
  cases found : next.outcome with
  | parked =>
    simp only [settleOutcome, outcomeWord, found]
    split <;> rfl
  | _ => simp only [settleOutcome, outcomeWord, found]; rfl

def countdownWord (m : RunMachine ν σ β ε δ ι α χ St κ φ η)
    (fiber : RunFiber ν σ β ε δ ι α χ κ φ) (targets : List FiberId) :
    List (Edit ν σ β ε δ ι α χ St κ φ η) :=
  [.bumpToken] ++ match countdownWalk {m with nextToken := m.nextToken + 1} targets [] with
    | (_, none) => []
    | (_, some _) => [.emit [.parkedOn fiber.id m.nextToken]]

theorem countdown_word (interp : RunInterp ν σ β ε δ ι α χ St κ)
    (m : RunMachine ν σ β ε δ ι α χ St κ φ η) (fiber : RunFiber ν σ β ε δ ι α χ κ φ)
    (targets : List FiberId) (resume : Resume ν) (failFast : Bool) :
    (countdownParkEdits interp m fiber targets resume failFast).1 = run (countdownWord m fiber targets) m := by
  cases found : countdownWalk {m with nextToken := m.nextToken + 1} targets [] with
  | mk exits target =>
    cases target <;> simp only [countdownParkEdits, countdownWord, found] <;> rfl

omit core in
/-- Every canonical countdown plan write misses the stored fiber table. -/
theorem countdown_misses (m : RunMachine ν σ β ε δ ι α χ St κ φ η)
    (fiber : RunFiber ν σ β ε δ ι α χ κ φ) (targets : List FiberId)
    (edit : Edit ν σ β ε δ ι α χ St κ φ η) (member : edit ∈ countdownWord m fiber targets) :
    edit.missesFibers := by
  simp only [countdownWord] at member
  split at member
  · simp only [List.mem_append, List.mem_singleton, List.not_mem_nil, or_false] at member
    subst edit
    intro impossible; cases impossible
  · simp only [List.mem_append, List.mem_singleton] at member
    rcases member with rfl | rfl <;> (intro impossible; cases impossible)

def linkWord (interp : RunInterp ν σ β ε δ ι α χ St κ)
    (m : RunMachine ν σ β ε δ ι α χ St κ φ η) (mode : Supervision.ScopeMode)
    (scope : Nat) (target : FiberId) (interruptor : Option FiberId) :
    List (Edit ν σ β ε δ ι α χ St κ φ η) :=
  match interp.scopeStatus scope m.state with
  | none => [.halt (.unknownScope scope)]
  | some (some _) =>
    match m.fiber? target with
    | none => [.halt (.unknownFiber target)]
    | some _ => [.emit [.scopeClosedOnLink scope target, .interruptRecorded interruptor target]]
  | some none =>
    match m.fiber? target with
    | none => [.halt (.unknownFiber target)]
    | some fiber =>
      if fiber.exit.isSome then []
      else match interp.scopeLinkFiber mode scope target m.state with
        | none => [.halt (.unknownScope scope)]
        | some (state, key) => [.setState state, .emit [.scopeLinked mode scope key target]]

omit core in
theorem link_plan_word (interp : RunInterp ν σ β ε δ ι α χ St κ)
    (m : RunMachine ν σ β ε δ ι α χ St κ φ η) (mode : Supervision.ScopeMode)
    (scope : Nat) (target : FiberId) (interruptor : Option FiberId) (extra : ReasonAnnotations α) :
    (linkScopeEdits interp m mode scope target interruptor extra).1 =
      run (linkWord interp m mode scope target interruptor) m := by
  cases status : interp.scopeStatus scope m.state with
  | none => simp only [linkScopeEdits, linkWord, status]; rfl
  | some closed =>
    cases closed with
    | some exit =>
      cases found : m.fiber? target <;> simp only [linkScopeEdits, linkWord, status, found] <;> rfl
    | none =>
      cases found : m.fiber? target with
      | none => simp only [linkScopeEdits, linkWord, status, found]; rfl
      | some fiber =>
        simp only [linkScopeEdits, linkWord, status, found]
        split
        · rfl
        · cases linked : interp.scopeLinkFiber mode scope target m.state with
          | none => rfl
          | some pair =>
            cases pair
            rfl

omit core in
/-- Scope-link plans expose the exact store result at the state-write prefix. -/
theorem link_plan_path
    {Edge : RunMachine ν σ β ε δ ι α χ St κ φ η → RunMachine ν σ β ε δ ι α χ St κ φ η →
      Edit ν σ β ε δ ι α χ St κ φ η → Prop}
    (interp : RunInterp ν σ β ε δ ι α χ St κ) (mode : Supervision.ScopeMode)
    (scope : Nat) (target : FiberId) (interruptor : Option FiberId)
    (m : RunMachine ν σ β ε δ ι α χ St κ φ η)
    (written : ∀ state key, interp.scopeLinkFiber mode scope target m.state = some (state, key) →
      Edge m {m with state := state} (.setState state))
    (closed : ∀ m, Edge m (m.emit [.scopeClosedOnLink scope target, .interruptRecorded interruptor target])
      (.emit [.scopeClosedOnLink scope target, .interruptRecorded interruptor target]))
    (linked : ∀ m key, Edge m (m.emit [.scopeLinked mode scope key target]) (.emit [.scopeLinked mode scope key target]))
    (halted : ∀ m why, Edge m (m.halt why) (.halt why))
    (extra : ReasonAnnotations α) :
    Effect4.Contracts.Path Edge m (linkScopeEdits interp m mode scope target interruptor extra).1
      (linkWord interp m mode scope target interruptor) := by
  rw [link_plan_word]
  fun_cases linkWord interp m mode scope target interruptor
  case case1 | case2 | case4 | case6 => exact .cons (halted _ _) (.nil _)
  case case3 => exact .cons (closed _) (.nil _)
  case case5 => exact .nil m
  case case7 =>
    rename_i fiber found live state key result
    exact .cons (written state key result) (.cons (linked _ key) (.nil _))

omit core in
/-- Every canonical scope-link plan write misses the stored fiber table. -/
theorem link_misses (interp : RunInterp ν σ β ε δ ι α χ St κ)
    (m : RunMachine ν σ β ε δ ι α χ St κ φ η) (mode : Supervision.ScopeMode)
    (scope : Nat) (target : FiberId) (interruptor : Option FiberId)
    (edit : Edit ν σ β ε δ ι α χ St κ φ η)
    (member : edit ∈ linkWord interp m mode scope target interruptor) : edit.missesFibers := by
  unfold linkWord at member
  repeat' split at member
  all_goals simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  all_goals rcases member with rfl | rfl
  all_goals (intro impossible; cases impossible)

end core

section messages
variable [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α]
  [FiberCore ν β ε δ ι α κ φ]

def interruptWord (interp : RunInterp ν σ β ε δ ι α χ St κ)
    (who : FiberId) (extra : ReasonAnnotations α) (target : FiberId)
    (m : RunMachine ν σ β ε δ ι α χ St κ φ η) : List (Edit ν σ β ε δ ι α χ St κ φ η) :=
  match m.fiber? target with
  | none => []
  | some fiber => [.update (interruptRecord interp (some who) extra fiber).1,
      .emit [.interruptRecorded (some who) target]]

def interruptWords (interp : RunInterp ν σ β ε δ ι α χ St κ)
    (who : FiberId) (extra : ReasonAnnotations α) : List FiberId →
    RunMachine ν σ β ε δ ι α χ St κ φ η × List (Cmd ν σ β ε δ ι α κ) →
    List (Edit ν σ β ε δ ι α χ St κ φ η)
  | [], _ => []
  | target :: rest, acc => interruptWord interp who extra target acc.1 ++
      interruptWords interp who extra rest (interruptEach interp who extra [target] acc)

theorem interrupts_word (interp : RunInterp ν σ β ε δ ι α χ St κ)
    (who : FiberId) (extra : ReasonAnnotations α) (targets : List FiberId)
    (acc : RunMachine ν σ β ε δ ι α χ St κ φ η × List (Cmd ν σ β ε δ ι α κ)) :
    (interruptEach interp who extra targets acc).1 = run (interruptWords interp who extra targets acc) acc.1 := by
  induction targets generalizing acc with
  | nil => rfl
  | cons target rest ih =>
    rw [interruptEach, List.foldl_cons]
    simp only [interruptWords, run_append]
    cases found : acc.1.fiber? target with
    | none =>
      simp only [found, interruptWord, interruptEach, List.foldl_cons, List.foldl_nil]
      exact ih acc
    | some fiber =>
      simp only [found, interruptWord, interruptEach, List.foldl_cons, List.foldl_nil]
      exact ih _

/-- One addressed interrupt path retains its actual lookup and event order. -/
theorem interrupt_path
    {Edge : RunMachine ν σ β ε δ ι α χ St κ φ η → RunMachine ν σ β ε δ ι α χ St κ φ η →
      Edit ν σ β ε δ ι α χ St κ φ η → Prop}
    (interp : RunInterp ν σ β ε δ ι α χ St κ) (who : FiberId) (extra : ReasonAnnotations α)
    (update : ∀ m target old, m.fiber? target = some old →
      Edge m (m.update (interruptRecord interp (some who) extra old).1)
        (.update (interruptRecord interp (some who) extra old).1))
    (recorded : ∀ m target, Edge m (m.emit [.interruptRecorded (some who) target])
      (.emit [.interruptRecorded (some who) target]))
    (target : FiberId)
    (acc : RunMachine ν σ β ε δ ι α χ St κ φ η × List (Cmd ν σ β ε δ ι α κ)) :
    Effect4.Contracts.Path Edge acc.1 (interruptEach interp who extra [target] acc).1
      (interruptWord interp who extra target acc.1) := by
  rw [interrupts_word]
  simp only [interruptWords, List.append_nil]
  cases found : acc.1.fiber? target with
  | none => simp only [interruptWord, found]; exact .nil acc.1
  | some old =>
    simp only [interruptWord, found]
    exact .cons (update acc.1 target old found) (.cons (recorded _ target) (.nil _))

/-- Interrupt-list paths compose at the actual lookup states and command prefixes. -/
theorem interrupts_path
    {Edge : RunMachine ν σ β ε δ ι α χ St κ φ η → RunMachine ν σ β ε δ ι α χ St κ φ η →
      Edit ν σ β ε δ ι α χ St κ φ η → Prop}
    (interp : RunInterp ν σ β ε δ ι α χ St κ) (who : FiberId) (extra : ReasonAnnotations α)
    (localPath : ∀ target acc, Effect4.Contracts.Path Edge acc.1
      (interruptEach interp who extra [target] acc).1 (interruptWord interp who extra target acc.1))
    (targets : List FiberId)
    (acc : RunMachine ν σ β ε δ ι α χ St κ φ η × List (Cmd ν σ β ε δ ι α κ)) :
    Effect4.Contracts.Path Edge acc.1 (interruptEach interp who extra targets acc).1
      (interruptWords interp who extra targets acc) := by
  rw [interrupts_word]
  induction targets generalizing acc with
  | nil => exact .nil acc.1
  | cons target rest ih =>
    rw [interruptWords, run_append]
    have firstPath := localPath target acc
    have firstEq := interrupts_word interp who extra [target] acc
    simp only [interruptWords, List.append_nil] at firstEq
    rw [← firstEq]
    exact firstPath.append (ih _)

theorem interrupt_choice_word (interp : RunInterp ν σ β ε δ ι α χ St κ)
    (who : FiberId) (extra : ReasonAnnotations α) (targets : List FiberId)
    (acc : RunMachine ν σ β ε δ ι α χ St κ φ η × List (Cmd ν σ β ε δ ι α κ))
    (chosen : Bool) :
    run (if chosen then interruptWords interp who extra targets acc else []) acc.1 =
      (if chosen then interruptEach interp who extra targets acc else acc).1 := by
  cases chosen with
  | false => rfl
  | true => exact (interrupts_word interp who extra targets acc).symm

def eagerLinkWord (interp : RunInterp ν σ β ε δ ι α χ St κ)
    (m : RunMachine ν σ β ε δ ι α χ St κ φ η) (mode : Supervision.ScopeMode)
    (scope : Nat) (target : FiberId) (interruptor : Option FiberId) (extra : ReasonAnnotations α) :
    List (Edit ν σ β ε δ ι α χ St κ φ η) :=
  let plan := linkScopeEdits interp m mode scope target interruptor extra
  linkWord interp m mode scope target interruptor ++ fiberWords plan.2 plan.1

theorem eager_link_word (interp : RunInterp ν σ β ε δ ι α χ St κ)
    (m : RunMachine ν σ β ε δ ι α χ St κ φ η) (mode : Supervision.ScopeMode)
    (scope : Nat) (target : FiberId) (interruptor : Option FiberId) (extra : ReasonAnnotations α) :
    (linkScope interp m mode scope target interruptor extra).1 =
      run (eagerLinkWord interp m mode scope target interruptor extra) m := by
  simp only [linkScope, eagerLinkWord, run_append, fiber_words]
  rw [← link_plan_word interp m mode scope target interruptor extra]

def installedWord (next : Iter ν σ β ε δ ι α χ St κ φ η) :
    List (Edit ν σ β ε δ ι α χ St κ φ η) :=
  [.update next.fiber] ++ fiberWords next.edits (next.machine.update next.fiber)

theorem installed_word (next : Iter ν σ β ε δ ι α χ St κ φ η) :
    run (installedWord next) next.machine =
      (applyFiberEdits next.edits (next.machine.update next.fiber)).1 := by
  rw [installedWord, run_append, fiber_words]
  rfl

def settleWord (next : Iter ν σ β ε δ ι α χ St κ φ η) :
    List (Edit ν σ β ε δ ι α χ St κ φ η) :=
  match next.edits with
  | [] => outcomeWord next
  | _ :: _ =>
    let changed := applyFiberEdits next.edits (next.machine.update next.fiber)
    installedWord next ++ match changed.1.fiber? next.fiber.id with
      | none => [.halt (.unknownFiber next.fiber.id)]
      | some owner => outcomeWord {next with
          machine := changed.1
          fiber := owner
          nested := changed.2 ++ next.nested
          edits := []}

/-- Settlement installs the local result, interprets addressed edits, rereads its owner,
and applies the disposition. The raw missing-owner branch remains a halt. -/
theorem settle_word (owner : FiberId) (rest : List (Cmd ν σ β ε δ ι α κ))
    (next : Iter ν σ β ε δ ι α χ St κ φ η) :
    (settle owner rest next).1 = run (settleWord next) next.machine := by
  cases edits : next.edits with
  | nil => simp only [settle, settleWord, edits]; exact outcome_word owner rest next
  | cons edit tail =>
    simp only [settle, settleWord, edits, run_append, installed_word]
    cases found : (applyFiberEdits (edit :: tail) (next.machine.update next.fiber)).1.fiber? next.fiber.id with
    | none => rfl
    | some fiber => exact outcome_word owner rest _

theorem fiberWord_settlement (message : FiberEdit ε δ ι α)
    (m : RunMachine ν σ β ε δ ι α χ St κ φ η)
    (edit : Edit ν σ β ε δ ι α χ St κ φ η) (member : edit ∈ fiberWord message m) :
    edit.settlementWrite := by
  cases message with
  | observe target observer =>
    simp only [fiberWord, List.mem_singleton] at member
    subst edit
    exact True.intro
  | dropToken token =>
    simp only [fiberWord, List.mem_singleton] at member
    subst edit
    exact True.intro
  | interrupt target cause =>
    cases found : m.fiber? target with
    | none => simp only [fiberWord, found, List.not_mem_nil] at member
    | some fiber =>
      simp only [fiberWord, found, List.mem_singleton] at member
      subst edit
      exact True.intro

theorem fiberWords_settlement (messages : List (FiberEdit ε δ ι α))
    (m : RunMachine ν σ β ε δ ι α χ St κ φ η)
    (edit : Edit ν σ β ε δ ι α χ St κ φ η) (member : edit ∈ fiberWords messages m) :
    edit.settlementWrite := by
  induction messages generalizing m with
  | nil => simp only [fiberWords, List.not_mem_nil] at member
  | cons message rest ih =>
    simp only [fiberWords, List.mem_append] at member
    rcases member with firstPart | later
    · exact fiberWord_settlement message m edit firstPart
    · exact ih _ later

omit [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α] in
theorem outcome_settlement (next : Iter ν σ β ε δ ι α χ St κ φ η)
    (edit : Edit ν σ β ε δ ι α χ St κ φ η) (member : edit ∈ outcomeWord next) :
    edit.settlementWrite := by
  cases found : next.outcome with
  | parked =>
    simp only [outcomeWord, found] at member
    split at member <;> simp only [List.mem_singleton] at member <;>
      subst edit <;> exact True.intro
  | stuck why =>
    simp only [outcomeWord, found, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> exact True.intro
  | _ =>
    simp only [outcomeWord, found, List.mem_singleton] at member
    subst edit
    exact True.intro

/-- Every settlement write is a fiber replacement, halt, observer append, or token drop. -/
theorem settle_settlement (next : Iter ν σ β ε δ ι α χ St κ φ η)
    (edit : Edit ν σ β ε δ ι α χ St κ φ η) (member : edit ∈ settleWord next) :
    edit.settlementWrite := by
  unfold settleWord at member
  cases messages : next.edits with
  | nil =>
    simp only [messages] at member
    exact outcome_settlement next edit member
  | cons message rest =>
    simp only [messages, List.mem_append] at member
    rcases member with installed | disposition
    · simp only [installedWord, List.mem_append, List.mem_singleton] at installed
      rcases installed with rfl | addressed
      · exact True.intro
      · exact fiberWords_settlement _ _ edit addressed
    · split at disposition
      · simp only [List.mem_singleton] at disposition
        subst edit
        exact True.intro
      · exact outcome_settlement _ edit disposition

/-- A projection kept by the four settlement writes is kept by actual settlement.
SettleQueue and FiberSumMessages consume this frame rule. -/
theorem settle_keeps {P : Sort w}
    (projection : RunMachine ν σ β ε δ ι α χ St κ φ η → P)
    (update : ∀ fiber, Keeps projection (fun held => held.update fiber))
    (halt : ∀ why, Keeps projection (fun held => held.halt why))
    (observe : ∀ target observer, Keeps projection (Edit.observe target observer).apply)
    (drop : ∀ token, Keeps projection (Edit.dropToken token).apply)
    (owner : FiberId) (rest : List (Cmd ν σ β ε δ ι α κ))
    (next : Iter ν σ β ε δ ι α χ St κ φ η) :
    projection (settle owner rest next).1 = projection next.machine := by
  rw [settle_word]
  apply run_keeps projection (settleWord next)
  intro edit member
  have allowed := settle_settlement next edit member
  cases edit with
  | update fiber => exact update fiber
  | halt why => exact halt why
  | observe target observer => exact observe target observer
  | dropToken token => exact drop token
  | _ => exact False.elim allowed

end messages
end Effect4.Machine.Edits
