import Effect4.Laws.Program.ReleaseCustody.NativeAccounting
import Effect4.Laws.Program.ReleaseCustody.ObserverDebit

/-!
Concept: scope-lifetime-finalization R11.
Question: actual non-parallel native fiber actions feed Execution.history and Workers.releases_step.
Reach: actual fork, await, mask, scope-close and administrative actions under source ownership.
Limit: parallel cleanup requires the discharged Workers sequential-source restriction.
Unlock: evaluator aggregate composes scalar actions with checked frame debit and actual settle.
-/
set_option autoImplicit false
namespace Effect4.Program.ReleaseCustody.NativeActionDebit
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Guard
open Effect4.Program.ReleaseCustody Effect4.Program.ReleaseCustody.Control
open Effect4.Program.ReleaseCustody.Sequencing
abbrev Interp := NativeStacks.Interp

/-- The spawned child receives at most the program reservation outside the selected owner.
Consumer: actual fork action debit. -/
theorem spawn_outside (q : List Nat) (interp : Interp) (m : NativeMachine) (fiber : Control.Fiber)
    (program : NCode) (options : Supervision.ForkOptions) (site : List Nat) :
    outsideCredits q fiber.id (spawn interp m fiber program options site).1 ≤
      outsideCredits q fiber.id m + currentCredits q program := by
  unfold spawn outsideCredits
  simp only [RunMachine.emit, List.map_append, List.sum_append, List.map_cons,
    List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
  unfold outsideFiber
  simp only [fiberCredits, RunFiber.make, FrameFiber.start, stackCredits,
    Dispatcher.empty, List.map_nil, List.sum_nil, Nat.add_zero]
  by_cases same : (⟨m.nextId⟩ : FiberId) = fiber.id
  all_goals simp only [same, if_true, if_false]
  all_goals omega

/-- Scheduling a child adds only a zero-credit start task to the caller.
Consumer: actual immediate and deferred fork actions. -/
theorem start_credit (q : List Nat) (m : NativeMachine) (fiber : Control.Fiber)
    (child : FiberId) (immediately : Bool) :
    outsideCredits q fiber.id (start m fiber child immediately).1 = outsideCredits q fiber.id m ∧
    fiberCredits q (start m fiber child immediately).2.1 = fiberCredits q fiber ∧
    ((start m fiber child immediately).2.2.map (commandCredits q)).sum = 0 := by
  cases immediately with
  | true => exact ⟨rfl, rfl, rfl⟩
  | false =>
    refine ⟨rfl, ?_, rfl⟩
    simp only [start, Bool.false_eq_true, if_false, fiberCredits, Dispatcher.enqueue,
      CommandDebit.insert_zero q 0 (.start child) rfl]

/-- Replacing only active code spends at most that code's existing reservation.
Consumer: administrative actions and missing-scope fork responses. -/
theorem replace_current (q : List Nat) (m : NativeMachine) (fiber : Control.Fiber)
    (yielding : Bool) (code : NCode) (outcome : Outcome EffName EffThunk Val Err Defect FiberId Ann)
    (held : NoAdd fiber.frame.stack)
    (carried : currentCredits q code ≤ currentCredits q fiber.frame.current) :
    IterDebit q m fiber ⟨m, {fiber with frame := {fiber.frame with current := code}}, yielding, outcome, []⟩ := by
  unfold IterDebit
  simp only [List.map_nil, List.sum_nil, Nat.add_zero, fiberCredits]
  rw [noAdd_full q code _ held, noAdd_full q fiber.frame.current _ held]
  omega

/-- A native fork transfers its program reservation into the new child exactly once.
Consumer: actual source and stored fork actions in the evaluator census. -/
theorem fork (q : List Nat) (interp : Interp) (m : NativeMachine) (fiber : Control.Fiber)
    (yielding : Bool) (program : NCode) (options : Supervision.ForkOptions) (site : List Nat)
    (held : NoAdd fiber.frame.stack)
    (carried : currentCredits q program ≤ currentCredits q fiber.frame.current) :
    IterDebit q m fiber (evaluatePrim.withFiber interp m fiber yielding (.fork program options site)) := by
  cases options with
  | mk daemon immediately mode =>
    cases daemon <;> cases immediately
    all_goals by_cases same : (⟨m.nextId⟩ : FiberId) = fiber.id
    all_goals
      unfold IterDebit outsideCredits outsideFiber fiberCredits
      dsimp only [evaluatePrim.withFiber, spawn, start, RunMachine.emit, RunMachine.arm,
        RunFiber.make, FrameFiber.start, Dispatcher.empty, currentCredits]
      simp only [List.isEmpty_cons, Bool.false_eq_true, if_false, if_true]
      rw [noAdd_full q (.success _) _ held, noAdd_full q fiber.frame.current _ held]
      simp only [List.countP_append, List.countP_cons, ReleaseTrace.releaseAt,
        ReleaseTrace.registeredAt, List.countP_nil, Bool.false_eq_true, if_false,
        List.map_append, List.sum_append, List.map_cons, List.map_nil,
        List.sum_cons, List.sum_nil, commandCredits, Nat.add_zero, Nat.zero_add,
        same, if_true, FrameFiber.start, stackCredits, Dispatcher.enqueue,
        CommandDebit.insert_zero q 0 (.start _) rfl]
      omega

/-- A scope-linked fork pays the same child reservation and adds only a zero-credit link command.
Consumer: actual Workers scoped forks in the evaluator census. -/
theorem forkIn (q : List Nat) (interp : Interp) (m : NativeMachine) (fiber : Control.Fiber)
    (yielding : Bool) (program : NCode) (options : Supervision.ForkOptions) (scope : Nat) (site : List Nat)
    (held : NoAdd fiber.frame.stack)
    (carried : currentCredits q program ≤ currentCredits q fiber.frame.current) :
    IterDebit q m fiber (evaluatePrim.withFiber interp m fiber yielding (.forkIn program options scope site)) := by
  have debit := fork q interp m fiber yielding program {options with daemon := true} site held carried
  have machine : (evaluatePrim.withFiber interp m fiber yielding (.forkIn program options scope site)).machine =
      (evaluatePrim.withFiber interp m fiber yielding (.fork program {options with daemon := true} site)).machine := rfl
  have returned : (evaluatePrim.withFiber interp m fiber yielding (.forkIn program options scope site)).fiber =
      (evaluatePrim.withFiber interp m fiber yielding (.fork program {options with daemon := true} site)).fiber := rfl
  have zero : ((evaluatePrim.withFiber interp m fiber yielding (.forkIn program options scope site)).nested.map
      (commandCredits q)).sum = 0 := by
    cases immediate : options.startImmediately <;>
      simp only [evaluatePrim.withFiber, start, immediate, Bool.false_eq_true,
        if_false, if_true, List.map_append, List.map_cons, List.map_nil,
        List.sum_append, List.sum_cons, List.sum_nil, commandCredits, Nat.add_zero]
  have daemonZero : ((evaluatePrim.withFiber interp m fiber yielding (.fork program {options with daemon := true} site)).nested.map
      (commandCredits q)).sum = 0 := by
    cases immediate : options.startImmediately <;>
      simp only [evaluatePrim.withFiber, start, Bool.false_eq_true,
        if_false, if_true, List.map_append, List.map_cons, List.map_nil,
        List.sum_append, List.sum_cons, List.sum_nil, commandCredits, Nat.add_zero]
  unfold IterDebit at debit ⊢
  rw [machine, returned, zero]
  rw [daemonZero] at debit
  exact debit

/-- Ambient-scope forks either transfer into their child or retain a failed caller.
Consumer: the actual non-parallel action evaluator census. -/
theorem forkScoped (q : List Nat) (interp : Interp) (m : NativeMachine) (fiber : Control.Fiber)
    (yielding : Bool) (program : NCode) (options : Supervision.ForkOptions) (site : List Nat)
    (held : NoAdd fiber.frame.stack)
    (carried : currentCredits q program ≤ currentCredits q fiber.frame.current) :
    IterDebit q m fiber (evaluatePrim.withFiber interp m fiber yielding (.forkScoped program options site)) := by
  cases foundScope : interp.ambientScope fiber.context with
  | some scope =>
    simpa only [evaluatePrim.withFiber, foundScope] using
      forkIn q interp m fiber yielding program options scope site held carried
  | none =>
    simp only [evaluatePrim.withFiber, foundScope]
    exact replace_current q m fiber yielding (.failure (.die interp.missingScope)) .continue_ held (Nat.zero_le _)

/-- State-first scope close transfers stored custody into its returned active program.
Consumer: the actual scope-close action in the native evaluator census. -/
theorem closeScope (q : List Nat) (root : NativeEff) (table : RowTable)
    (m : NativeMachine) (fiber : Control.Fiber) (yielding : Bool) (scope : Nat) (exit : ExitV)
    (held : NoAdd fiber.frame.stack) (unique : (m.state.scopes.entries.map ScopeEntry.key).Nodup) :
    IterDebit q m fiber (evaluatePrim.withFiber (interpAt root m.completedExits table) m fiber yielding (.closeScope scope exit)) := by
  cases step : storesCloseScope scope exit fiber.frame.interruptible m.state with
  | none =>
    have close : (interpAt root m.completedExits table).closeScope scope exit fiber.frame.interruptible fiber.id m.state = none := by
      change (storesCloseScope scope exit fiber.frame.interruptible m.state).map
        (fun result => (result.1, embed result.2)) = _
      rw [step]
      rfl
    simp only [evaluatePrim.withFiber, close]
    unfold IterDebit
    simp only [List.map_nil, List.sum_nil, Nat.add_zero]
    exact Nat.le_refl _
  | some next =>
    obtain ⟨state, program⟩ := next
    have transfer := ScopeTransfer.close q scope exit fiber.frame.interruptible unique step
    have close : (interpAt root m.completedExits table).closeScope scope exit fiber.frame.interruptible fiber.id m.state =
        some (state, embed program) := by
      change (storesCloseScope scope exit fiber.frame.interruptible m.state).map
        (fun result => (result.1, embed result.2)) = _
      rw [step]
      rfl
    simp only [evaluatePrim.withFiber, close]
    unfold IterDebit outsideCredits fiberCredits
    simp only [List.map_nil, List.sum_nil, Nat.add_zero]
    rw [noAdd_full q (embed program) _ held, noAdd_full q fiber.frame.current _ held]
    unfold ScopeTransfer.storedCredits at transfer
    omega

/-- A race transfers all entrant reservations into the existing race pool.
Consumer: the two actual race modes in the evaluator census. -/
theorem race (q : List Nat) (root : NativeEff) (table : RowTable) (m : NativeMachine)
    (fiber : Control.Fiber) (yielding : Bool) (entrants : List NCode) (site : Option (List Nat))
    (mode : Supervision.RaceMode) (held : NoAdd fiber.frame.stack)
    (carried : (entrants.map (currentCredits q)).sum ≤ currentCredits q fiber.frame.current) :
    IterDebit q m fiber (beginRace (interpAt root m.completedExits table) m fiber yielding entrants site mode) := by
  unfold IterDebit beginRace outsideCredits fiberCredits
  dsimp only [RunMachine.emit]
  simp only [List.isEmpty_cons, Bool.false_eq_true, if_false, List.countP_append,
    List.countP_cons, List.countP_nil, ReleaseTrace.releaseAt, ReleaseTrace.registeredAt,
    List.map_append, List.sum_append, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, Nat.add_zero]
  have answer : currentCredits q ((interpAt root m.completedExits table).parkCode (.race m.nextRace)) = 0 := rfl
  rw [noAdd_full q _ _ held, noAdd_full q fiber.frame.current _ held, answer]
  omega

/-- Masking preserves the residual stack reservation and selects at most the body reservation.
Consumer: both actual interruptibility actions in the evaluator census. -/
theorem mask (q : List Nat) (interp : Interp) (m : NativeMachine) (fiber : Control.Fiber)
    (yielding : Bool) (body : NCode) (flag : Bool) (held : NoAdd fiber.frame.stack)
    (carried : currentCredits q body ≤ currentCredits q fiber.frame.current) :
    IterDebit q m fiber (evaluatePrim.withFiber interp m fiber yielding (.setInterruptible body flag)) := by
  have full (active : NCode) := noAdd_full q active fiber.frame.stack held
  cases flag
  all_goals
    unfold IterDebit
    simp only [evaluatePrim.withFiber, FrameFiber.uninterruptible, FrameFiber.interruptibleRegion,
      FrameFiber.setFiberInterruptible]
  all_goals repeat' split
  all_goals
    simp only [List.map_nil, List.sum_nil, Nat.add_zero, fiberCredits,
      Option.getD_none, Option.getD_some, currentCredits, stackCredits, futureCredits, Nat.zero_add]
    simp only [full]
  all_goals omega

/-- Native countdown parks add only observer metadata and an administrative cancellation frame.
Consumer: await-all, fail-fast and new-child action clauses. -/
theorem countdown (q : List Nat) (root : NativeEff) (table : RowTable) (m : NativeMachine)
    (fiber : Control.Fiber) (yielding : Bool) (targets : List FiberId) (resume : Resume EffName)
    (failFast : Bool) (held : NoAdd fiber.frame.stack)
    (unique : (m.fibers.map RunFiber.id).Nodup)
    (shape : resume = .exitsValue ∨ resume = .void) :
    let out := countdownPark (interpAt root m.completedExits table) m fiber targets resume failFast
    IterDebit q m fiber ⟨out.1, out.2.1, yielding, .continue_, []⟩ := by
  have full (active : NCode) := noAdd_full q active fiber.frame.stack held
  unfold countdownPark
  dsimp only
  cases walk : countdownWalk {m with nextToken := m.nextToken + 1} targets [] with
  | mk exits waiting =>
    cases waiting with
    | none =>
      have zero : currentCredits q (countdownPark.resumePrim (interpAt root m.completedExits table) resume exits) = 0 := by
        rcases shape with rfl | rfl <;> rfl
      unfold IterDebit outsideCredits fiberCredits
      simp only [List.map_nil, List.sum_nil, Nat.add_zero, full]
      rw [zero]
      omega
    | some pair =>
      obtain ⟨target, remaining⟩ := pair
      have off := CommandDebit.modify_outside q {m with nextToken := m.nextToken + 1} fiber.id target
        (fun g => {g with observers := g.observers ++ [Observer.countdown fiber.id m.nextToken]}) unique
        (fun _ => rfl) (fun _ => Nat.le_refl _)
      have trace : ({m with nextToken := m.nextToken + 1}.modify target
          (fun g => {g with observers := g.observers ++ [Observer.countdown fiber.id m.nextToken]})).trace = m.trace := by
        unfold RunMachine.modify
        split <;> rfl
      unfold IterDebit
      simp only [RunMachine.emit_trace, trace, List.countP_append,
        List.countP_cons, List.countP_nil, ReleaseTrace.releaseAt, ReleaseTrace.registeredAt,
        List.map_nil, List.sum_nil, Nat.add_zero, fiberCredits, RunFiber.park,
        stackCredits, futureCredits, Nat.zero_add, Bool.false_eq_true, if_false, full]
      change _ + outsideCredits q fiber.id _ + _ + _ ≤ _ + outsideCredits q fiber.id m + _ + _
      have emitted : outsideCredits q fiber.id
          (({m with nextToken := m.nextToken + 1}.modify target
            (fun g => {g with observers := g.observers ++ [Observer.countdown fiber.id m.nextToken]})).emit
              [.parkedOn fiber.id m.nextToken]) =
          outsideCredits q fiber.id ({m with nextToken := m.nextToken + 1}.modify target
            (fun g => {g with observers := g.observers ++ [Observer.countdown fiber.id m.nextToken]})) := rfl
      rw [emitted]
      change outsideCredits q fiber.id _ ≤ outsideCredits q fiber.id m at off
      exact Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_left off _) _) _

/-- Interrupting another stored fiber discards at most its old reservation.
Consumer: the actual interruptAs action in the evaluator census. -/
theorem interruptAs (q : List Nat) (root : NativeEff) (table : RowTable) (m : NativeMachine)
    (fiber : Control.Fiber) (yielding : Bool) (target who : FiberId)
    (unique : (m.fibers.map RunFiber.id).Nodup) :
    IterDebit q m fiber (evaluatePrim.interruptAs (interpAt root m.completedExits table) m fiber yielding target who) := by
  unfold evaluatePrim.interruptAs
  cases found : m.fiber? target with
  | none =>
    unfold IterDebit
    simp only [List.map_nil, List.sum_nil, Nat.add_zero]
    exact Nat.le_refl _
  | some old =>
    dsimp only
    have bound := outside_update_le q m fiber.id old
      (interruptRecord (interpAt root m.completedExits table) (some who)
        ((interpAt root m.completedExits table).stackAnnotations fiber.id) old).1 unique
      (by simpa only [fiber_id_of_lookup found] using found)
      (interruptRecord_id root table (some who) _ old)
      (CommandDebit.interrupt_record root table q (some who) _ old)
    unfold IterDebit
    simp only [RunMachine.emit_trace, List.countP_append, List.countP_cons, List.countP_nil,
      ReleaseTrace.releaseAt, ReleaseTrace.registeredAt, RunMachine.update_trace]
    cases applyNow : (interruptRecord (interpAt root m.completedExits table) (some who)
      ((interpAt root m.completedExits table).stackAnnotations fiber.id) old).2
    all_goals
      simp only [Bool.false_eq_true, if_false, if_true, List.map_append, List.sum_append, List.map_cons, List.map_nil,
        List.sum_cons, List.sum_nil, commandCredits, Nat.add_zero]
      change _ + outsideCredits q fiber.id (m.update _) + _ + _ ≤ _ + outsideCredits q fiber.id m + _ + _
      omega

/-- Administrative commands and answers satisfy the same local accounting inequality.
Consumer: the actual action census. -/
theorem boundary (q : List Nat) (before : NativeMachine) (fiber : Control.Fiber) (it : RuntimeShape.Iteration)
    (starts : it.machine.trace.countP (ReleaseTrace.releaseAt q) = before.trace.countP (ReleaseTrace.releaseAt q))
    (registrations : it.machine.trace.countP (ReleaseTrace.registeredAt q) = before.trace.countP (ReleaseTrace.registeredAt q))
    (outside : outsideCredits q fiber.id it.machine ≤ outsideCredits q fiber.id before)
    (localDebit : fiberCredits q it.fiber ≤ fiberCredits q fiber)
    (commands : (it.nested.map (commandCredits q)).sum = 0) : IterDebit q before fiber it := by
  unfold IterDebit
  rw [starts, registrations, commands, Nat.add_zero]
  omega

/-- Scope linking changes only administrative finalizers, metadata or interruption state.
Consumer: runIn action debit in the native evaluator census. -/
theorem link (q : List Nat) (root : NativeEff) (table : RowTable) (m : NativeMachine)
    (owner target : FiberId) (scope : Nat) (mode : Supervision.ScopeMode)
    (who : Option FiberId) (extra : ReasonAnnotations Ann)
    (fibers : (m.fibers.map RunFiber.id).Nodup)
    (scopes : (m.state.scopes.entries.map ScopeEntry.key).Nodup) (fresh : m.state.ScopeKeysFresh) :
    let out := linkScope (interpAt root m.completedExits table) m mode scope target who extra
    outsideCredits q owner out.1 ≤ outsideCredits q owner m ∧
    out.1.trace.countP (ReleaseTrace.releaseAt q) = m.trace.countP (ReleaseTrace.releaseAt q) ∧
    out.1.trace.countP (ReleaseTrace.registeredAt q) = m.trace.countP (ReleaseTrace.registeredAt q) ∧
    (out.2.map (commandCredits q)).sum = 0 := by
  unfold linkScope
  cases status : (interpAt root m.completedExits table).scopeStatus scope m.state with
  | none => exact ⟨Nat.le_refl _, rfl, rfl, rfl⟩
  | some closing =>
    cases closing with
    | some exit =>
      cases found : m.fiber? target with
      | none => exact ⟨Nat.le_refl _, rfl, rfl, rfl⟩
      | some fiber =>
        dsimp only
        have off := outside_update_le q m owner fiber
          (interruptRecord (interpAt root m.completedExits table) who extra fiber).1 fibers
          (by simpa only [fiber_id_of_lookup found] using found)
          (interruptRecord_id root table who extra fiber)
          (CommandDebit.interrupt_record root table q who extra fiber)
        refine ⟨off, ?_, ?_, ?_⟩
        · simp only [RunMachine.emit_trace, RunMachine.update_trace, List.countP_append,
            List.countP_cons, List.countP_nil, ReleaseTrace.releaseAt, Bool.false_eq_true, if_false, Nat.add_zero]
        · simp only [RunMachine.emit_trace, RunMachine.update_trace, List.countP_append,
            List.countP_cons, List.countP_nil, ReleaseTrace.registeredAt, Bool.false_eq_true, if_false, Nat.add_zero]
        · split <;> rfl
    | none =>
      cases found : m.fiber? target with
      | none => exact ⟨Nat.le_refl _, rfl, rfl, rfl⟩
      | some fiber =>
        dsimp only
        split
        · exact ⟨Nat.le_refl _, rfl, rfl, rfl⟩
        · cases linked : (interpAt root m.completedExits table).scopeLinkFiber mode scope target m.state with
          | none => exact ⟨Nat.le_refl _, rfl, rfl, rfl⟩
          | some result =>
            obtain ⟨stores, key⟩ := result
            have changed := ScopeTransfer.link q mode scope target scopes fresh linked
            have off := CommandDebit.modify_outside q {m with state := stores} owner target
              (fun f => {f with observers := f.observers ++ [Observer.dropScopeFinalizer scope key]}) fibers
              (fun _ => rfl) (fun _ => Nat.le_refl _)
            have old : outsideCredits q owner {m with state := stores} = outsideCredits q owner m := by
              unfold outsideCredits
              unfold ScopeTransfer.storedCredits at changed
              rw [changed]
            have trace : ({m with state := stores}.modify target
                (fun f => {f with observers := f.observers ++ [Observer.dropScopeFinalizer scope key]})).trace = m.trace := by
              unfold RunMachine.modify
              split <;> rfl
            refine ⟨?_, ?_, ?_, rfl⟩
            · exact old ▸ off
            · simp only [RunMachine.emit_trace, trace, List.countP_append, List.countP_cons,
                List.countP_nil, ReleaseTrace.releaseAt, Bool.false_eq_true, if_false, Nat.add_zero]
            · simp only [RunMachine.emit_trace, trace, List.countP_append, List.countP_cons,
                List.countP_nil, ReleaseTrace.registeredAt, Bool.false_eq_true, if_false, Nat.add_zero]

/-- Reservation required by programs an actual fiber action installs or launches.
Consumer: actual action debit and the source/stored producer bound. -/
def demand (q : List Nat) : NAction → Nat
  | .fork program _ _ | .forkIn program _ _ _ | .forkScoped program _ _
  | .setInterruptible program _ => currentCredits q program
  | .raceAll programs _ | .raceAllFirst programs _ => (programs.map (currentCredits q)).sum
  | _ => 0

/-- Removing observer metadata leaves every off-owner reservation unchanged.
Consumer: the actual dropObservers action census. -/
theorem drop_outside (q : List Nat) (m : NativeMachine) (owner : FiberId) (token : Nat) :
    outsideCredits q owner {m with fibers := m.fibers.map fun g =>
      {g with observers := g.observers.filter fun
        | .resumeAwait _ t _ => t ≠ token
        | .countdown _ t => t ≠ token
        | _ => true}} = outsideCredits q owner m := by
  unfold outsideCredits
  rw [List.map_map]
  rfl

/-- Every actual non-parallel fiber action spends at most its existing active reservation.
Consumer: the native evaluator aggregate, then unchanged Workers release history. -/
theorem action (q : List Nat) (root : NativeEff) (table : RowTable) (m : NativeMachine)
    (fiber : Control.Fiber) (yielding : Bool) (selected : NAction)
    (held : NoAdd fiber.frame.stack) (source : SourceScope.ActionAt root selected)
    (sequential : SourceScope.SequentialSource root)
    (fibers : (m.fibers.map RunFiber.id).Nodup)
    (scopes : (m.state.scopes.entries.map ScopeEntry.key).Nodup) (fresh : m.state.ScopeKeysFresh)
    (carried : demand q selected ≤ currentCredits q fiber.frame.current) :
    IterDebit q m fiber (evaluatePrim.withFiber (interpAt root m.completedExits table) m fiber yielding selected) := by
  have full (active : NCode) := noAdd_full q active fiber.frame.stack held
  cases selected
  case fork program options site => exact fork q _ m fiber yielding program options site held carried
  case forkIn program options scope site => exact forkIn q _ m fiber yielding program options scope site held carried
  case forkScoped program options site => exact forkScoped q _ m fiber yielding program options site held carried
  case setInterruptible program flag => exact mask q _ m fiber yielding program flag held carried
  case raceAll programs site => exact race q root table m fiber yielding programs site .firstSuccess held carried
  case raceAllFirst programs site => exact race q root table m fiber yielding programs site .firstExit held carried
  case closeScope scope exit => exact closeScope q root table m fiber yielding scope exit held scopes
  case closePar programs => exact False.elim (SourceScope.SequentialSource.not_parallel sequential source.2)
  case interruptAs target who => exact interruptAs q root table m fiber yielding target who fibers
  case awaitAll targets => exact countdown q root table m fiber yielding targets .exitsValue false held fibers (Or.inl rfl)
  case awaitAllFailFast targets => exact countdown q root table m fiber yielding targets .exitsValue true held fibers (Or.inl rfl)
  case awaitNewChildren snapshot => exact countdown q root table m fiber yielding _ .void false held fibers (Or.inr rfl)
  case runIn target scope =>
    have linked := link q root table m fiber.id target scope .fiberRunIn (some target) ReasonAnnotations.empty fibers scopes fresh
    apply boundary
    · exact linked.2.1
    · exact linked.2.2.1
    · exact linked.1
    · simp only [evaluatePrim.withFiber, fiberCredits, currentCredits, full]
      omega
    · exact linked.2.2.2
  case dropObservers token =>
    apply boundary
    · rfl
    · rfl
    · exact Nat.le_of_eq (drop_outside q m fiber.id token)
    · simp only [evaluatePrim.withFiber, fiberCredits, currentCredits, full]
      omega
    · rfl
  case interrupt target =>
    simp only [evaluatePrim.withFiber]
    apply replace_current q m fiber yielding _ .continue_ held
    exact Nat.zero_le _
  case interruptScoped target =>
    simp only [evaluatePrim.withFiber]
    split
    all_goals apply replace_current q m fiber yielding _ .continue_ held
    all_goals exact Nat.zero_le _
  case interruptAll targets interruptor =>
    clear source carried
    have commands : (((targets.map fun t => Cmd.interruptTarget (κ := NCode) t
        (some (interruptor.getD fiber.id)) ((interpAt root m.completedExits table).stackAnnotations fiber.id)) ++
        [Cmd.afterInterrupt fiber.id yielding (.awaitAll targets)]).map (commandCredits q)).sum = 0 := by
      induction targets with
      | nil => rfl
      | cons target rest ih => simpa only [List.map_append, List.sum_append, List.map_cons, List.map_nil, List.cons_append,
          List.sum_cons, List.sum_nil, commandCredits, Nat.zero_add, Nat.add_zero] using ih
    exact boundary q m fiber _ rfl rfl (Nat.le_refl _) (Nat.le_refl _) commands
  case setContext context =>
    apply boundary
    · simp only [evaluatePrim.withFiber, RunMachine.emit_trace, List.countP_append,
        List.countP_cons, List.countP_nil, ReleaseTrace.releaseAt, Bool.false_eq_true, if_false, Nat.add_zero]
    · simp only [evaluatePrim.withFiber, RunMachine.emit_trace, List.countP_append,
        List.countP_cons, List.countP_nil, ReleaseTrace.registeredAt, Bool.false_eq_true, if_false, Nat.add_zero]
    · exact Nat.le_refl _
    · simp only [evaluatePrim.withFiber, fiberCredits, currentCredits, full]
      omega
    · rfl
  all_goals
    unfold IterDebit
    simp only [evaluatePrim.withFiber, FrameFiber.uninterruptible]
  all_goals repeat' split
  all_goals
    simp only [List.map_nil, List.sum_nil, List.map_cons, List.sum_cons, commandCredits,
      fiberCredits, currentCredits, stackCredits, futureCredits, full, Nat.add_zero,
      Nat.zero_add]
  all_goals omega

/-- Stored actions retain precisely the programs that their active name reserves.
Consumer: actual withFiberOf producer bound. -/
theorem store_demand (q : List Nat) (name : ActionName) :
    demand q (embedAction (actionOf name)) ≤ Names.actionCredits q name := by
  cases name
  case raceAll race => cases race <;> exact Nat.le_refl _
  all_goals
    simp only [actionOf, embedAction, demand, Names.actionCredits, prog_of_credits]
    aesop (add safe apply [Nat.zero_le])

/-- Every source race entrant starts before its first cleanup registration.
Consumer: source_action_demand. -/
theorem entrants_demand (q : List Nat) (bodies : Effs NativeOp) (point : Point) :
    ((actionAt.entrants bodies point).map (currentCredits q)).sum = 0 := by
  fun_induction actionAt.entrants bodies point <;>
    simp only [List.map_nil, List.sum_nil, List.map_cons, List.sum_cons, compile_credits, Nat.zero_add]
  assumption

/-- The native source action compiler creates no previously registered reservation.
Consumer: actual withFiberOf producer bound. -/
theorem source_demand (q : List Nat) (root : NativeEff) (point : Point) (selected : NAction)
    (found : actionAt root point = some selected) : demand q selected = 0 := by
  fun_cases actionAt root point
  case case1 body source =>
    simp only [actionAt, source] at found
    cases found
    exact Evaluation.resolve_credits q root _
  case case2 body source =>
    simp only [actionAt, source] at found
    cases found
    exact Evaluation.resolve_credits q root _
  case case3 saved body source =>
    simp only [actionAt, source] at found
    cases found
    exact Evaluation.resolve_credits q root _
  case case4 action source qPoint refusal handles =>
    simp only [actionAt, source] at found
    cases action
    all_goals repeat' split at found
    all_goals cases found
    all_goals simp only [demand, Evaluation.resolve_credits, entrants_demand]
  case case5 noMask noInterrupt noRestore noAction =>
    unfold actionAt at found
    repeat' split at found
    all_goals aesop

/-- The actual interpreter's selected action uses at most the active thunk's reservation.
Consumer: native withFiber evaluator debit. -/
theorem producer_demand (q : List Nat) (root : NativeEff) (completed : List (FiberId × ExitV))
    (table : RowTable) (thunk : EffThunk) (selected : NAction)
    (found : (interpAt root completed table).withFiberOf thunk = some selected) :
    demand q selected ≤ currentCredits q (.withFiber thunk) := by
  cases thunk
  case act point =>
    have bounded := source_demand q root point selected found
    rw [bounded]
    exact Nat.zero_le _
  case forkInAt point scope =>
    change forkScopedAt root point scope = some selected at found
    unfold forkScopedAt at found
    split at found
    · cases found
      rw [show demand q (.forkIn (resolve root _) _ _ _) = 0 from Evaluation.resolve_credits q root _]
      exact Nat.zero_le _
    · cases found
  case store name =>
    cases name
    case act action =>
      cases found
      exact store_demand q action
    all_goals cases found
  case acquireMasked point context =>
    cases found
    exact Nat.le_refl _
  case releaseMasked point previous =>
    cases found
    simp only [demand, currentCredits, Evaluation.resolve_credits]
    exact Nat.le_refl _
  case forkLayer point memo scope =>
    cases found
    rw [show demand q (.fork (resolveLayer root point memo scope) _ _) = 0 from
      Evaluation.layer_resolve_credits q root point memo scope]
    exact Nat.zero_le _
  all_goals aesop (add norm simp [interpAt, interpOf, demand, currentCredits])

/-- The actual native fiber-action boundary discharges its program demand and source premises.
Consumer: complete primitive evaluator debit in the original Workers history proof. -/
theorem native_action (q : List Nat) (root : NativeEff) (table : RowTable) (m : NativeMachine)
    (fiber : Control.Fiber) (yielding : Bool) (thunk : EffThunk) (selected : NAction)
    (current : fiber.frame.current = .withFiber thunk)
    (held : Kept fiber.frame.current fiber.frame.stack)
    (fragment : SourceScope.Fragment root) (source : SourceScope.FrameAt root fiber.frame)
    (sequential : SourceScope.SequentialSource root)
    (fibers : (m.fibers.map RunFiber.id).Nodup)
    (scopes : (m.state.scopes.entries.map ScopeEntry.key).Nodup) (fresh : m.state.ScopeKeysFresh)
    (found : (interpAt root m.completedExits table).withFiberOf thunk = some selected) :
    IterDebit q m fiber (evaluatePrim.withFiber (interpAt root m.completedExits table) m fiber yielding selected) := by
  have clean := opaque_noAdd (current ▸ held) (by intro fin phase; cases phase) (by intro phase; cases phase)
  have code : SourceScope.CodeAt root (.withFiber thunk) := current ▸ source.1
  exact action q root table m fiber yielding selected clean
    (SourceScope.interp_action_at root fragment m.completedExits table thunk selected code found)
    sequential fibers scopes fresh (current ▸ producer_demand q root m.completedExits table thunk selected found)

end Effect4.Program.ReleaseCustody.NativeActionDebit
