import Effect4.Laws.Program.Guard.Core
import Effect4.Laws.Program.Guard.RegistrationQueue

/-! C3 observer and race-command extension. GuardCore is the frozen checked prefix.
The public reachable guard statement is unchanged; this module supplies its local
ownership steps. No evaluator or returned-frame proof is duplicated here. -/

set_option autoImplicit false
set_option maxRecDepth 2048

namespace Effect4.Program.Guard
open Effect4 Effect4.Machine Effect4.Program
open Effect4.Program.Guard.RegistrationQueue


abbrev NPending := Pending EffName Val Err Defect FiberId Ann

theorem fiberGuardState_pendingMap {m : NativeMachine} {f : NFiber}
    (valid : FiberGuardState m f) (changePending : NPending → NPending)
    (tokens : ∀ pending, (changePending pending).token = pending.token) :
    FiberGuardState m { f with pending := f.pending.map changePending } := by
  refine ⟨valid.below, ?_, valid.idle, valid.parkedBelow, valid.exited,
    valid.deferredCause, valid.codes, valid.tasks⟩
  have shape := valid.pending
  cases hp : f.parked with
  | notParked =>
    simp only [PendingShape, hp] at shape ⊢
    rw [shape]; rfl
  | withGuard token =>
    simp only [PendingShape, hp] at shape ⊢
    obtain ⟨pending, he, ht⟩ := shape
    exact ⟨changePending pending, by rw [he]; rfl, (tokens pending).trans ht⟩

theorem fiberGuardState_context {m n : NativeMachine} {f : NFiber}
    (valid : FiberGuardState m f) (ids : m.nextId ≤ n.nextId)
    (tokens : m.nextToken ≤ n.nextToken) (races : RaceHostsPreserved m n) :
    FiberGuardState n f :=
  ⟨Nat.lt_of_lt_of_le valid.below ids, valid.pending, valid.idle,
    fun token hp => Nat.lt_of_lt_of_le (valid.parkedBelow token hp) tokens,
    valid.exited, valid.deferredCause, frameCodeOwned_transport races valid.codes, valid.tasks⟩

theorem requestOf_update_noExternal_subset (m : NativeMachine) (g : NFiber)
    (code : externalRequest g.frame.current = none) (fiber : FiberId) (token : Nat)
    (request : NativeOp × Val) (hr : requestOf (m.update g) fiber token = some request) :
    requestOf m fiber token = some request := by
  obtain ⟨f, hf, hp, hc⟩ := requestOf_shape hr
  rw [fiber_lookup_update] at hf
  cases hold : m.fiber? fiber with
  | none => simp only [hold, Option.map_none] at hf; cases hf
  | some old =>
    simp only [hold, Option.map_some] at hf
    split at hf
    · obtain rfl := Option.some.inj hf
      rw [code] at hc; cases hc
    · obtain rfl := Option.some.inj hf
      exact requestOf_of_shape hold hp hc

theorem commandControls_update_inactive {m : NativeMachine} {f : NFiber}
    (hf : m.fiber? f.id = some f) (g : NFiber) (id : g.id = f.id)
    (inactive : f.running = false) (exit : g.exit = f.exit) :
    CommandControlsPreserved m (m.update g) := by
  constructor
  · intro fiber old hold running parked
    by_cases he : old.id = f.id
    · have hl : m.fiber? f.id = some old := by
        simpa only [← he, fiber_id_of_lookup hold] using hold
      have heq : old = f := Option.some.inj (hl.symm.trans hf)
      subst old
      rw [inactive] at running
      cases running
    · refine ⟨old, ?_, running, parked, rfl⟩
      simp only [fiber_lookup_update, hold, Option.map_some, id, he, ↓reduceIte]
  · intro fiber old hold hexit
    by_cases he : old.id = f.id
    · have hl : m.fiber? f.id = some old := by
        simpa only [← he, fiber_id_of_lookup hold] using hold
      have heq : old = f := Option.some.inj (hl.symm.trans hf)
      subst old
      exact ⟨g, fiber_lookup_update_self hold g (id.trans (fiber_id_of_lookup hold)), exit ▸ hexit⟩
    · refine ⟨old, ?_, hexit⟩
      simp only [fiber_lookup_update, hold, Option.map_some, id, he, ↓reduceIte]

theorem guardQueue_update_inactive (p : NativeEff) (table : RowTable)
    {m : NativeMachine} {commands : List NCmd} (queue : GuardQueue p table m commands)
    {f : NFiber} (hf : m.fiber? f.id = some f) (g : NFiber) (id : g.id = f.id)
    (inactive : f.running = false) (exit : g.exit = f.exit)
    (code : externalRequest g.frame.current = none) : GuardQueue p table (m.update g) commands := by
  refine ⟨?_, queue.owners, ?_, queue.codeSites⟩
  · intro command hc
    exact commandAuthority_transport_commands p table
      (commandControls_update_inactive hf g id inactive exit)
      (fun _ race hr => ⟨race, hr, rfl⟩) command (queue.authority command hc)
  · exact reservedKeys_of_requests_subset queue.keys (Nat.le_refl _)
      (requestOf_update_noExternal_subset m g code)

theorem interruptRecord_running_exit (p : NativeEff) (table : RowTable)
    (who : Option FiberId) (extra : ReasonAnnotations Ann) (f : NFiber) :
    (interruptRecord (interpOf p table) who extra f).1.running = f.running ∧
    (interruptRecord (interpOf p table) who extra f).1.exit = f.exit := by
  cases he : f.exit <;> cases hi : f.frame.interruptible <;> cases hr : f.running <;>
    simp [interruptRecord, FiberCore.interruptible, FiberCore.recordCause,
      FiberCore.setDeferred, FiberCore.answerWith, he, hi, hr]

theorem fiber_lookup_interruptRecord_fields (p : NativeEff) (table : RowTable)
    {m : NativeMachine} {target : NFiber} (ht : m.fiber? target.id = some target)
    (who : Option FiberId) (extra : ReasonAnnotations Ann) {fiber : FiberId} {f : NFiber}
    (hf : m.fiber? fiber = some f) :
    ∃ g, (m.update (interruptRecord (interpOf p table) who extra target).1).fiber? fiber = some g ∧
      g.running = f.running ∧ g.exit = f.exit := by
  let next := (interruptRecord (interpOf p table) who extra target).1
  have id : next.id = target.id := interruptRecord_id p table who extra target
  by_cases he : f.id = target.id
  · have hl : m.fiber? target.id = some f := by
      simpa only [← he, fiber_id_of_lookup hf] using hf
    have heq : f = target := Option.some.inj (hl.symm.trans ht)
    subst f
    exact ⟨next, fiber_lookup_update_self hf next (id.trans (fiber_id_of_lookup hf)),
      interruptRecord_running_exit p table who extra target⟩
  · refine ⟨f, ?_, rfl, rfl⟩
    change (m.update next).fiber? fiber = some f
    simp only [fiber_lookup_update, hf, Option.map_some, id, he, ↓reduceIte]

theorem interruptEach_context (p : NativeEff) (table : RowTable)
    (who : FiberId) (extra : ReasonAnnotations Ann) (targets : List FiberId)
    (m : NativeMachine) (commands : List NCmd) :
    let after := (interruptEach (interpOf p table) who extra targets (m, commands)).1
    after.nextId = m.nextId ∧ after.races = m.races := by
  induction targets generalizing m commands with
  | nil => exact ⟨rfl, rfl⟩
  | cons target targets ih =>
    cases hf : m.fiber? target with
    | none => simpa only [interruptEach, List.foldl_cons, hf] using ih m commands
    | some f =>
      let next := (m.update (interruptRecord (interpOf p table) (some who) extra f).1).emit
        [RunEvent.interruptRecorded (some who) target]
      let pending := commands ++ (if (interruptRecord (interpOf p table) (some who) extra f).2 then
        [.evaluate target] else [])
      have hc : next.nextId = m.nextId ∧ next.races = m.races := ⟨rfl, rfl⟩
      have later := ih next pending
      simpa only [interruptEach, List.foldl_cons, hf] using
        And.intro (later.1.trans hc.1) (later.2.trans hc.2)

theorem interruptEach_lookup_fields (p : NativeEff) (table : RowTable)
    (who : FiberId) (extra : ReasonAnnotations Ann) (targets : List FiberId)
    (m : NativeMachine) (commands : List NCmd) {fiber : FiberId} {f : NFiber}
    (hf : m.fiber? fiber = some f) :
    ∃ g, (interruptEach (interpOf p table) who extra targets (m, commands)).1.fiber? fiber = some g ∧
      g.running = f.running ∧ g.exit = f.exit := by
  induction targets generalizing m commands f with
  | nil => exact ⟨f, hf, rfl, rfl⟩
  | cons target targets ih =>
    cases ht : m.fiber? target with
    | none => simpa only [interruptEach, List.foldl_cons, ht] using ih m commands hf
    | some old =>
      obtain ⟨g, hg, running, exit⟩ := fiber_lookup_interruptRecord_fields p table (target := old)
        (by simpa only [fiber_id_of_lookup ht] using ht) (some who) extra hf
      let next := (m.update (interruptRecord (interpOf p table) (some who) extra old).1).emit
        [RunEvent.interruptRecorded (some who) target]
      let pending := commands ++ (if (interruptRecord (interpOf p table) (some who) extra old).2 then
        [.evaluate target] else [])
      obtain ⟨last, hl, run', exit'⟩ := ih next pending hg
      refine ⟨last, ?_, run'.trans running, exit'.trans exit⟩
      simpa only [interruptEach, List.foldl_cons, ht] using hl

theorem interruptedAt_interruptEach (p : NativeEff) (table : RowTable)
    (who : FiberId) (extra : ReasonAnnotations Ann) (targets : List FiberId)
    (m : NativeMachine) (commands : List NCmd) {fiber : FiberId}
    (interrupted : InterruptedAt m fiber) :
    InterruptedAt (interruptEach (interpOf p table) who extra targets (m, commands)).1 fiber := by
  induction targets generalizing m commands with
  | nil => exact interrupted
  | cons target targets ih =>
    cases ht : m.fiber? target with
    | none => simpa only [interruptEach, List.foldl_cons, ht] using ih m commands interrupted
    | some old =>
      let next := (m.update (interruptRecord (interpOf p table) (some who) extra old).1).emit
        [RunEvent.interruptRecorded (some who) target]
      let pending := commands ++ (if (interruptRecord (interpOf p table) (some who) extra old).2 then
        [.evaluate target] else [])
      have hi : InterruptedAt next fiber :=
        interruptedAt_update_interruptRecord p table ht (some who) extra fiber interrupted
      simpa only [interruptEach, List.foldl_cons, ht] using ih next pending hi


theorem fiber_lookup_addObserver_fields (m : NativeMachine) (target : FiberId)
    (observer : Observer) {fiber : FiberId} {f : NFiber} (hf : m.fiber? fiber = some f) :
    ∃ g, (m.modify target fun old => { old with observers := old.observers ++ [observer] }).fiber?
      fiber = some g ∧ g.running = f.running ∧ g.exit = f.exit := by
  unfold RunMachine.modify
  cases ht : m.fiber? target with
  | none => exact ⟨f, hf, rfl, rfl⟩
  | some old =>
    by_cases he : f.id = old.id
    · have hl : m.fiber? target = some f := by
        simpa only [← fiber_id_of_lookup ht, ← he, fiber_id_of_lookup hf] using hf
      have heq : f = old := Option.some.inj (hl.symm.trans ht)
      subst f
      exact ⟨{ old with observers := old.observers ++ [observer] },
        fiber_lookup_update_self hf { old with observers := old.observers ++ [observer] }
          (show ({ old with observers := old.observers ++ [observer] } : NFiber).id = fiber from
            fiber_id_of_lookup (f := old) (m := m) hf), rfl, rfl⟩
    · refine ⟨f, ?_, rfl, rfl⟩
      simp only [fiber_lookup_update, hf, Option.map_some, he, ↓reduceIte]

theorem guardState_restorePending {m n : NativeMachine} {w current : NFiber}
    (original : GuardState m) (hw : m.fiber? w.id = some w)
    (state : GuardState n) (hc : n.fiber? w.id = some current)
    (ids : m.nextId ≤ n.nextId) (tokens : m.nextToken ≤ n.nextToken)
    (races : RaceHostsPreserved m n) (reserved : ReservedKeys n (fiberKeys w))
    (code : externalRequest w.frame.current = none)
    (changePending : NPending → NPending)
    (preserveToken : ∀ pending, (changePending pending).token = pending.token) :
    GuardState (n.update { w with pending := w.pending.map changePending }) := by
  have currentId : current.id = w.id := fiber_id_of_lookup hc
  apply guardState_update_noExternal (f := current) state
    (by simpa only [currentId] using hc)
    { w with pending := w.pending.map changePending } currentId.symm
    (fiberGuardState_pendingMap
      (fiberGuardState_context (guardState_fiber original (List.mem_of_find?_eq_some hw))
        ids tokens races) changePending preserveToken)
    reserved code

theorem guardState_fireObserver_countdown (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (id : FiberId) (exit : ExitV) (commands : List NCmd)
    (waiter : FiberId) (token : Nat) (state : GuardState m)
    (reserved : ReservedKeys m [(waiter, token)]) :
    GuardState (fireObserver (interpOf p table) id exit (m, commands) (.countdown waiter token)).1 := by
  let base := m.emit [RunEvent.observerFired id (.countdown waiter token)]
  have baseState : GuardState base := guardState_emit state [RunEvent.observerFired id (.countdown waiter token)]
  have baseKeys : ReservedKeys base [(waiter, token)] := reservedKeys_emit reserved _
  cases hw : base.fiber? waiter with
  | none => simpa only [fireObserver, show m.emit _ = base from rfl, hw] using baseState
  | some w =>
    have wid : w.id = waiter := fiber_id_of_lookup hw
    have hw' : base.fiber? w.id = some w := by simpa only [wid] using hw
    cases hp : w.pending.find? (fun q => q.token = token) with
    | none => simpa only [fireObserver, show m.emit _ = base from rfl, hw, hp] using baseState
    | some pending =>
      have code : externalRequest w.frame.current = none :=
        pending_reserved_noExternal baseState hw' hp (by simpa only [wid] using baseKeys)
      let run := if pending.failFast && !exit.isSuccess && pending.collected.all Exit.isSuccess then
        interruptEach (interpOf p table) waiter ((interpOf p table).stackAnnotations waiter)
          pending.remaining (base, []) else (base, [])
      have runState : GuardState run.1 := by
        dsimp only [run]; split
        · exact guardState_interruptEach p table waiter _ _ base [] baseState
        · exact baseState
      have runKeys : ReservedKeys run.1 (fiberKeys w) := by
        have keys := reservedKeys_fiber baseState (List.mem_of_find?_eq_some hw)
        dsimp only [run]; split
        · exact reservedKeys_interruptEach p table waiter _ _ base [] _ keys
        · exact keys
      have callbackKeys : ReservedKeys run.1 [(waiter, token)] := by
        dsimp only [run]; split
        · exact reservedKeys_interruptEach p table waiter _ _ base [] _ baseKeys
        · exact baseKeys
      have context : run.1.nextId = base.nextId ∧ run.1.nextToken = base.nextToken ∧
          run.1.races = base.races := by
        dsimp only [run]; split
        · have hc := interruptEach_context p table waiter ((interpOf p table).stackAnnotations waiter)
            pending.remaining base []
          exact ⟨hc.1, nextToken_interruptEach p table waiter _ _ base [], hc.2⟩
        · exact ⟨rfl, rfl, rfl⟩
      have races : RaceHostsPreserved base run.1 := by
        intro raceId race hr
        refine ⟨race, ?_, rfl⟩
        change run.1.races.find? _ = some race
        rw [context.2.2]
        exact hr
      have lookup : ∃ current, run.1.fiber? w.id = some current ∧
          current.running = w.running ∧ current.exit = w.exit := by
        dsimp only [run]; split
        · exact interruptEach_lookup_fields p table waiter _ _ base [] hw'
        · exact ⟨w, hw', rfl, rfl⟩
      obtain ⟨current, currentLookup, currentRunning, currentExit⟩ := lookup
      simp only [fireObserver, show m.emit _ = base from rfl, hw, hp]
      cases walk : countdownWalk run.1 pending.remaining (pending.collected ++ [exit]) with
      | mk exits next =>
        cases next with
        | none =>
          exact guardState_restorePending baseState hw' runState currentLookup
            (Nat.le_of_eq context.1.symm) (Nat.le_of_eq context.2.1.symm) races runKeys code
            (fun q => if q.token = token then { q with waitingOn := none, remaining := [], collected := exits } else q)
            (by intro q; split <;> rfl)
        | some pair =>
          obtain ⟨next, rest⟩ := pair
          let updated := run.1.modify next fun f => { f with observers := f.observers ++ [.countdown waiter token] }
          have added : GuardState updated := guardState_addObserver runState next (.countdown waiter token) callbackKeys
          obtain ⟨after, afterLookup, _, _⟩ :=
            fiber_lookup_addObserver_fields run.1 next (.countdown waiter token) currentLookup
          have ids : base.nextId ≤ updated.nextId := by
            dsimp only [updated, RunMachine.modify]
            split <;> exact Nat.le_of_eq context.1.symm
          have tokens : base.nextToken ≤ updated.nextToken := by
            dsimp only [updated, RunMachine.modify]
            split <;> exact Nat.le_of_eq context.2.1.symm
          have races' : RaceHostsPreserved base updated := by
            intro raceId race hr
            obtain ⟨found, hf, hh⟩ := races raceId race hr
            refine ⟨found, ?_, hh⟩
            dsimp only [updated, RunMachine.modify]
            split <;> exact hf
          exact guardState_restorePending baseState hw' added afterLookup ids tokens races'
            (reservedKeys_addObserver runKeys next (.countdown waiter token)) code
            (fun q => if q.token = token then
              { q with waitingOn := some next, remaining := rest, collected := exits } else q)
            (by intro q; split <;> rfl)


theorem interruptEach_append (p : NativeEff) (table : RowTable)
    (who : FiberId) (extra : ReasonAnnotations Ann) (targets : List FiberId)
    (m : NativeMachine) (front rest : List NCmd) :
    interruptEach (interpOf p table) who extra targets (m, front ++ rest) =
      let result := interruptEach (interpOf p table) who extra targets (m, rest)
      (result.1, front ++ result.2) := by
  induction targets generalizing m rest with
  | nil => rfl
  | cons target targets ih =>
    cases hf : m.fiber? target with
    | none => simpa only [interruptEach, List.foldl_cons, hf] using ih m rest
    | some f =>
      let next := (m.update (interruptRecord (interpOf p table) (some who) extra f).1).emit
        [RunEvent.interruptRecorded (some who) target]
      let owed : List NCmd := if (interruptRecord (interpOf p table) (some who) extra f).2 then
        [Cmd.evaluate target] else []
      simpa only [interruptEach, List.foldl_cons, hf, List.append_assoc] using ih next (rest ++ owed)

theorem guardQueue_restorePending (p : NativeEff) (table : RowTable)
    {m : NativeMachine} {commands : List NCmd} (queue : GuardQueue p table m commands)
    {w current : NFiber} (hc : m.fiber? w.id = some current)
    (running : current.running = false) (exit : current.exit = w.exit)
    (code : externalRequest w.frame.current = none) (changePending : NPending → NPending) :
    GuardQueue p table (m.update { w with pending := w.pending.map changePending }) commands := by
  have id : current.id = w.id := fiber_id_of_lookup hc
  exact guardQueue_update_inactive p table queue (f := current)
    (by simpa only [id] using hc) { w with pending := w.pending.map changePending }
    id.symm running exit.symm code

theorem guardQueue_fireObserver_countdown (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (id : FiberId) (exit : ExitV) (commands : List NCmd)
    (waiter : FiberId) (token : Nat) (state : GuardState m)
    (queue : GuardQueue p table m commands) (reserved : ReservedKeys m [(waiter, token)]) :
    let result := fireObserver (interpOf p table) id exit (m, commands) (.countdown waiter token)
    GuardQueue p table result.1 result.2 := by
  let base := m.emit [RunEvent.observerFired id (.countdown waiter token)]
  have baseState : GuardState base := guardState_emit state _
  have baseQueue : GuardQueue p table base commands := guardQueue_emit p table queue _
  have baseKeys : ReservedKeys base [(waiter, token)] := reservedKeys_emit reserved _
  cases hw : base.fiber? waiter with
  | none => simpa only [fireObserver, show m.emit _ = base from rfl, hw] using baseQueue
  | some w =>
    have wid : w.id = waiter := fiber_id_of_lookup hw
    have hw' : base.fiber? w.id = some w := by simpa only [wid] using hw
    cases hp : w.pending.find? (fun q => q.token = token) with
    | none => simpa only [fireObserver, show m.emit _ = base from rfl, hw, hp] using baseQueue
    | some pending =>
      have code : externalRequest w.frame.current = none :=
        pending_reserved_noExternal baseState hw' hp (by simpa only [wid] using baseKeys)
      have parked := (pending_lookup_guard baseState (List.mem_of_find?_eq_some hw) hp).1
      have idle : w.running = false := baseState.parkedIdle w (List.mem_of_find?_eq_some hw)
        (by rw [parked]; intro h; cases h)
      let run := if pending.failFast && !exit.isSuccess && pending.collected.all Exit.isSuccess then
        interruptEach (interpOf p table) waiter ((interpOf p table).stackAnnotations waiter)
          pending.remaining (base, []) else (base, [])
      have runQueue : GuardQueue p table run.1 (commands ++ run.2) := by
        dsimp only [run]; split
        · have hq := guardQueue_interruptEach p table waiter
            ((interpOf p table).stackAnnotations waiter) pending.remaining base commands baseQueue
          have ha := interruptEach_append p table waiter
            ((interpOf p table).stackAnnotations waiter) pending.remaining base commands []
          simp only [List.append_nil] at ha
          rw [ha] at hq
          exact hq
        · simpa only [List.append_nil] using baseQueue
      have callbackKeys : ReservedKeys run.1 [(waiter, token)] := by
        dsimp only [run]; split
        · exact reservedKeys_interruptEach p table waiter _ _ base [] _ baseKeys
        · exact baseKeys
      have lookup : ∃ current, run.1.fiber? w.id = some current ∧
          current.running = w.running ∧ current.exit = w.exit := by
        dsimp only [run]; split
        · exact interruptEach_lookup_fields p table waiter _ _ base [] hw'
        · exact ⟨w, hw', rfl, rfl⟩
      obtain ⟨current, currentLookup, currentRunning, currentExit⟩ := lookup
      simp only [fireObserver, show m.emit _ = base from rfl, hw, hp]
      cases walk : countdownWalk run.1 pending.remaining (pending.collected ++ [exit]) with
      | mk exits next =>
        cases next with
        | none =>
          have restored := guardQueue_restorePending p table runQueue currentLookup
            (currentRunning.trans idle) currentExit code
            (fun q => if q.token = token then
              { q with waitingOn := none, remaining := [], collected := exits } else q)
          apply guardQueue_snoc_resume p table restored waiter token
            (countdownPark.resumePrim (interpOf p table) pending.resumeWith exits)
          · exact reservedKeys_of_requests_subset callbackKeys (Nat.le_refl _)
              (requestOf_update_noExternal_subset _ _ code)
          · exact raceSites_countdownResume p table pending.resumeWith exits
        | some pair =>
          obtain ⟨next, rest⟩ := pair
          have added := guardQueue_addObserver p table runQueue next (.countdown waiter token)
          obtain ⟨after, afterLookup, afterRunning, afterExit⟩ :=
            fiber_lookup_addObserver_fields run.1 next (.countdown waiter token) currentLookup
          exact guardQueue_restorePending p table added afterLookup
            (afterRunning.trans (currentRunning.trans idle)) (afterExit.trans currentExit) code
            (fun q => if q.token = token then
              { q with waitingOn := some next, remaining := rest, collected := exits } else q)


theorem guardState_fireObserver (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (id : FiberId) (exit : ExitV) (commands : List NCmd)
    (observer : Observer) (state : GuardState m)
    (reserved : ReservedKeys m (observerKeys observer)) :
    GuardState (fireObserver (interpOf p table) id exit (m, commands) observer).1 := by
  cases observer with
  | countdown waiter token => exact guardState_fireObserver_countdown p table m id exit commands waiter token state reserved
  | resumeAwait waiter token mode => exact guardState_emit state _
  | callback key => exact guardState_emit (guardState_emit state _) _
  | untrackChild parent =>
    apply guardState_modify_view (guardState_emit state _) parent
      (fun f => { f with children := f.children.filter fun child => child ≠ id })
    · exact fun f hf => fiberGuardState_children (guardState_fiber (guardState_emit state _) hf) _
    · exact fun _ => ⟨rfl, rfl, rfl⟩
    · exact fun _ => rfl
  | dropScopeFinalizer scope key =>
    let base := m.emit [RunEvent.observerFired id (.dropScopeFinalizer scope key)]
    have before : GuardState base := guardState_emit state _
    have drop : (interpOf p table).dropFinalizer scope key base.state =
        match base.state.scopes.entryAt scope with
        | none => none
        | some _ => some { base.state with scopes := base.state.scopes.removeFinalizer scope key } := rfl
    simp only [fireObserver, show m.emit _ = base from rfl, drop]
    cases hs : base.state.scopes.entryAt scope with
    | none => exact guardState_halt before _
    | some entry =>
      exact guardState_withState before _ (List.Subset.refl _)
        ⟨before.internalCodes.1, before.internalCodes.2.1⟩
  | raceCallback raceId =>
    let base := m.emit [RunEvent.observerFired id (.raceCallback raceId)]
    have before : GuardState base := guardState_emit state _
    cases hr : base.race? raceId with
    | none => simpa only [fireObserver, show m.emit _ = base from rfl, hr] using before
    | some race =>
      have hr' : base.race? race.id = some race := by simpa only [race_id_of_lookup hr] using hr
      have programs := before.internalCodes.2.2.2 race (List.mem_of_find?_eq_some hr)
      let next : NRace := { race with state := Supervision.raceComplete race.state id exit }
      have updated := guardState_updateRace before hr' next rfl rfl rfl programs
      have hn : (base.updateRace next).race? next.id = some next := by
        simp only [race_lookup_updateRace, show next.id = race.id from rfl, hr', Option.map_some, ↓reduceIte]
      simp only [fireObserver, show m.emit _ = base from rfl, hr]
      split
      · exact guardState_emit (guardState_updateRace updated hn { next with settled := true }
          rfl rfl rfl programs) _
      · exact updated

theorem guardQueue_fireObserver (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (id : FiberId) (exit : ExitV) (commands : List NCmd)
    (observer : Observer) (state : GuardState m) (queue : GuardQueue p table m commands)
    (reserved : ReservedKeys m (observerKeys observer)) :
    let result := fireObserver (interpOf p table) id exit (m, commands) observer
    GuardQueue p table result.1 result.2 := by
  cases observer with
  | countdown waiter token => exact guardQueue_fireObserver_countdown p table m id exit commands waiter token state queue reserved
  | resumeAwait waiter token mode =>
    exact guardQueue_snoc_resume p table (guardQueue_emit p table queue _) waiter token
      ((interpOf p table).exitValue exit mode) (reservedKeys_emit reserved _) (raceSites_exitValue p table exit mode)
  | callback key => exact guardQueue_emit p table (guardQueue_emit p table queue _) _
  | untrackChild parent =>
    exact guardQueue_modify_fields p table (guardQueue_emit p table queue _) parent
      (fun f => { f with children := f.children.filter fun child => child ≠ id })
      (fun _ => ⟨rfl, rfl, rfl⟩) (fun _ => rfl) (fun _ h => h)
  | dropScopeFinalizer scope key =>
    let base := m.emit [RunEvent.observerFired id (.dropScopeFinalizer scope key)]
    have before : GuardQueue p table base commands := guardQueue_emit p table queue _
    have drop : (interpOf p table).dropFinalizer scope key base.state =
        match base.state.scopes.entryAt scope with
        | none => none
        | some _ => some { base.state with scopes := base.state.scopes.removeFinalizer scope key } := rfl
    simp only [fireObserver, show m.emit _ = base from rfl, drop]
    cases hs : base.state.scopes.entryAt scope with
    | none => exact guardQueue_halt p table before _
    | some entry => exact guardQueue_withState p table before _
  | raceCallback raceId =>
    let base := m.emit [RunEvent.observerFired id (.raceCallback raceId)]
    have before : GuardQueue p table base commands := guardQueue_emit p table queue _
    have baseState : GuardState base := guardState_emit state _
    cases hr : base.race? raceId with
    | none => simpa only [fireObserver, show m.emit _ = base from rfl, hr] using before
    | some race =>
      have hr' : base.race? race.id = some race := by simpa only [race_id_of_lookup hr] using hr
      let next : NRace := { race with state := Supervision.raceComplete race.state id exit }
      have updated := guardQueue_updateRace p table before hr' next rfl rfl
      have hn : (base.updateRace next).race? next.id = some next := by
        simp only [race_lookup_updateRace, show next.id = race.id from rfl, hr', Option.map_some, ↓reduceIte]
      simp only [fireObserver, show m.emit _ = base from rfl, hr]
      split
      · rename_i accepted haccepted hsettled
        have settled := guardQueue_emit p table
          (guardQueue_updateRace p table updated hn { next with settled := true } rfl rfl)
          [RunEvent.raceSettled raceId accepted]
        split
        · simpa only [List.append_nil] using settled
        · apply guardQueue_snoc_resume p table settled race.host race.token
          · exact reservedKeys_emit
              (reservedKeys_updateRace (reservedKeys_updateRace
                (reservedKeys_race baseState (List.mem_of_find?_eq_some hr)) next)
                { next with settled := true }) _
          · exact raceSites_raceSettle p table _ _ _
      · exact updated


theorem nextToken_modify (m : NativeMachine) (target : FiberId) (changeFiber : NFiber → NFiber) :
    (m.modify target changeFiber).nextToken = m.nextToken := by
  unfold RunMachine.modify
  split <;> rfl

theorem nextToken_fireObserver (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (id : FiberId) (exit : ExitV) (commands : List NCmd) (observer : Observer) :
    (fireObserver (interpOf p table) id exit (m, commands) observer).1.nextToken = m.nextToken := by
  cases observer <;> simp only [fireObserver]
  all_goals repeat' first
    | rfl
    | (solve | simp only [RunMachine.update, RunMachine.updateRace, RunMachine.emit,
        RunMachine.halt, nextToken_modify, nextToken_interruptEach])
    | split

theorem requestOf_fireObserver_countdown_subset (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (id : FiberId) (exit : ExitV) (commands : List NCmd)
    (waiter : FiberId) (token : Nat) (state : GuardState m)
    (reserved : ReservedKeys m [(waiter, token)]) (fiber : FiberId) (offered : Nat)
    (request : NativeOp × Val)
    (hr : requestOf (fireObserver (interpOf p table) id exit (m, commands) (.countdown waiter token)).1
      fiber offered = some request) : requestOf m fiber offered = some request := by
  let base := m.emit [RunEvent.observerFired id (.countdown waiter token)]
  change requestOf base fiber offered = some request
  have baseState : GuardState base := guardState_emit state _
  have baseKeys : ReservedKeys base [(waiter, token)] := reservedKeys_emit reserved _
  cases hw : base.fiber? waiter with
  | none => simpa only [fireObserver, show m.emit _ = base from rfl, hw] using hr
  | some w =>
    have wid : w.id = waiter := fiber_id_of_lookup hw
    have hw' : base.fiber? w.id = some w := by simpa only [wid] using hw
    cases hp : w.pending.find? (fun q => q.token = token) with
    | none => simpa only [fireObserver, show m.emit _ = base from rfl, hw, hp] using hr
    | some pending =>
      have code : externalRequest w.frame.current = none :=
        pending_reserved_noExternal baseState hw' hp (by simpa only [wid] using baseKeys)
      let run := if pending.failFast && !exit.isSuccess && pending.collected.all Exit.isSuccess then
        interruptEach (interpOf p table) waiter ((interpOf p table).stackAnnotations waiter)
          pending.remaining (base, []) else (base, [])
      have subset : ∀ f t r, requestOf run.1 f t = some r → requestOf base f t = some r := by
        dsimp only [run]; split
        · exact requestOf_interruptEach_subset p table waiter _ _ base []
        · exact fun _ _ _ h => h
      simp only [fireObserver, show m.emit _ = base from rfl, hw, hp] at hr
      cases walk : countdownWalk run.1 pending.remaining (pending.collected ++ [exit]) with
      | mk exits next =>
        rw [walk] at hr
        cases next with
        | none => exact subset fiber offered request (requestOf_update_noExternal_subset run.1
            { w with pending := w.pending.map fun q => if q.token = token then
              { q with waitingOn := none, remaining := [], collected := exits } else q }
            code fiber offered request hr)
        | some pair =>
          obtain ⟨next, rest⟩ := pair
          have h := requestOf_update_noExternal_subset
            (run.1.modify next fun f => { f with observers := f.observers ++ [.countdown waiter token] })
            { w with pending := w.pending.map fun q => if q.token = token then
              { q with waitingOn := some next, remaining := rest, collected := exits } else q }
            code fiber offered request hr
          rw [requestOf_addObserver] at h
          exact subset fiber offered request h

theorem requestOf_fireObserver_subset (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (id : FiberId) (exit : ExitV) (commands : List NCmd)
    (observer : Observer) (state : GuardState m) (reserved : ReservedKeys m (observerKeys observer))
    (fiber : FiberId) (token : Nat) (request : NativeOp × Val)
    (hr : requestOf (fireObserver (interpOf p table) id exit (m, commands) observer).1 fiber token = some request) :
    requestOf m fiber token = some request := by
  cases observer with
  | countdown waiter offered =>
    exact requestOf_fireObserver_countdown_subset p table m id exit commands waiter offered state reserved fiber token request hr
  | untrackChild parent =>
    rw [show (fireObserver (interpOf p table) id exit (m, commands) (.untrackChild parent)).1 =
      (m.emit [RunEvent.observerFired id (.untrackChild parent)]).modify parent
        (fun f => { f with children := f.children.filter fun child => child ≠ id }) from rfl,
      requestOf_modify_view _ _ _ _
        (fun f => { f with children := f.children.filter fun child => child ≠ id })
        (fun _ => ⟨rfl, rfl, rfl⟩)] at hr
    exact hr
  | resumeAwait waiter offered mode => exact hr
  | callback key => exact hr
  | dropScopeFinalizer scope key =>
    simp only [fireObserver] at hr
    split at hr <;> exact hr
  | raceCallback raceId =>
    simp only [fireObserver] at hr
    repeat' first | exact hr | split at hr

theorem reservedKeys_fireObserver (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (id : FiberId) (exit : ExitV) (commands : List NCmd)
    (observer : Observer) (state : GuardState m) (owned : ReservedKeys m (observerKeys observer))
    (keys : List GuardKey) (reserved : ReservedKeys m keys) :
    ReservedKeys (fireObserver (interpOf p table) id exit (m, commands) observer).1 keys := by
  apply reservedKeys_of_requests_subset reserved
  · rw [nextToken_fireObserver]; exact Nat.le_refl _
  · exact requestOf_fireObserver_subset p table m id exit commands observer state owned

theorem requestOrInterrupted_interruptEach (p : NativeEff) (table : RowTable)
    (who : FiberId) (extra : ReasonAnnotations Ann) (targets : List FiberId)
    (m : NativeMachine) (commands : List NCmd) (fiber : FiberId) (token : Nat)
    (request : NativeOp × Val) (hr : requestOf m fiber token = some request) :
    let after := (interruptEach (interpOf p table) who extra targets (m, commands)).1
    requestOf after fiber token = some request ∨ InterruptedAt after fiber := by
  letI := evaluatorFor p table
  induction targets generalizing m commands with
  | nil => exact Or.inl hr
  | cons target targets ih =>
    cases ht : m.fiber? target with
    | none => simpa only [interruptEach, List.foldl_cons, ht] using ih m commands hr
    | some old =>
      let next := (m.update (interruptRecord (interpOf p table) (some who) extra old).1).emit
        [RunEvent.interruptRecorded (some who) target]
      let pending := commands ++ (if (interruptRecord (interpOf p table) (some who) extra old).2 then
        [.evaluate target] else [])
      have first : requestOf next fiber token = some request ∨ InterruptedAt next fiber := by
        simpa only [driveStep, ht] using
          requestOrInterrupted_driveStep_interruptTarget p table m target (some who) extra commands fiber token request hr
      have later : requestOf (interruptEach (interpOf p table) who extra targets (next, pending)).1 fiber token = some request ∨
          InterruptedAt (interruptEach (interpOf p table) who extra targets (next, pending)).1 fiber := by
        rcases first with h | h
        · exact ih next pending h
        · exact Or.inr (interruptedAt_interruptEach p table who extra targets next pending h)
      simpa only [interruptEach, List.foldl_cons, ht] using later

theorem interruptedAt_update_other (m : NativeMachine) (g : NFiber) {fiber : FiberId}
    (different : g.id ≠ fiber) (interrupted : InterruptedAt m fiber) : InterruptedAt (m.update g) fiber := by
  obtain ⟨f, hf, hi⟩ := interrupted
  refine ⟨f, ?_, hi⟩
  simp only [fiber_lookup_update, hf, Option.map_some, fiber_id_of_lookup hf, Ne.symm different, ↓reduceIte]

theorem interruptedAt_restorePending {m n : NativeMachine} {w current : NFiber}
    (hw : m.fiber? w.id = some w) (hc : n.fiber? w.id = some current)
    (changePending : NPending → NPending) {fiber : FiberId}
    (original : InterruptedAt m fiber) (updated : InterruptedAt n fiber) :
    InterruptedAt (n.update { w with pending := w.pending.map changePending }) fiber := by
  by_cases same : w.id = fiber
  · obtain ⟨f, hf, hi⟩ := original
    have hl : m.fiber? w.id = some f := by simpa only [same] using hf
    have heq : f = w := Option.some.inj (hl.symm.trans hw)
    subst f
    refine ⟨{ w with pending := w.pending.map changePending }, ?_, hi⟩
    exact same ▸ fiber_lookup_update_self hc _ rfl
  · exact interruptedAt_update_other _ _ same updated


theorem requestOrInterrupted_update_other (m : NativeMachine) (g : NFiber)
    (fiber : FiberId) (token : Nat) (request : NativeOp × Val) (different : g.id ≠ fiber)
    (before : requestOf m fiber token = some request ∨ InterruptedAt m fiber) :
    requestOf (m.update g) fiber token = some request ∨ InterruptedAt (m.update g) fiber := by
  rcases before with h | h
  · exact Or.inl ((requestOf_update_other m g fiber token different) ▸ h)
  · exact Or.inr (interruptedAt_update_other m g different h)

theorem requestOrInterrupted_addObserver (m : NativeMachine) (target : FiberId) (observer : Observer)
    (fiber : FiberId) (token : Nat) (request : NativeOp × Val)
    (before : requestOf m fiber token = some request ∨ InterruptedAt m fiber) :
    let after := m.modify target fun f => { f with observers := f.observers ++ [observer] }
    requestOf after fiber token = some request ∨ InterruptedAt after fiber := by
  rcases before with h | h
  · exact Or.inl ((requestOf_addObserver m target observer fiber token) ▸ h)
  · exact Or.inr (interruptedAt_addObserver target observer h)

theorem requestOrInterrupted_fireObserver_countdown (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (id : FiberId) (exit : ExitV) (commands : List NCmd)
    (waiter : FiberId) (token : Nat) (state : GuardState m)
    (reserved : ReservedKeys m [(waiter, token)]) (fiber : FiberId) (offered : Nat)
    (request : NativeOp × Val) (hr : requestOf m fiber offered = some request) :
    let after := (fireObserver (interpOf p table) id exit (m, commands) (.countdown waiter token)).1
    requestOf after fiber offered = some request ∨ InterruptedAt after fiber := by
  let base := m.emit [RunEvent.observerFired id (.countdown waiter token)]
  have baseState : GuardState base := guardState_emit state _
  have baseKeys : ReservedKeys base [(waiter, token)] := reservedKeys_emit reserved _
  have baseRequest : requestOf base fiber offered = some request := hr
  cases hw : base.fiber? waiter with
  | none => simpa only [fireObserver, show m.emit _ = base from rfl, hw] using Or.inl (b := InterruptedAt base fiber) baseRequest
  | some w =>
    have wid : w.id = waiter := fiber_id_of_lookup hw
    have hw' : base.fiber? w.id = some w := by simpa only [wid] using hw
    cases hp : w.pending.find? (fun q => q.token = token) with
    | none => simpa only [fireObserver, show m.emit _ = base from rfl, hw, hp] using Or.inl (b := InterruptedAt base fiber) baseRequest
    | some pending =>
      have code : externalRequest w.frame.current = none :=
        pending_reserved_noExternal baseState hw' hp (by simpa only [wid] using baseKeys)
      have different : w.id ≠ fiber := by
        intro he
        obtain ⟨found, hf, _, hc⟩ := requestOf_shape baseRequest
        have hl : base.fiber? w.id = some found := by simpa only [he] using hf
        have eq : found = w := Option.some.inj (hl.symm.trans hw')
        subst found
        rw [code] at hc
        cases hc
      let run := if pending.failFast && !exit.isSuccess && pending.collected.all Exit.isSuccess then
        interruptEach (interpOf p table) waiter ((interpOf p table).stackAnnotations waiter)
          pending.remaining (base, []) else (base, [])
      have runRequest : requestOf run.1 fiber offered = some request ∨ InterruptedAt run.1 fiber := by
        dsimp only [run]; split
        · exact requestOrInterrupted_interruptEach p table waiter _ _ base [] fiber offered request baseRequest
        · exact Or.inl baseRequest
      simp only [fireObserver, show m.emit _ = base from rfl, hw, hp]
      cases walk : countdownWalk run.1 pending.remaining (pending.collected ++ [exit]) with
      | mk exits next =>
        cases next with
        | none =>
          exact requestOrInterrupted_update_other run.1
            { w with pending := w.pending.map fun q => if q.token = token then
              { q with waitingOn := none, remaining := [], collected := exits } else q }
            fiber offered request different runRequest
        | some pair =>
          obtain ⟨next, rest⟩ := pair
          exact requestOrInterrupted_update_other
            (run.1.modify next fun f => { f with observers := f.observers ++ [.countdown waiter token] })
            { w with pending := w.pending.map fun q => if q.token = token then
              { q with waitingOn := some next, remaining := rest, collected := exits } else q }
            fiber offered request different
            (requestOrInterrupted_addObserver run.1 next (.countdown waiter token) fiber offered request runRequest)

theorem requestOrInterrupted_fireObserver (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (id : FiberId) (exit : ExitV) (commands : List NCmd)
    (observer : Observer) (state : GuardState m) (reserved : ReservedKeys m (observerKeys observer))
    (fiber : FiberId) (token : Nat) (request : NativeOp × Val)
    (hr : requestOf m fiber token = some request) :
    let after := (fireObserver (interpOf p table) id exit (m, commands) observer).1
    requestOf after fiber token = some request ∨ InterruptedAt after fiber := by
  cases observer with
  | countdown waiter offered =>
    exact requestOrInterrupted_fireObserver_countdown p table m id exit commands waiter offered state reserved fiber token request hr
  | untrackChild parent =>
    left
    exact (requestOf_modify_view (m.emit [RunEvent.observerFired id (.untrackChild parent)]) parent fiber token
      (fun f => { f with children := f.children.filter fun child => child ≠ id })
      (fun _ => ⟨rfl, rfl, rfl⟩)) ▸ hr
  | resumeAwait waiter offered mode => exact Or.inl hr
  | callback key => exact Or.inl hr
  | dropScopeFinalizer scope key =>
    simp only [fireObserver]
    split <;> exact Or.inl hr
  | raceCallback raceId =>
    simp only [fireObserver]
    repeat' first | exact Or.inl hr | split

theorem interruptedAt_fireObserver_countdown (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (id : FiberId) (exit : ExitV) (commands : List NCmd)
    (waiter : FiberId) (token : Nat) (fiber : FiberId) (interrupted : InterruptedAt m fiber) :
    InterruptedAt (fireObserver (interpOf p table) id exit (m, commands) (.countdown waiter token)).1 fiber := by
  let base := m.emit [RunEvent.observerFired id (.countdown waiter token)]
  have baseInterrupted : InterruptedAt base fiber := interrupted
  cases hw : base.fiber? waiter with
  | none => simpa only [fireObserver, show m.emit _ = base from rfl, hw] using baseInterrupted
  | some w =>
    have wid : w.id = waiter := fiber_id_of_lookup hw
    have hw' : base.fiber? w.id = some w := by simpa only [wid] using hw
    cases hp : w.pending.find? (fun q => q.token = token) with
    | none => simpa only [fireObserver, show m.emit _ = base from rfl, hw, hp] using baseInterrupted
    | some pending =>
      let run := if pending.failFast && !exit.isSuccess && pending.collected.all Exit.isSuccess then
        interruptEach (interpOf p table) waiter ((interpOf p table).stackAnnotations waiter)
          pending.remaining (base, []) else (base, [])
      have runInterrupted : InterruptedAt run.1 fiber := by
        dsimp only [run]; split
        · exact interruptedAt_interruptEach p table waiter _ _ base [] baseInterrupted
        · exact baseInterrupted
      have lookup : ∃ current, run.1.fiber? w.id = some current ∧
          current.running = w.running ∧ current.exit = w.exit := by
        dsimp only [run]; split
        · exact interruptEach_lookup_fields p table waiter _ _ base [] hw'
        · exact ⟨w, hw', rfl, rfl⟩
      obtain ⟨current, currentLookup, _, _⟩ := lookup
      simp only [fireObserver, show m.emit _ = base from rfl, hw, hp]
      cases walk : countdownWalk run.1 pending.remaining (pending.collected ++ [exit]) with
      | mk exits next =>
        cases next with
        | none =>
          exact interruptedAt_restorePending hw' currentLookup
            (fun q => if q.token = token then { q with waitingOn := none, remaining := [], collected := exits } else q)
            baseInterrupted runInterrupted
        | some pair =>
          obtain ⟨next, rest⟩ := pair
          obtain ⟨after, afterLookup, _, _⟩ :=
            fiber_lookup_addObserver_fields run.1 next (.countdown waiter token) currentLookup
          exact interruptedAt_restorePending hw' afterLookup
            (fun q => if q.token = token then
              { q with waitingOn := some next, remaining := rest, collected := exits } else q)
            baseInterrupted (interruptedAt_addObserver next (.countdown waiter token) runInterrupted)

theorem interruptedAt_fireObserver (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (id : FiberId) (exit : ExitV) (commands : List NCmd)
    (observer : Observer) (fiber : FiberId) (interrupted : InterruptedAt m fiber) :
    InterruptedAt (fireObserver (interpOf p table) id exit (m, commands) observer).1 fiber := by
  cases observer with
  | countdown waiter token => exact interruptedAt_fireObserver_countdown p table m id exit commands waiter token fiber interrupted
  | untrackChild parent =>
    exact interruptedAt_modify_view parent
      (fun f => { f with children := f.children.filter fun child => child ≠ id })
      (fun _ => rfl) (fun _ h => h) fiber interrupted
  | resumeAwait waiter token mode => exact interrupted
  | callback key => exact interrupted
  | dropScopeFinalizer scope key =>
    simp only [fireObserver]
    split <;> exact interrupted
  | raceCallback raceId =>
    simp only [fireObserver]
    repeat' first | exact interrupted | split


theorem guardQueue_swap_append (p : NativeEff) (table : RowTable)
    {m : NativeMachine} {front rest : List NCmd} (queue : GuardQueue p table m (front ++ rest)) :
    GuardQueue p table m (rest ++ front) := by
  constructor
  · intro command hc
    exact queue.authority command (by simpa only [List.mem_append, or_comm] using hc)
  · have ho := queue.owners
    simp only [List.filterMap_append, List.nodup_append] at ho ⊢
    exact ⟨ho.2.1, ho.1, fun a ha b hb he => ho.2.2 b hb a ha he.symm⟩
  · constructor
    · intro key hk
      exact queue.keys.below key (by simpa only [List.flatMap_append, List.mem_append, or_comm] using hk)
    · intro fiber token request hr hk
      exact queue.keys.disjoint fiber token request hr
        (by simpa only [List.flatMap_append, List.mem_append, or_comm] using hk)
  · intro command hc
    exact queue.codeSites command (by simpa only [List.mem_append, or_comm] using hc)

theorem fireObserver_append (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (id : FiberId) (exit : ExitV) (front rest : List NCmd) (observer : Observer) :
    fireObserver (interpOf p table) id exit (m, front ++ rest) observer =
      let result := fireObserver (interpOf p table) id exit (m, rest) observer
      (result.1, front ++ result.2) := by
  cases observer <;> simp only [fireObserver]
  all_goals repeat' first
    | rfl
    | (solve | simp_all only [List.append_assoc])
    | split

theorem guardQueue_observe_keys (p : NativeEff) (table : RowTable)
    {m : NativeMachine} {id : FiberId} {exit : ExitV} {observer : Observer} {rest : List NCmd}
    (queue : GuardQueue p table m (.observe id exit observer :: rest)) :
    ReservedKeys m (observerKeys observer) := by
  apply reservedKeys_subset queue.keys
  intro key hk
  exact List.mem_append_left _ hk

theorem guardState_driveStep_observe (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (id : FiberId) (exit : ExitV) (observer : Observer) (rest : List NCmd)
    (state : GuardState m) (queue : GuardQueue p table m (.observe id exit observer :: rest)) :
    letI := evaluatorFor p table
    GuardState (driveStep (interpOf p table) m (.observe id exit observer) rest).1 :=
  guardState_fireObserver p table m id exit [] observer state (guardQueue_observe_keys p table queue)

theorem guardQueue_driveStep_observe (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (id : FiberId) (exit : ExitV) (observer : Observer) (rest : List NCmd)
    (state : GuardState m) (queue : GuardQueue p table m (.observe id exit observer :: rest)) :
    letI := evaluatorFor p table
    let result := driveStep (interpOf p table) m (.observe id exit observer) rest
    GuardQueue p table result.1 result.2 := by
  letI := evaluatorFor p table
  have after := guardQueue_fireObserver p table m id exit rest observer state
    (guardQueue_tail p table queue) (guardQueue_observe_keys p table queue)
  have append := fireObserver_append p table m id exit rest [] observer
  simp only [List.append_nil] at append
  rw [append] at after
  exact guardQueue_swap_append p table after

theorem reservedKeys_driveStep_observe (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (id : FiberId) (exit : ExitV) (observer : Observer) (rest : List NCmd)
    (state : GuardState m) (queue : GuardQueue p table m (.observe id exit observer :: rest))
    (keys : List GuardKey) (reserved : ReservedKeys m keys) :
    letI := evaluatorFor p table
    ReservedKeys (driveStep (interpOf p table) m (.observe id exit observer) rest).1 keys :=
  reservedKeys_fireObserver p table m id exit [] observer state (guardQueue_observe_keys p table queue) keys reserved

theorem requestOrInterrupted_driveStep_observe (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (id : FiberId) (exit : ExitV) (observer : Observer) (rest : List NCmd)
    (state : GuardState m) (queue : GuardQueue p table m (.observe id exit observer :: rest))
    (fiber : FiberId) (token : Nat) (request : NativeOp × Val) (hr : requestOf m fiber token = some request) :
    letI := evaluatorFor p table
    let after := (driveStep (interpOf p table) m (.observe id exit observer) rest).1
    requestOf after fiber token = some request ∨ InterruptedAt after fiber :=
  requestOrInterrupted_fireObserver p table m id exit [] observer state (guardQueue_observe_keys p table queue) fiber token request hr

theorem interruptedAt_driveStep_observe (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (id : FiberId) (exit : ExitV) (observer : Observer) (rest : List NCmd)
    (fiber : FiberId) (interrupted : InterruptedAt m fiber) :
    letI := evaluatorFor p table
    InterruptedAt (driveStep (interpOf p table) m (.observe id exit observer) rest).1 fiber :=
  interruptedAt_fireObserver p table m id exit [] observer fiber interrupted


theorem registrationQueue_interruptEach (p : NativeEff) (table : RowTable)
    (who : FiberId) (extra : ReasonAnnotations Ann) (targets : List FiberId)
    (m : NativeMachine) (commands : List NCmd) (registration : RegistrationQueue commands) :
    RegistrationQueue (interruptEach (interpOf p table) who extra targets (m, commands)).2 := by
  induction targets generalizing m commands with
  | nil => exact registration
  | cons target targets ih =>
    cases ht : m.fiber? target with
    | none => simpa only [interruptEach, List.foldl_cons, ht] using ih m commands registration
    | some f =>
      let next := (m.update (interruptRecord (interpOf p table) (some who) extra f).1).emit
        [RunEvent.interruptRecorded (some who) target]
      let pending := commands ++ (if (interruptRecord (interpOf p table) (some who) extra f).2 then
        [.evaluate target] else [])
      have registered : RegistrationQueue pending := by
        apply registrationQueue_append registration
        split
        · exact ⟨True.intro, True.intro⟩
        · trivial
      simpa only [interruptEach, List.foldl_cons, ht] using ih next pending registered

theorem registrationQueue_fireObserver (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (id : FiberId) (exit : ExitV) (commands : List NCmd)
    (observer : Observer) (registration : RegistrationQueue commands) :
    RegistrationQueue (fireObserver (interpOf p table) id exit (m, commands) observer).2 := by
  cases observer with
  | countdown waiter token =>
    simp only [fireObserver]
    split
    · exact registration
    · rename_i w hw
      split
      · exact registration
      · rename_i pending hp
        let base := m.emit [RunEvent.observerFired id (.countdown waiter token)]
        let run := if pending.failFast && !exit.isSuccess && pending.collected.all Exit.isSuccess then
          interruptEach (interpOf p table) waiter ((interpOf p table).stackAnnotations waiter)
            pending.remaining (base, []) else (base, [])
        have nested : RegistrationQueue run.2 := by
          dsimp only [run]; split
          · exact registrationQueue_interruptEach p table waiter _ _ base [] True.intro
          · trivial
        cases walk : countdownWalk run.1 pending.remaining (pending.collected ++ [exit]) with
        | mk exits next =>
          cases next with
          | none =>
            exact registrationQueue_append (registrationQueue_append registration nested)
              ⟨True.intro, True.intro⟩
          | some pair => exact registrationQueue_append registration nested
  | raceCallback raceId =>
    simp only [fireObserver]
    split
    · exact registration
    · split
      · apply registrationQueue_append registration
        split
        · trivial
        · exact ⟨True.intro, True.intro⟩
      · exact registration
  | resumeAwait waiter token mode =>
    exact registrationQueue_append registration ⟨True.intro, True.intro⟩
  | untrackChild parent => exact registration
  | callback key => exact registration
  | dropScopeFinalizer scope key =>
    simp only [fireObserver]
    split <;> exact registration

theorem registrationQueue_driveStep_observe (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (id : FiberId) (exit : ExitV) (observer : Observer) (rest : List NCmd)
    (registration : RegistrationQueue (.observe id exit observer :: rest)) :
    letI := evaluatorFor p table
    RegistrationQueue (driveStep (interpOf p table) m (.observe id exit observer) rest).2 := by
  exact registrationQueue_append
    (registrationQueue_fireObserver p table m id exit [] observer True.intro)
    (registrationQueue_tail registration)










end Effect4.Program.Guard
