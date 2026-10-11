import Effect4.Laws.Program.ReleaseCustody.CommandStoreDebit
import Effect4.Laws.Program.ReleaseCustody.Outside

/-!
Concept: scope-lifetime-finalization R11, serving `ReleaseCustody.Execution.history`.
Consumers: countdown observer and native interrupt-action custody.
Nested interruptions reduce off-owner credit before the saved waiter record is installed once.
These local bounds establish no history closure, source uniqueness or progress.
-/
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
namespace Effect4.Program.ReleaseCustody.CommandDebit
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Guard
open Effect4.Program.ReleaseCustody.Control

/-- Interrupting a list changes neither counted release events nor queued answer credit.
The off-owner bound supports reinstalling a waiter retained before these interruptions. -/
theorem interrupt_each (root : NativeEff) (table : RowTable) (q : List Nat)
    (owner who : FiberId) (extra : ReasonAnnotations Ann) (targets : List FiberId)
    (m : NativeMachine) (commands : List Command) (unique : (m.fibers.map RunFiber.id).Nodup) :
    let out := interruptEach (interpOf root table) who extra targets (m, commands)
    outsideCredits q owner out.1 ≤ outsideCredits q owner m ∧
    out.1.fibers.map RunFiber.id = m.fibers.map RunFiber.id ∧
    out.1.trace.countP (ReleaseTrace.releaseAt q) = m.trace.countP (ReleaseTrace.releaseAt q) ∧
    out.1.trace.countP (ReleaseTrace.registeredAt q) = m.trace.countP (ReleaseTrace.registeredAt q) ∧
    (out.2.map (commandCredits q)).sum = (commands.map (commandCredits q)).sum := by
  induction targets generalizing m commands with
  | nil => exact ⟨Nat.le_refl _, rfl, rfl, rfl, rfl⟩
  | cons target targets ih =>
    cases found : m.fiber? target with
    | none => simpa only [interruptEach, List.foldl_cons, found] using ih m commands unique
    | some fiber =>
      let next := interruptRecord (interpOf root table) (some who) extra fiber
      let base := (m.update next.1).emit [RunEvent.interruptRecorded (some who) target]
      let queued := commands ++ (if next.2 then [.evaluate target] else [])
      have ids : base.fibers.map RunFiber.id = m.fibers.map RunFiber.id :=
        RunMachine.update_keeps_ids _ _
      have debit : outsideCredits q owner base ≤ outsideCredits q owner m :=
        outside_update_le q m owner fiber next.1 unique
          (by simpa only [fiber_id_of_lookup found] using found)
          (interruptRecord_id root table (some who) extra fiber)
          (interrupt_record root table q (some who) extra fiber)
      have starts : base.trace.countP (ReleaseTrace.releaseAt q) = m.trace.countP (ReleaseTrace.releaseAt q) := by
        rw [RunMachine.emit_trace, List.countP_append]
        exact Nat.add_zero _
      have registrations : base.trace.countP (ReleaseTrace.registeredAt q) =
          m.trace.countP (ReleaseTrace.registeredAt q) := by
        rw [RunMachine.emit_trace, List.countP_append]
        exact Nat.add_zero _
      have queuedCredit : (queued.map (commandCredits q)).sum = (commands.map (commandCredits q)).sum := by
        unfold queued
        split <;> simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil,
          List.sum_cons, List.sum_nil, commandCredits, Nat.add_zero]
      have rest := ih base queued (by rw [ids]; exact unique)
      simp only [interruptEach, List.foldl_cons, found]
      exact ⟨Nat.le_trans rest.1 debit, rest.2.1.trans ids, rest.2.2.1.trans starts,
        rest.2.2.2.1.trans registrations, rest.2.2.2.2.trans queuedCredit⟩

/-- Administrative fiber metadata cannot increase off-owner credit. -/
theorem modify_outside (q : List Nat) (m : NativeMachine) (owner target : FiberId)
    (edit : Fiber → Fiber) (unique : (m.fibers.map RunFiber.id).Nodup)
    (key : ∀ fiber, (edit fiber).id = fiber.id)
    (debit : ∀ fiber, fiberCredits q (edit fiber) ≤ fiberCredits q fiber) :
    outsideCredits q owner (m.modify target edit) ≤ outsideCredits q owner m := by
  unfold RunMachine.modify
  split
  · exact Nat.le_refl _
  · rename_i fiber found
    exact outside_update_le q m owner fiber (edit fiber) unique
      (by simpa only [fiber_id_of_lookup found] using found) (key fiber) (debit fiber)

/-- Native countdown completion shapes create no foreign finalizer credit. -/
theorem countdown_zero (root : NativeEff) (table : RowTable) (q : List Nat)
    (resume : Resume EffName) (exits : List ExitV)
    (shape : resume = .exitsValue ∨ resume = .void ∨ ∃ exit, resume = .continueWith (.restore exit)) :
    currentCredits q (countdownPark.resumePrim (core := frameCore) (interpOf root table) resume exits) = 0 := by
  rcases shape with rfl | rfl | ⟨exit, rfl⟩
  · rfl
  · rfl
  · rfl

/-- Countdown callbacks reinstall the saved waiter after nested interruptions exactly once. -/
theorem countdown_observer (root : NativeEff) (table : RowTable) (q : List Nat) (m : NativeMachine)
    (id : FiberId) (exit : ExitV) (waiter : FiberId) (token : Nat) (commands rest : List Command)
    (unique : (m.fibers.map RunFiber.id).Nodup) (pendingShape : Execution.PendingShape m)
    (held : Funded q m (commands ++ rest)) :
    let out := fireObserver (interpOf root table) id exit (m, commands) (.countdown waiter token)
    Funded q out.1 (out.2 ++ rest) := by
  let base := m.emit [RunEvent.observerFired id (.countdown waiter token)]
  have before : Funded q base (commands ++ rest) := emit q m _ held _ rfl rfl
  simp only [fireObserver, show m.emit _ = base from rfl]
  cases found : base.fiber? waiter with
  | none => exact before
  | some fiber =>
    simp only []
    cases pending : fiber.pending.find? (fun p => p.token = token) with
    | none => exact before
    | some park =>
      simp only []
      have shape := pendingShape fiber (List.mem_of_find?_eq_some found) park
        (List.mem_of_find?_eq_some pending)
      have key : fiber.id = waiter := fiber_id_of_lookup found
      have partition := outside_split q base waiter fiber unique found
      have restore (after : NativeMachine) (links : CommandStacks.StackLinks base after)
          (afterUnique : (after.fibers.map RunFiber.id).Nodup)
          (debit : outsideCredits q waiter after ≤ outsideCredits q waiter base)
          (starts : after.trace.countP (ReleaseTrace.releaseAt q) = base.trace.countP (ReleaseTrace.releaseAt q))
          (registered : after.trace.countP (ReleaseTrace.registeredAt q) = base.trace.countP (ReleaseTrace.registeredAt q))
          (next : Fiber) (key : next.id = waiter) (credit : fiberCredits q next = fiberCredits q fiber)
          (queued : List Command)
          (cost : (queued.map (commandCredits q)).sum ≤ ((commands ++ rest).map (commandCredits q)).sum) :
          Funded q (after.update next) queued := by
        obtain ⟨stored, seen, _⟩ := links waiter fiber found
        have installed := outside_install q after waiter stored next afterUnique seen key
        unfold Funded at before ⊢
        change after.trace.countP (ReleaseTrace.releaseAt q) + machineCredits q (after.update next) +
          (queued.map (commandCredits q)).sum ≤ after.trace.countP (ReleaseTrace.registeredAt q)
        rw [installed, credit, starts, registered]
        omega
      generalize result : (if park.failFast && !exit.isSuccess && park.collected.all Exit.isSuccess then
          interruptEach (interpOf root table) waiter ((interpOf root table).stackAnnotations waiter)
            park.remaining (base, []) else (base, [])) = out
      have facts : outsideCredits q waiter out.1 ≤ outsideCredits q waiter base ∧
          out.1.fibers.map RunFiber.id = base.fibers.map RunFiber.id ∧
          out.1.trace.countP (ReleaseTrace.releaseAt q) = base.trace.countP (ReleaseTrace.releaseAt q) ∧
          out.1.trace.countP (ReleaseTrace.registeredAt q) = base.trace.countP (ReleaseTrace.registeredAt q) ∧
          (out.2.map (commandCredits q)).sum = 0 := by
        rw [← result]
        split
        · exact interrupt_each root table q waiter waiter _ park.remaining base [] unique
        · exact ⟨Nat.le_refl _, rfl, rfl, rfl, rfl⟩
      have links : CommandStacks.StackLinks base out.1 := by
        rw [← result]
        split
        · exact CommandStacks.interruptEach_links root table waiter _ park.remaining base []
        · exact .refl base
      have afterUnique : (out.1.fibers.map RunFiber.id).Nodup := by rw [facts.2.1]; exact unique
      obtain ⟨outMachine, nested⟩ := out
      dsimp only at facts links afterUnique ⊢
      cases walked : countdownWalk outMachine park.remaining (park.collected ++ [exit]) with
      | mk exits next =>
        cases next with
        | none =>
          refine restore outMachine links afterUnique facts.1 facts.2.2.1 facts.2.2.2.1
            {fiber with pending := fiber.pending.map (fun p => if p.token = token then
              {p with waitingOn := none, remaining := [], collected := exits} else p)}
            key rfl _ ?_
          simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons,
            List.sum_nil, commandCredits, countdown_zero root table q park.resumeWith exits shape,
            facts.2.2.2.2, Nat.add_zero]
          exact Nat.le_refl _
        | some pair =>
          obtain ⟨next, remaining⟩ := pair
          let edit : Fiber → Fiber := fun f => {f with observers := f.observers ++ [.countdown waiter token]}
          have linked := links.trans (CommandStacks.modify_links outMachine next edit (fun _ => rfl) (fun _ => rfl))
          have smaller := modify_outside q outMachine waiter next edit afterUnique (fun _ => rfl) (fun _ => Nat.le_refl _)
          refine restore (outMachine.modify next edit) linked (by rw [modify_ids]; exact afterUnique)
            (Nat.le_trans smaller facts.1)
            (by rw [RunMachine.modify_trace]; exact facts.2.2.1)
            (by rw [RunMachine.modify_trace]; exact facts.2.2.2.1)
            {fiber with pending := fiber.pending.map (fun p => if p.token = token then
              {p with waitingOn := some next, remaining := remaining, collected := exits} else p)}
            key rfl _ ?_
          simp only [List.map_append, List.sum_append, facts.2.2.2.2, Nat.add_zero]
          exact Nat.le_refl _

/-- Every native observer retains release funding, including nested countdown interruptions. -/
theorem fire_observer (root : NativeEff) (table : RowTable) (q : List Nat) (m : NativeMachine)
    (id : FiberId) (exit : ExitV) (observer : Observer) (commands rest : List Command)
    (fibers : (m.fibers.map RunFiber.id).Nodup) (races : (m.races.map Race.id).Nodup)
    (scopes : (m.state.scopes.entries.map ScopeEntry.key).Nodup)
    (pending : Execution.PendingShape m) (held : Funded q m (commands ++ rest)) :
    let out := fireObserver (interpOf root table) id exit (m, commands) observer
    Funded q out.1 (out.2 ++ rest) := by
  cases observer with
  | countdown waiter token => exact countdown_observer root table q m id exit waiter token commands rest fibers pending held
  | raceCallback race => exact race_observer root table q m id exit race commands rest races held
  | resumeAwait waiter token mode =>
    apply queue q _ (commands ++ rest) _ (emit q m _ held [RunEvent.observerFired id (.resumeAwait waiter token mode)] rfl rfl)
    have answer : currentCredits q ((interpOf root table).exitValue exit mode) = 0 := by
      cases mode
      · rfl
      · exact Evaluation.exit_credits q exit
    simp only [fireObserver, List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, commandCredits, answer, Nat.add_zero]
    exact Nat.le_refl _
  | untrackChild parent =>
    exact modify q _ parent (fun f => {f with children := f.children.filter (fun child => child ≠ id)})
      (commands ++ rest) (emit q m _ held [RunEvent.observerFired id (.untrackChild parent)] rfl rfl)
      fibers (fun _ => rfl) (fun _ => Nat.le_refl _)
  | dropScopeFinalizer scope key =>
    let base := m.emit [RunEvent.observerFired id (.dropScopeFinalizer scope key)]
    have before : Funded q base (commands ++ rest) := emit q m _ held _ rfl rfl
    have drop : (interpOf root table).dropFinalizer scope key base.state =
        match base.state.scopes.entryAt scope with
        | none => none
        | some _ => some {base.state with scopes := base.state.scopes.removeFinalizer scope key} := rfl
    simp only [fireObserver, show m.emit _ = base from rfl, drop]
    cases found : base.state.scopes.entryAt scope with
    | none => exact before
    | some entry => exact state q base _ _ before (ScopeTransfer.remove q base.state.scopes scope key scopes)
  | callback key =>
    exact emit q _ _ (emit q m _ held [RunEvent.observerFired id (.callback key)] rfl rfl)
      [RunEvent.callback key exit] rfl rfl

/-- The actual observe command appends the observer's funded nested work before its suffix. -/
theorem observe (root : NativeEff) (table : RowTable) (q : List Nat) (m : NativeMachine)
    (id : FiberId) (exit : ExitV) (observer : Observer) (rest : List Command)
    (fibers : (m.fibers.map RunFiber.id).Nodup) (races : (m.races.map Race.id).Nodup)
    (scopes : (m.state.scopes.entries.map ScopeEntry.key).Nodup)
    (pending : Execution.PendingShape m) (held : Funded q m (.observe id exit observer :: rest)) :
    letI := evaluatorFor root table
    let out := driveStep (interpOf root table) m (.observe id exit observer) rest
    Funded q out.1 out.2 :=
  fire_observer root table q m id exit observer [] rest fibers races scopes pending (tail q m _ rest held)

end Effect4.Program.ReleaseCustody.CommandDebit
