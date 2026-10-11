import Effect4.Laws.Program.FinalizerTransfer

/-!
# Finalizer accounting for native commands

Concept: scope-lifetime-finalization, R11, at most one start per registration.
These command cases serve `Program.FinalizerRun.funded_reachable` and `Atomic.cleans_once`.
The driver uses actual table lookups, observer edits, registrations and evaluator results.
Reach: arbitrary commands under the existing distinct-identity invariant.
No statement establishes source-use uniqueness, log provenance, progress or host agreement.
-/

set_option autoImplicit false
namespace Effect4.Program.FinalizerTransfer
open Effect4 Effect4.Machine Effect4.Machine.FinalizerCredits
open Effect4.Machine.ForkLedger.Invariant Effect4.Program.Guard

/-- An observer records no finalizer start and retains every frame credit. -/
theorem observer_same (choose : EffName → Bool) (interp : Native.NInterp) (id : FiberId)
    (exit : ExitV) (acc : NativeMachine × List Native.NCmd) (observer : Observer) (ok : Ok acc.1) :
    Same choose acc.1 (fireObserver interp id exit acc observer).1 := by
  have emitted := same_emit choose acc.1 [.observerFired id observer] rfl rfl
  unfold fireObserver
  dsimp only
  split
  · exact emitted
  · rename_i parent
    exact emitted.trans (same_modify choose
      (acc.1.emit [.observerFired id (.untrackChild parent)]) ok.idsUnique parent
      (fun f => { f with children := f.children.filter fun c => c ≠ id })
      (fun _ => rfl) (fun _ => rfl))
  · split <;> exact emitted
  · rename_i waiter token
    split
    · exact emitted
    · rename_i w found
      split
      · exact emitted
      · rename_i pending pendingFound
        let before := acc.1.emit [.observerFired id (.countdown waiter token)]
        let middle := if pending.failFast && !exit.isSuccess && pending.collected.all Exit.isSuccess then
          interruptEach interp waiter (interp.stackAnnotations waiter) pending.remaining (before, [])
          else (before, [])
        have kept : Same choose acc.1 middle.1 ∧ Ok middle.1 := by
          unfold middle
          split
          · exact ⟨emitted.trans (same_interruptEach choose interp waiter
              (interp.stackAnnotations waiter) pending.remaining (before, []) ok),
              Native.interruptEach_ok interp waiter (interp.stackAnnotations waiter)
                pending.remaining (before, []) ok⟩
          · exact ⟨emitted, ok⟩
        have atOld : atFiber choose acc.1 w.id = fiberCredits choose w := by
          have key := RunMachine.id_of_fiber? found
          rw [key]
          exact atFiber_found choose _ waiter w found
        split
        · apply kept.1.trans
          apply same_update_view choose middle.1 kept.2.idsUnique
          change atFiber choose middle.1 w.id = fiberCredits choose w
          rw [kept.1.2.1]
          exact atOld
        · rename_i exits next rest walked
          let edit (g : NFiber) : NFiber :=
            { g with observers := g.observers ++ [.countdown waiter token] }
          have changed := same_modify choose middle.1 kept.2.idsUnique next edit
            (fun _ => rfl) (fun _ => rfl)
          apply (kept.1.trans changed).trans
          apply same_update_view choose (middle.1.modify next edit) (modify_ok kept.2 next edit).idsUnique
          change atFiber choose (middle.1.modify next edit) w.id = fiberCredits choose w
          rw [changed.2.1, kept.1.2.1]
          exact atOld
  · split
    · exact emitted
    · rename_i race found
      split
      · exact emitted.trans (same_emit choose _ [.raceSettled _ _] rfl rfl)
      · exact emitted
  · exact emitted.trans (same_emit choose _ [.callback _ exit] rfl rfl)

/-- Publishing a fiber retains its credit, and clearing it can only discard credit. -/
theorem exit_funded (choose : EffName → Bool) (interp : Native.NInterp)
    (m : NativeMachine) (f : NFiber) (exit : ExitV) (ok : Ok m)
    (stored : atFiber choose m f.id = fiberCredits choose f) (funded : Funded choose m) :
    Funded choose (exitFiber interp m f exit).1 := by
  unfold exitFiber
  split
  · unfold exitFiber.exitInterruptChildren
    dsimp only
    apply (same_emit choose _ [.childrenInterrupted f.id f.children] rfl rfl).funded
    apply (same_update_view choose m ok.idsUnique _ ?_).funded funded
    exact stored
  · unfold exitFiber.exitStore
    dsimp only
    have published := (same_update_view choose m ok.idsUnique (f.publish exit) stored).funded funded
    have after := (same_emit choose (m.update (f.publish exit)) [.exited f.id exit] rfl rfl).funded published
    split
    · exact update_funded_le choose
        ((m.update (f.publish exit)).emit [.exited f.id exit])
        (update_ok ok (f.publish exit)).idsUnique ((f.publish exit).cleared interp)
        (Nat.zero_le _) after
    · exact after

/-- A lookup supplies the stored credit at its row's own identity. -/
theorem found_credit (choose : EffName → Bool) (m : NativeMachine) (id : FiberId)
    (f : NFiber) (found : m.fiber? id = some f) : atFiber choose m f.id = fiberCredits choose f := by
  rw [RunMachine.id_of_fiber? found]
  exact atFiber_found choose m id f found

/-- A neutral iteration carries its stored credit through the driver's settlement. -/
theorem settle_view (choose : EffName → Bool) (m : NativeMachine) (next : Native.NIter)
    (ok : Ok next.machine) (funded : Funded choose m) (same : Same choose m next.machine)
    (stored : atFiber choose m next.fiber.id = fiberCredits choose next.fiber)
    (id : FiberId) (rest : List Native.NCmd) : Funded choose (settle id rest next).1 := by
  apply settle_balanced choose m next ok.idsUnique funded _ id rest
  unfold Balanced
  rw [same.1, same.2.1, same.2.2.1, same.2.2.2, stored]
  exact Nat.le_refl _

/-- Every actual native command respects finalizer registration custody. -/
theorem command_funded (choose : EffName → Bool) (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (cmd : Native.NCmd) (rest : List Native.NCmd)
    (ok : Ok m) (funded : Funded choose m) :
    letI := evaluatorFor p table
    Funded choose (driveStep (interpOf p table) m cmd rest).1 := by
  letI := evaluatorFor p table
  cases cmd with
  | evaluate id =>
    simp only [driveStep]
    split
    · exact funded
    · rename_i f found
      split
      · exact funded
      · apply (same_emit choose _ [.started id] rfl rfl).funded
        apply (same_update_view choose m ok.idsUnique _ ?_).funded funded
        exact found_credit choose m id f found
  | loop id y =>
    simp only [driveStep]
    split
    · exact funded
    · rename_i f found
      exact settle_balanced choose m _ (Native.iteration_ok p table m f y ok).idsUnique funded
        ((iteration_kept choose p table m f y ok).balanced
          (by simpa only [RunMachine.id_of_fiber? found] using found)) id rest
  | deliver id y =>
    simp only [driveStep]
    split
    · exact funded
    · rename_i f found
      exact settle_balanced choose m _ (Native.evaluateNative_ok p table m f y ok).idsUnique funded
        ((evaluate_kept choose p table m f y ok).balanced
          (by simpa only [RunMachine.id_of_fiber? found] using found)) id rest
  | resume id token answer =>
    simp only [driveStep]
    split
    · exact funded
    · rename_i f found
      split
      · split
        · apply (same_emit choose _ [.resumedWith id token answer] rfl rfl).funded
          apply (same_update_view choose m ok.idsUnique _ ?_).funded funded
          exact found_credit choose m id f found
        · exact funded
      · exact funded
  | launch raceId =>
    simp only [driveStep]
    split
    · exact funded
    · split
      · exact funded
      · rename_i program more _
        split
        · exact funded
        · split
          · exact funded
          · rename_i host found
            apply (same_emit choose _ [.raceLaunched raceId _] rfl rfl).funded
            exact (same_spawn choose (interpOf p table) m host program
              ⟨true, true, .interruptible⟩ _).funded funded
  | enrollRace raceId child =>
    simp only [driveStep]
    split
    · rename_i race c raceFound childFound
      let registered := m.updateRace { race with state := { race.state with live := race.state.live ++ [child] } }
      split
      · exact (observer_same choose (interpOf p table) child _ (registered, [])
          (.raceCallback raceId) ok).funded funded
      · exact (same_modify choose registered ok.idsUnique child
          (fun f => { f with observers := f.observers ++ [.raceCallback raceId] })
          (fun _ => rfl) (fun _ => rfl)).funded funded
    · exact funded
  | registrationDone raceId y =>
    simp only [driveStep]
    split
    · exact funded
    · split
      · exact funded
      · rename_i f found
        split
        · apply settle_view choose m _ ok funded (.refl choose m) _ _ rest
          exact found_credit choose m _ f found
        · apply settle_view choose m _ ok funded
            (same_emit choose _ [.parkedOn f.id _] rfl rfl) _ _ rest
          exact found_credit choose m _ f found
  | interruptTarget target who extra =>
    simp only [driveStep]
    split
    · exact funded
    · rename_i f found
      exact (same_emit choose _ [.interruptRecorded who target] rfl rfl).funded
        ((same_interruptUpdate choose (interpOf p table) m ok.idsUnique target f found who extra).funded funded)
  | afterInterrupt host y kind =>
    simp only [driveStep]
    split
    · exact funded
    · rename_i f found
      apply settle_view choose m _ ok funded (.refl choose m) _ _ rest
      exact found_credit choose m host f found
  | raceCancel raceId host y remaining visited =>
    simp only [driveStep]
    repeat' split
    all_goals exact funded
  | trackChild parent child =>
    simp only [driveStep]
    split
    · exact funded
    · split
      · exact funded
      · have first := same_modify choose m ok.idsUnique parent
          (fun f => { f with children := f.children ++ [child] }) (fun _ => rfl) (fun _ => rfl)
        apply (same_modify choose _ (modify_ok ok parent _).idsUnique child
          (fun f => { f with observers := f.observers ++ [.untrackChild parent] })
          (fun _ => rfl) (fun _ => rfl)).funded (first.funded funded)
  | observe id exit observer =>
    exact (observer_same choose (interpOf p table) id exit (m, []) observer ok).funded funded
  | exitDone id =>
    simp only [driveStep]
    split
    · exact funded
    · exact update_funded_le choose m ok.idsUnique _ (Nat.zero_le _) funded
  | closeParAwait host y fibers =>
    simp only [driveStep]
    split
    · exact funded
    · rename_i f found
      apply settle_view choose m _ ok funded (.refl choose m) _ _ rest
      exact found_credit choose m host f found
  | link mode scope target who extra =>
    exact (same_linkScope choose (interpOf p table) m ok.idsUnique mode scope target who extra).funded funded
  | finish id exit =>
    simp only [driveStep]
    split
    · exact funded
    · rename_i f found
      exact exit_funded choose (interpOf p table) m { f with running := false } exit ok
        (found_credit choose m id f found) funded
  | drainDue =>
    exact (same_drainOwed choose
      { m with state := ((interpOf p table).dueResumes m.state).2 } ok
      ((interpOf p table).dueResumes m.state).1).funded funded
  | wake list phase => exact funded

/-- The outer interrupt edit records events before updating the selected row. -/
theorem interrupt_same (choose : EffName → Bool) (interp : Native.NInterp)
    (m : NativeMachine) (ok : Ok m) (who : Option FiberId) (extra : ReasonAnnotations Ann)
    (target : FiberId) (f : NFiber) (found : m.fiber? target = some f) :
    Same choose m (Lift.interruptEdit interp m who extra target f) := by
  unfold Lift.interruptEdit
  dsimp only
  split
  · let before := (m.emit [.interruptRecorded who target]).emit [.interruptDeferred target]
    exact ((same_emit choose m [.interruptRecorded who target] rfl rfl).trans
      (same_emit choose _ [.interruptDeferred target] rfl rfl)).trans
      (same_interruptUpdate choose interp before ok.idsUnique target f found who extra)
  · let before := m.emit [.interruptRecorded who target]
    exact (same_emit choose m [.interruptRecorded who target] rfl rfl).trans
      (same_interruptUpdate choose interp before ok.idsUnique target f found who extra)

/-- The existing allocation invariant supplies the distinct identities used by credit sums. -/
def Holds (choose : EffName → Bool) (m : NativeMachine) : Prop := Ok m ∧ Funded choose m

/-- Every edit outside the command loop retains the same two actual machine invariants. -/
theorem edits (choose : EffName → Bool) (interp : Native.NInterp) :
    Lift.MachineEdits interp (Holds choose) where
  drain := by
    intro m owner f h found
    refine ⟨(ForkLedger.Invariant.edits interp).drain m owner f h.1 found, ?_⟩
    exact (same_update_view choose m h.1.idsUnique
      { f with dispatcher := f.dispatcher.drain.2 } (found_credit choose m owner f found)).funded h.2
  ran := by
    intro m owner task h
    exact ⟨h.1, (same_emit choose m [.ranTask owner task] rfl rfl).funded h.2⟩
  yield := by
    intro m id verdict h
    exact ⟨modify_ok h.1 id _, (same_modify choose m h.1.idsUnique id
      (fun f => { f with yieldOverride := some verdict }) (fun _ => rfl) (fun _ => rfl)).funded h.2⟩
  interrupt := by
    intro m who extra target f h found
    exact ⟨interruptEdit_ok interp h.1 who extra target f,
      (interrupt_same choose interp m h.1 who extra target f found).funded h.2⟩
  middleware := fun _ h => h
  clock := fun _ _ h _ => h
  owed := by
    intro m owed h
    exact ⟨drainOwed_ok m [owed] h.1, (same_drainOwed choose m h.1 [owed]).funded h.2⟩
  prepare := fun _ _ _ _ h => h

/-- All decisions and every finite command budget preserve finalizer registration custody. -/
theorem stepped (choose : EffName → Bool) (p : NativeEff) (table : RowTable)
    (fuel : Nat) (m : NativeMachine) (decision : NativeDecision) (h : Holds choose m) :
    Holds choose (steppedBy p fuel table m decision) := by
  letI := evaluatorFor p table
  exact Lift.machineFact_stepDecision (interpOf p table) (Holds choose)
    (fun m cmd rest _ h => ⟨Native.driveStep_ok p table m cmd rest h.1,
      command_funded choose p table m cmd rest h.1 h.2⟩)
    (edits choose (interpOf p table)) fuel m decision h

end Effect4.Program.FinalizerTransfer
