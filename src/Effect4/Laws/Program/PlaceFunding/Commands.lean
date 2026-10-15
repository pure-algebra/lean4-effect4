import Effect4.Laws.Program.PlaceFunding.Transfer

/-!
Concept: scope-lifetime-finalization, R11, and reactive-scheduling.
Question: shared place funding serves Atomic.Cleanup.log_debits and the existing stack ledger run claim.
Reach: actual machine rows, source permissions for imported code, and local evaluator debit.
The command instance assigns zero weight to races, pending commands, and detached tasks.
External step allowances remain explicit. The saved-stack instance uses zero allowance and unrestricted code.
These laws establish no instance evaluator debit, source admission, progress, or host agreement.
-/
set_option autoImplicit false
namespace Effect4.Program.PlaceFunding
open Effect4 Effect4.Machine Effect4.Program
open Effect4.Machine.ForkLedger.Invariant Effect4.Program.Guard

variable {L : Ledger} {Free : NCode → Prop}

theorem exit_balance_at (control : Control L Free) (events : Events L)
    (interp : Native.NInterp) (admin : Administration L Free interp)
    (m : NativeMachine) (old fiber : NFiber) (exit : ExitV) (ok : Ok m)
    (found : m.fiber? old.id = some old) (key : fiber.id = old.id) (weight : L.fiber fiber ≤ L.fiber old) :
    L.Balanced m [] [] (exitFiber interp m fiber exit).1 [] [] := by
  unfold exitFiber
  split
  · unfold exitFiber.exitInterruptChildren
    dsimp only
    let next : NFiber := {fiber with
        finalizing := some exit
        running := false
        frame := {fiber.frame with
          deferredInterrupt := false
          current := .onSuccess (interp.interruptAllCode fiber.children) (interp.restoreName exit)}}
    have localWeight := control.replace_changed fiber next rfl (admin.children fiber.children exit) rfl (Nat.le_refl _)
    apply (control.update m old next ok found key (Nat.le_trans localWeight weight)).trans L
    exact events.emit _ [.childrenInterrupted fiber.id fiber.children]
      (by intro event member; have same := List.mem_singleton.mp member; subst event; rfl)
  · unfold exitFiber.exitStore
    dsimp only
    have publishedWeight := control.metadata fiber (fiber.publish exit) rfl rfl rfl (Nat.le_refl _)
    have published := control.update m old (fiber.publish exit) ok found key
      (Nat.le_trans publishedWeight weight)
    have emitted := events.emit (m.update (fiber.publish exit)) [.exited fiber.id exit]
      (by intro event member; have same := List.mem_singleton.mp member; subst event; rfl)
    have before := published.trans L emitted
    split
    · have stored : ((m.update (fiber.publish exit)).emit [.exited fiber.id exit]).fiber? fiber.id = some (fiber.publish exit) := by
        change (m.update (fiber.publish exit)).fiber? fiber.id = some (fiber.publish exit)
        apply RunMachine.fiber?_update_self
        exact ⟨old, RunMachine.mem_of_fiber? found, key.symm⟩
      exact before.trans L (control.update _ (fiber.publish exit) ((fiber.publish exit).cleared interp)
        (emit_ok (update_ok ok (fiber.publish exit)) _) stored rfl
        (control.clear_changed (fiber.publish exit) ((fiber.publish exit).cleared interp) rfl rfl rfl (Nat.le_refl _)))
    · exact before

/-- The previous zero-place exit uses the same transfer. -/
theorem exit_balance (control : Control L Free) (_quiet : NoQueue L) (events : Events L)
    (interp : Native.NInterp) (admin : Administration L Free interp)
    (m : NativeMachine) (old fiber : NFiber) (exit : ExitV) (ok : Ok m)
    (found : m.fiber? old.id = some old) (key : fiber.id = old.id) (weight : L.fiber fiber ≤ L.fiber old) :
    L.Balanced m [] [] (exitFiber interp m fiber exit).1 [] [] :=
  exit_balance_at control events interp admin m old fiber exit ok found key weight

/-- An admitted zero-weight entrant uses the original launch producer. -/
theorem NoQueue.launch_balance (root : NativeEff) (table : RowTable)
    (control : Control L Free) (quiet : NoQueue L) (events : Events L)
    (m : NativeMachine) (raceId : Nat) (rest : List Native.NCmd) (ok : Ok m)
    (free : ∀ race code more, m.race? raceId = some race → race.programs = code :: more → Free code) :
    letI := evaluatorFor root table
    L.Balanced m [] [] (driveStep (interpOf root table) m (.launch raceId) rest).1 [] [] := by
  letI := evaluatorFor root table
  simp only [driveStep]
  split
  · exact Nat.le_refl _
  · rename_i race found
    split
    · exact Nat.le_refl _
    · rename_i code more programs
      split
      · exact Nat.le_refl _
      · split
        · exact Nat.le_refl _
        · rename_i host hostFound
          have born := spawn_balance_at control events (interpOf root table) m host code
            ⟨true, true, .interruptible⟩ (race.nextSite.getD []) (free race code more found programs)
          have replaced := (race_transfer quiet
            (launchEntrant (interpOf root table) raceId m host code (race.nextSite.getD [])).1
            {race with programs := more, nextSite := race.nextSite.map (fun site => site ++ [1])}).2
            (launchEntrant_ok (interpOf root table) ok raceId host code (race.nextSite.getD []))
          exact (born.trans L replaced.2).trans L
            (events.emit _ [.raceLaunched raceId _]
              (by intro event member; have same := List.mem_singleton.mp member; subst event; rfl))

theorem command_funded_at {cap : Nat} (root : NativeEff) (table : RowTable)
    (control : Control L Free) (quiet : NoPending L) (events : Events L)
    (stores : StoreHooks L (interpOf root table)) (admin : Administration L Free (interpOf root table))
    (P : NativeMachine → Prop) (charge : NativeMachine → FiberId → Bool → Nat)
    (evaluation : Evaluation L P root table charge)
    (m : NativeMachine) (cmd : Native.NCmd) (rest : List Native.NCmd)
    (ok : Ok m) (permission : P m)
    (reply : ∀ owner token code, cmd = .resume owner token code → Free code)
    (R : NativeMachine → Prop)
    (raceStable : ∀ before after : NativeMachine,
      after.races.map Race.id = before.races.map Race.id → R before → R after)
    (raceStep : ∀ (machine : NativeMachine) (key : Nat) (old next : Race EffName EffThunk Val Err Defect FiberId Ann),
      machine.race? key = some old → next.id = old.id → next.programs = old.programs → R machine →
      Transfer (L := L) machine (machine.updateRace next) (.updateRace next))
    (raceHeld : R m)
    (launch : ∀ raceId, cmd = .launch raceId →
      letI := evaluatorFor root table
      L.Balanced m [] [] (driveStep (interpOf root table) m (.launch raceId) rest).1 [] [])
    (funded : L.Funded cap m [] []) :
    letI := evaluatorFor root table
    L.Funded (cap + commandAllowance charge m cmd) (driveStep (interpOf root table) m cmd rest).1 [] [] := by
  letI := evaluatorFor root table
  cases cmd with
  | evaluate id =>
    simp only [commandAllowance, Nat.add_zero, driveStep]
    split
    · exact funded
    · rename_i fiber found
      split
      · exact funded
      · apply (events.emit _ [.started id]
          (by intro event member; have same := List.mem_singleton.mp member; subst event; rfl)).funded L
        apply (metadata_transfer control m fiber {fiber with running := true, currentOpCount := 0}
          id found rfl rfl rfl (Nat.zero_le _)).2 ok |>.2.funded L funded
  | loop id y =>
    simp only [commandAllowance, driveStep]
    split
    · unfold PlaceLedger.Funded at funded ⊢
      dsimp only
      omega
    · rename_i fiber found
      have installed := PlaceLedger.charged_funded L
        (evaluation.iteration m fiber y ok permission
          (by simpa only [RunMachine.id_of_fiber? found] using found)) funded
      have settled := (settle_balance_at control quiet id rest _ (Native.iteration_ok root table m fiber y ok)).funded L installed
      simpa only [RunMachine.id_of_fiber? found] using settled
  | deliver id y =>
    simp only [commandAllowance, Nat.add_zero, driveStep]
    split
    · exact funded
    · rename_i fiber found
      have installed := (evaluation.native m fiber y ok permission
        (by simpa only [RunMachine.id_of_fiber? found] using found)).funded L funded
      exact (settle_balance_at control quiet id rest _ (Native.evaluateNative_ok root table m fiber y ok)).funded L installed
  | resume id token answer =>
    simp only [commandAllowance, Nat.add_zero, driveStep]
    split
    · exact funded
    · rename_i fiber found
      split
      · split
        · apply (events.emit _ [.resumedWith id token answer]
            (by intro event member; have same := List.mem_singleton.mp member; subst event; rfl)).funded L
          exact ((update_transfer control m fiber
            {fiber with
              parked := .notParked
              pending := fiber.pending.filter fun p => p.token ≠ token
              frame.current := answer} id found rfl
            (control.replace_changed fiber
              {fiber with
                parked := .notParked
                pending := fiber.pending.filter fun p => p.token ≠ token
                frame.current := answer} rfl (reply id token answer rfl) rfl (Nat.le_refl _))).2 ok).2.funded L funded
        · exact funded
      · exact funded
  | launch raceId =>
    simpa only [commandAllowance, Nat.add_zero] using (launch raceId rfl).funded L funded
  | enrollRace raceId child =>
    simp only [commandAllowance, Nat.add_zero, driveStep]
    split
    · rename_i race fiber raceFound childFound
      let changed := m.updateRace {race with state.live := race.state.live ++ [child]}
      have changedBalance := (raceStep m raceId race
        {race with state.live := race.state.live ++ [child]} raceFound rfl rfl raceHeld).2 ok
      have changedHeld := raceStable m changed (RunMachine.race_ids_update m _) raceHeld
      have before := changedBalance.2.funded L funded
      split
      · exact (observer_balance_on control events (interpOf root table) stores R raceStable raceStep
          child _ (changed, []) (.raceCallback raceId) changedHeld (updateRace_ok ok _)).funded L before
      · exact (modify_transfer control changed child
          (fun fiber => {fiber with observers := fiber.observers ++ [.raceCallback raceId]})
          (fun _ => rfl) (fun fiber => control.metadata fiber _ rfl rfl rfl (Nat.le_refl _))
          (updateRace_ok ok _)).2.funded L before
    · exact funded
  | registrationDone raceId y =>
    simp only [commandAllowance, Nat.add_zero, driveStep]
    split
    · exact funded
    · rename_i race raceFound
      split
      · exact ((raceStep m raceId race {race with registering := false} raceFound rfl rfl raceHeld).2 ok).2.funded L funded
      · rename_i fiber found
        have before := ((raceStep m raceId race {race with registering := false} raceFound rfl rfl raceHeld).2 ok).2
        have stored : m.fiber? fiber.id = some fiber := by
          simpa only [RunMachine.updateRace, RunMachine.fiber?, RunMachine.id_of_fiber? found] using found
        split
        · exact (settle_bookkeeping_at control quiet m fiber _ rest (updateRace_ok ok _) stored rfl rfl
            (control.replace_changed fiber _ rfl (admin.race raceId race.state.cleanupNeeded _) rfl (Nat.le_refl _)) before).funded L funded
        · apply (settle_bookkeeping_at control quiet m fiber _ rest (emit_ok (updateRace_ok ok _) _) stored rfl rfl ?_
            (before.trans L (events.emit _ [.parkedOn fiber.id race.token]
              (by intro event member; have same := List.mem_singleton.mp member; subst event; rfl)))).funded L funded
          exact Nat.le_trans
            (control.metadata {fiber with frame.stack := .asyncFinalizer _ :: fiber.frame.stack} _
              rfl rfl rfl (Nat.le_refl _)) (admin.cancel fiber raceId race.token)
  | interruptTarget target who extra =>
    simp only [commandAllowance, Nat.add_zero, driveStep]
    split
    · exact funded
    · rename_i fiber found
      apply (events.emit _ [.interruptRecorded who target]
        (by intro event member; have same := List.mem_singleton.mp member; subst event; rfl)).funded L
      exact ((update_transfer control m fiber _ target found
        (StackLedger.interruptRecord_key (interpOf root table) who extra fiber)
        (control.interruption (interruptCause (interpOf root table) who extra fiber.id) fiber)).2 ok).2.funded L funded
  | afterInterrupt host y kind =>
    simp only [commandAllowance, Nat.add_zero, driveStep]
    split
    · exact funded
    · rename_i fiber found
      exact (settle_bookkeeping_at control quiet m fiber _ rest ok
        (by simpa only [RunMachine.id_of_fiber? found] using found) rfl rfl
        (control.replace_changed fiber _ rfl (admin.await m kind) rfl (Nat.le_refl _)) (Nat.le_refl _)).funded L funded
  | raceCancel raceId host y remaining visited =>
    simp only [commandAllowance, Nat.add_zero, driveStep]
    repeat' split
    all_goals exact funded
  | trackChild parent child =>
    simp only [commandAllowance, Nat.add_zero, driveStep]
    split
    · exact funded
    · split
      · exact funded
      · have first := modify_transfer control m parent
          (fun fiber => {fiber with children := fiber.children ++ [child]})
          (fun _ => rfl) (fun fiber => control.metadata fiber _ rfl rfl rfl (Nat.le_refl _)) ok
        exact (modify_transfer control _ child
          (fun fiber => {fiber with observers := fiber.observers ++ [.untrackChild parent]})
          (fun _ => rfl) (fun fiber => control.metadata fiber _ rfl rfl rfl (Nat.le_refl _)) first.1).2.funded L
          (first.2.funded L funded)
  | observe id exit observer =>
    simp only [commandAllowance, Nat.add_zero]
    exact (observer_balance_on control events (interpOf root table) stores R raceStable raceStep
      id exit (m, []) observer raceHeld ok).funded L funded
  | exitDone id =>
    simp only [commandAllowance, Nat.add_zero, driveStep]
    split
    · exact funded
    · rename_i fiber found
      exact ((update_transfer control m fiber (fiber.cleared (interpOf root table)) id found rfl
        (control.clear_changed fiber _ rfl rfl rfl (Nat.le_refl _))).2 ok).2.funded L funded
  | closeParAwait host y fibers =>
    simp only [commandAllowance, Nat.add_zero, driveStep]
    split
    · exact funded
    · rename_i fiber found
      apply (settle_bookkeeping_at control quiet m fiber _ rest ok
        (by simpa only [RunMachine.id_of_fiber? found] using found) rfl rfl ?_ (Nat.le_refl _)).funded L funded
      exact Nat.le_trans (control.replace_changed
        {fiber with frame.stack := .iterator (interpOf root table).closeDoneName (interpOf root table).voidValue :: fiber.frame.stack}
        _ rfl (admin.park fibers) rfl (Nat.le_refl _)) (admin.iterator fiber)
  | link mode scope target who extra =>
    simp only [commandAllowance, Nat.add_zero]
    exact (link_balance_at control events (interpOf root table) stores mode scope target who extra m ok).funded L funded
  | finish id exit =>
    simp only [commandAllowance, Nat.add_zero, driveStep]
    split
    · exact funded
    · rename_i fiber found
      exact (exit_balance_at control events (interpOf root table) admin m fiber {fiber with running := false} exit ok
        (by simpa only [RunMachine.id_of_fiber? found] using found) rfl
        (control.metadata fiber _ rfl rfl rfl (Nat.le_refl _))).funded L funded
  | drainDue =>
    simp only [commandAllowance, Nat.add_zero]
    have state := PlaceLedger.state_balance L m ((interpOf root table).dueResumes m.state).2 [] [] (stores.due m.state)
    exact (state.trans L (drain_balance_at control events _ _ (state_ok ok _))).funded L funded
  | wake list phase =>
    simp only [commandAllowance, Nat.add_zero, driveStep]
    exact (PlaceLedger.state_balance L m _ [] [] (stores.wake list phase m.state)).funded L funded


/-- The earlier zero-race command API is the same producer at the trivial race permission. -/
theorem command_funded {cap : Nat} (root : NativeEff) (table : RowTable)
    (control : Control L Free) (quiet : NoQueue L) (events : Events L)
    (stores : StoreHooks L (interpOf root table)) (admin : Administration L Free (interpOf root table))
    (P : NativeMachine → Prop) (charge : NativeMachine → FiberId → Bool → Nat)
    (evaluation : Evaluation L P root table charge)
    (m : NativeMachine) (cmd : Native.NCmd) (rest : List Native.NCmd)
    (ok : Ok m) (permission : P m) (inputs : Inputs Free m cmd) (funded : L.Funded cap m [] []) :
    letI := evaluatorFor root table
    L.Funded (cap + commandAllowance charge m cmd) (driveStep (interpOf root table) m cmd rest).1 [] [] := by
  apply command_funded_at root table control quiet.pending events stores admin P charge evaluation
    m cmd rest ok permission inputs.reply (fun _ => True) (fun _ _ _ _ => trivial)
    (fun machine _ _ next _ _ _ _ => race_transfer quiet machine next) trivial _ funded
  intro raceId selected
  exact NoQueue.launch_balance root table control quiet events m raceId rest ok
    (fun race code more found programs => inputs.entrant raceId race code more selected found programs)



theorem commandAllowance_zero (m : NativeMachine) (command : Native.NCmd) :
    commandAllowance (fun _ _ _ => 0) m command = 0 := by
  fun_cases commandAllowance (fun _ _ _ => 0) m command <;> rfl

end Effect4.Program.PlaceFunding
