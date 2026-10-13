import Effect4.Laws.Program.SourceOpportunityMachine
import Effect4.Laws.Machine.Handshake
import Effect4.Laws.Machine.WriterWeights

/-!
Concept: scope-lifetime-finalization R11.
Consumer: actual native evaluator closure for application source-use bounds.
The debit excludes the acting stored row until the returned fiber is installed.
It measures the existing machine, frame and trace fields only.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace Effect4.Program.SourceScope.Opportunities
open Effect4 Effect4.Machine Effect4.Program

/-- The actual evaluator spends only its acting frame's source reservation.
Consumer: command settlement and the source-use history invariant. -/
def Debit (root : NativeEff) (q : List Nat) (m : NativeMachine) (fiber : SourceFiber)
    (next : SourceIteration) : Prop :=
  recorded q next.machine + outside root q fiber.id next.machine + frame root q next.fiber.frame ≤
    recorded q m + outside root q fiber.id m + frame root q fiber.frame

/-- Diagnostic events leave the stored source reservation unchanged.
Consumer: native observer and interruption actions. -/
theorem outside_emit (root : NativeEff) (q : List Nat) (owner : FiberId)
    (m : NativeMachine) (events) : outside root q owner (m.emit events) = outside root q owner m := rfl

/-- A shared keyed replacement decreases the off-owner source reservation.
Consumer: native observer metadata and interruption actions. -/
theorem outside_update_le (root : NativeEff) (q : List Nat) (m : NativeMachine)
    (owner : FiberId) (old next : SourceFiber) (same : next.id = old.id)
    (unique : (m.fibers.map (fun fiber => fiber.id)).Nodup) (member : old ∈ m.fibers)
    (carried : frame root q next.frame ≤ frame root q old.frame) :
    outside root q owner (m.update next) ≤ outside root q owner m :=
  FiberSum.outside_update_le (fun fiber => frame root q fiber.frame) m owner old next unique
    (fiber_lookup_of_mem_nodup m unique old member) same carried

/-- A metadata-only fiber edit retains the off-owner source reservation.
Consumer: countdown observers, child tracking and scope links. -/
theorem outside_modify_le (root : NativeEff) (q : List Nat) (m : NativeMachine)
    (owner target : FiberId) (edit : SourceFiber → SourceFiber)
    (unique : (m.fibers.map (fun fiber => fiber.id)).Nodup)
    (same : ∀ fiber, (edit fiber).id = fiber.id)
    (carried : ∀ fiber, frame root q (edit fiber).frame ≤ frame root q fiber.frame) :
    outside root q owner (m.modify target edit) ≤ outside root q owner m := by
  unfold RunMachine.modify
  split
  · exact Nat.le_refl _
  · rename_i fiber found
    exact outside_update_le root q m owner fiber (edit fiber) (same fiber) unique
      (List.mem_of_find?_eq_some found) (carried fiber)

/-- Applying an interruption discards active opportunities and preserves saved frames.
Consumer: actual interrupt and scope-link actions. -/
theorem interrupt_record_le (root : NativeEff) (q : List Nat) (table : RowTable)
    (completed : List (FiberId × ExitV)) (who : Option FiberId) (extra : ReasonAnnotations Ann)
    (fiber : SourceFiber) :
    frame root q (interruptRecord (interpAt root completed table) who extra fiber).1.frame ≤
      frame root q fiber.frame := by
  exact Machine.WriterWeights.interrupt_weight_le (weightModel root q) _ fiber

/-- Addressed messages cannot increase the source reservations outside a named owner.
Consumer: eager countdown and scope-link adapters; settlement uses the shared total bound. -/
theorem outside_edits_le (root : NativeEff) (q : List Nat) (m : NativeMachine)
    (owner : FiberId) (edits : List (FiberEdit Err Defect FiberId Ann))
    (unique : (m.fibers.map (fun fiber => fiber.id)).Nodup) :
    outside root q owner (applyFiberEdits edits m).1 ≤ outside root q owner m := by
  apply (FiberSum.fiberEdits_le (ControlWeights.omitted (fun fiber : SourceFiber => fiber.id)
    (fun fiber : SourceFiber => frame root q fiber.frame) owner) (fun _ _ => rfl) ?_ edits m unique).2
  intro cause fiber
  have same := (interruptWithCause_maskLater cause fiber).1
  dsimp only [ControlWeights.omitted]
  simp only [same]
  split
  · exact Nat.le_refl _
  · exact Machine.WriterWeights.interrupt_weight_le (weightModel root q) cause fiber

/-- The countdown plan adds only a zero-weight cleanup and diagnostic event.
Consumer: native countdown evaluation before addressed observers are installed. -/
theorem countdown_plan_debit (root : NativeEff) (q : List Nat) (table : RowTable)
    (m : NativeMachine) (fiber : SourceFiber) (yielding : Bool) (targets : List FiberId)
    (resume : Resume EffName) (failFast : Bool) (shape : ResumeAt root resume) :
    let out := countdownParkEdits (interpAt root m.completedExits table) m fiber targets resume failFast
    Debit root q m fiber ⟨out.1, out.2.1, yielding, .continue_, [], out.2.2.2⟩ := by
  have zero (exits : List ExitV) : current root q
      (countdownPark.resumePrim (interpAt root m.completedExits table) resume exits) = 0 := by
    cases resume
    case continueWith => exact shape.elim
    all_goals rfl
  unfold countdownParkEdits
  dsimp only
  split
  · unfold Debit frame
    simp only [zero, Nat.zero_add]
    change recorded q m + outside root q fiber.id m + _ ≤ recorded q m + outside root q fiber.id m + _
    omega
  · have cancelZero : name q ((interpAt root m.completedExits table).cancelName
        (interpAt root m.completedExits table).parkCancelName fiber.id m.nextToken) = 0 := rfl
    unfold Debit
    simp only [recorded_emit, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      runEvent, Nat.add_zero, outside_emit, frame, RunFiber.park, saved, cancelZero, Nat.zero_add]
    exact Nat.le_refl _

/-- Native countdown callbacks retain the existing saved source budget.
Consumer: awaitAll and awaitNewChildren native evaluator clauses. -/
theorem countdown_debit (root : NativeEff) (q : List Nat) (table : RowTable)
    (m : NativeMachine) (fiber : SourceFiber) (yielding : Bool) (targets : List FiberId)
    (resume : Resume EffName) (failFast : Bool)
    (unique : (m.fibers.map (fun fiber => fiber.id)).Nodup) (shape : ResumeAt root resume) :
    let out := countdownPark (interpAt root m.completedExits table) m fiber targets resume failFast
    Debit root q m fiber ⟨out.1, out.2.1, yielding, .continue_, [], []⟩ := by
  let out := countdownParkEdits (interpAt root m.completedExits table) m fiber targets resume failFast
  have debit := countdown_plan_debit root q table m fiber yielding targets resume failFast shape
  have sameFibers : out.1.fibers = m.fibers := by
    rw [Edits.countdown_word]
    exact Edits.run_keeps _ _ (fun edit member => edit.keeps_fibers
      (Edits.countdown_misses m fiber targets edit member)) m
  have off := outside_edits_le root q out.1 fiber.id out.2.2.2 (by rw [sameFibers]; exact unique)
  have trace := congrArg RunMachine.trace (RunMachine.applyFiberEdits_shape out.2.2.2 out.1).1
  unfold countdownPark Debit
  change recorded q (applyFiberEdits out.2.2.2 out.1).1 +
    outside root q fiber.id (applyFiberEdits out.2.2.2 out.1).1 + frame root q out.2.1.frame ≤ _
  have count : recorded q (applyFiberEdits out.2.2.2 out.1).1 = recorded q out.1 := by
    unfold recorded
    rw [trace]
  rw [count]
  exact Nat.le_trans (Nat.add_le_add_right (Nat.add_le_add_left off _) _) debit

/-- Closing a source-owned scope installs only code with no selected source opportunity.
Consumer: the close arm of `native_action_debit`. -/
theorem close_scope_zero (root : NativeEff) (q : List Nat) (table : RowTable)
    (completed : List (FiberId × ExitV)) (scope : Nat) (exit : ExitV) (flag : Bool)
    (closer : FiberId) (clear : ClearFinalizers root q) (state next : Stores)
    (owned : ScopesAt root state.scopes) (program : NCode)
    (closed : (interpAt root completed table).closeScope scope exit flag closer state =
      some (next, some program)) :
    current root q program = 0 := by
  change (storesCloseScope scope exit flag state).map (fun result => (result.1, result.2.map embed)) =
    some (next, some program) at closed
  cases step : storesCloseScope scope exit flag state with
  | none => rw [step] at closed; cases closed
  | some result =>
    obtain ⟨after, code⟩ := result
    rw [step] at closed
    cases code with
    | none => cases closed
    | some code =>
      cases closed
      unfold storesCloseScope at step
      cases snapshot : scopeCloseSnapshot scope exit state with
      | none => rw [snapshot] at step; cases step
      | some result =>
        obtain ⟨closedState, strategy, order⟩ := result
        have slots := close_snapshot_at root scope exit state closedState strategy order owned snapshot
        simp only [snapshot, Option.pure_def] at step
        cases order with
        | nil => cases step
        | cons first rest =>
          cases rest with
          | nil =>
            cases step
            have finZero := fin_program_zero root q clear first exit (slots.2.1 first (.head _))
            simpa only [embed, current, cata_prim, name, push, Nat.add_zero] using finZero
          | cons second tail =>
            cases step
            rfl

/-- Removing observer rows leaves source reservations unchanged.
Consumer: cancellation cleanup action accounting. -/
theorem drop_outside (root : NativeEff) (q : List Nat) (m : NativeMachine) (owner : FiberId) (token : Nat) :
    outside root q owner {m with fibers := m.fibers.map fun g =>
      {g with observers := g.observers.filter fun
        | .resumeAwait _ t _ => t ≠ token
        | .countdown _ t => t ≠ token
        | _ => true}} = outside root q owner m := by
  unfold outside
  rw [List.map_map]
  rfl

end Effect4.Program.SourceScope.Opportunities
